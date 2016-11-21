include "../../commons/MapsHelpers.dfy"

/*
 * I didn't managed to prove a correlation between the cardinality of the relations in a dafny map and some operations of the stack, 
 * because of this I am unable to provide an access to a size/length variable
 */

//This data structure is named TreeMapInt, because the key will always be integers but the values are generic and can hold any type
//There is no use of autocontracts here because there are some recursive methods which doesn't necessarily maintain the stack (There is a way to avoid that by implementing the methods directly on the node and not on the main data structure, but it was not implemented here)
class TreeMapInt<T> {
	//Those variables are on the implementation side, they will hold the main elements of the TreeMap
	var root: Node<T>;
	
	//Those variables are on the specification side, they will hold the elements which help to prove the validity of the TreeMap
	ghost var KeyValueMap: map<int, T>; //This a simple map, it is a built-in type in Dafny, and it will represent all the key value pairs in the TreeMap
	ghost var Repr: set<object>; // This is the dynamic frame


	predicate Valid()
		reads this, this.Repr;
	{
		(this in this.Repr) 
		&&
		(null !in this.Repr)
		&&
		//If the root is null, then the map is supposed to be empty
		(this.root == null ==> this.KeyValueMap == map[])
		&&
		//If it is not, then :
		(this.root != null ==>
			(this.root in this.Repr)
			&& 
			//The dynamic frame of the root node must be a subset of the tree's dynamic frame
			(this.root.Repr <= this.Repr)
			&&
			(this !in this.root.Repr) 
			&&
			//The root node must be valid (and therefore the whole tree, this method will check the validity of the leaf nodes)
			(this.root.Valid())
			&&
			//Finally, the map of the TreeMap must be equal to the map of the root node
			(this.KeyValueMap == this.root.KeyValueMap)
		)
	}

	constructor()
		modifies this;
		//The node must be valid and the dynamic frame (minus the current object) must be fresh (this is required by Dafny but doesn't makes a lot of sense here)
		ensures Valid() && fresh(this.Repr - {this});
		ensures this.KeyValueMap == map[];
	{
		this.root := null;
		this.Repr := {this};
		this.KeyValueMap := map[];
	}
	
	//Returns true if the node is empty, false otherwise
	method isEmpty() returns (empty: bool)
		requires Valid();
		ensures empty <==> |KeyValueMap| == 0;
	{
		empty := this.root == null;
	}

	//Returns true if the map contains the key, false otherwise
	method contains(keyToFind: int) returns (contain: bool)
		requires Valid();
		ensures contain <==> keyToFind in this.KeyValueMap;
	{
		if (this.root == null) {
			contain := false;
		} else {
			//makes use of a recursive call for this
			contain := private_contains(this.root, keyToFind);
		}
	}
	
	//Recursive call for the contains method, doesn't use the Valid() predicate of the TreeMap because it only interracts with the Nodes
	//This could be directly implemented as a method of the Node
	method private_contains(node: Node<T>, keyToFind: int) returns (present: bool)
		requires node != null && node.Valid();
		ensures present <==> keyToFind in node.KeyValueMap;
		//This is the termination measure for this recursive method, the dynamic frame of the node will be smaller as we go deeper in the tree
		//so dafny knows that the method wont be called anymore as soon as node.Repr is equal to an empty set
		decreases node.Repr;
	{
		present := false;

		if (keyToFind == node.key) { //The key was found
			present := true;
		} else if (node.left != null && keyToFind < node.key) { //Exploration of the left part
			present := private_contains(node.left, keyToFind);
		} else if (node.right != null && node.key < keyToFind) { //Exploration of the right part
			present := private_contains(node.right, keyToFind);
		} else { //No more nodes, not found
			present := false;
		}
	}

	//Returns the object mapped by the given key
	method get(keyToFind: int) returns (value: T)
		//This method only works if the key is actually in the tree (since we can't return null for a generic type in Dafny)
		requires this.root != null && keyToFind in this.KeyValueMap;
		requires Valid();
		ensures value == this.KeyValueMap[keyToFind];
	{
		value := private_get(this.root, keyToFind);
	}

	//Recursive call for the get method (see the private_contains methods for details)
	method private_get(node: Node<T>, keyToFind: int) returns (value: T)
		requires node != null && node.Valid();
		//Again, the key must be in the tree
		requires keyToFind in node.KeyValueMap;
		ensures value == node.KeyValueMap[keyToFind];
		decreases node.Repr;
	{
		if (keyToFind == node.key) {
			value := node.value;
		} else if (node.left != null && keyToFind < node.key) {
			value := private_get(node.left, keyToFind);
		} else if (node.right != null && node.key < keyToFind) {
			value := private_get(node.right, keyToFind);
		}
	}
	
	//Inserts the given object mapped by the given key in the TreeMap
	method put(key: int, value: T)
		requires Valid();
		modifies this.Repr;
		ensures Valid() && fresh(this.Repr - old(this.Repr));
		ensures this.KeyValueMap == old(this.KeyValueMap)[key := value];
	{ 
		var updatedRoot := private_put(key, value, root);
		this.root := updatedRoot;
		this.KeyValueMap := root.KeyValueMap;
		this.Repr := root.Repr + {this};
	}

	//Recursive call for the put method (see the private_contains methods for details)
	//The timeLimit element increases the time allocated to the automated verifier (10 seconds by default, 20 seconds here), this method can be complicated to prove
	method {:timeLimit 20} private_put(key: int, value: T, node: Node<T>) returns (updatedNode: Node<T>)
		requires node == null || node.Valid();
		//The modifies clause here will change depending on if the node is null or not, we can use a condition for that
		modifies if node != null then node.Repr else {};
		ensures updatedNode != null && updatedNode.Valid();
		//if the given node was null, then the returned node must only have the given key and value in its map
		ensures node == null ==> fresh(updatedNode.Repr) && updatedNode.KeyValueMap == map[key := value];
		//If not, then it must have its old map with the new mapping
		ensures node != null ==> updatedNode == node && node.KeyValueMap == old(node.KeyValueMap)[key := value];
		ensures node != null ==> fresh(node.Repr - old(node.Repr));
		//As for the modifies clause, we need to specify all the cases
		decreases if node == null then {} else node.Repr;
	{
		if (node == null) { //No existing node with the given key was found, we append a new one
			updatedNode := new Node(key, value);
		} else if (key == node.key) { //An existing node with the given key was found, we update the value
			node.value := value;
			updatedNode := node;
			node.KeyValueMap := node.KeyValueMap[key := value];
		} else { //No existing nor end of the tree was found, we keep going down into the tree
			if (key < node.key) {
				var updatedLeftNode := private_put(key, value, node.left);
				node.left := updatedLeftNode;
				node.Repr := node.Repr + node.left.Repr;
			} else {
				var updatedRightNode := private_put(key, value, node.right);
				node.right := updatedRightNode;
				node.Repr := node.Repr + node.right.Repr;
			}

			node.KeyValueMap := node.KeyValueMap[key := value];
			updatedNode := node;
		}
	}
	
	//Removes the given key from the tree
	method remove(keyToRemove: int)
		requires Valid() && keyToRemove in this.KeyValueMap;
		modifies Repr;
		ensures Valid() && fresh(Repr - old(Repr));
		//The MapHelpers are a set of functions helping with some particular map manipulations (see file for more details)
		ensures this.KeyValueMap == MapsHelpers.excludeFromMap(old(this.KeyValueMap), keyToRemove);
		decreases Repr;
	{
		this.root := private_remove(keyToRemove, this.root);

		if (this.root == null) { 
			this.Repr := {this};
			this.KeyValueMap := map[];
		} else {
			this.KeyValueMap := root.KeyValueMap;
			this.Repr := root.Repr + {this};
		}
	}

	//Recursive call for the remove method (see the private_contains methods for details)
	method private_remove(keyToRemove: int, node: Node<T>) returns (updatedNode: Node<T>)
		requires node != null && node.Valid() && keyToRemove in node.KeyValueMap;
		modifies node.Repr;
		ensures fresh(node.Repr - old(node.Repr));
		ensures updatedNode != null ==> updatedNode.Valid();
		//If the updated node is null, then its old map only had a single mapping (the given key to the given value)
		ensures updatedNode == null ==> keyToRemove in old(node.KeyValueMap) && old(node.KeyValueMap) == map[keyToRemove := old(node.KeyValueMap)[keyToRemove]];
		//If not, then its updated map is the exact old one without the current mapping (given key to given value)
		ensures updatedNode != null ==> updatedNode.Repr <= node.Repr && updatedNode.KeyValueMap == MapsHelpers.excludeFromMap(old(node.KeyValueMap), keyToRemove);
		decreases node.Repr;
	{
		updatedNode := node;
		if (node.left != null && keyToRemove < node.key) { // We keep exploring the left part of the tree
			var updatedLeftNode := private_remove(keyToRemove, node.left);
			node.left := updatedLeftNode;
			node.KeyValueMap := MapsHelpers.excludeFromMap(node.KeyValueMap, keyToRemove);

			if (node.left != null) { 
				node.Repr := node.Repr + node.left.Repr; 
			}
		} else if (node.right != null && node.key < keyToRemove) { // We keep exploring the right part of the tree
			var updatedRightNode := private_remove(keyToRemove, node.right);
			node.right := updatedRightNode;
			node.KeyValueMap := MapsHelpers.excludeFromMap(node.KeyValueMap, keyToRemove);

			if (node.right != null) { 
				node.Repr := node.Repr + node.right.Repr; 
			}
		} else if (keyToRemove == node.key) { // We found the node to remove
			if (node.left == null && node.right == null) {
				//The node to remove was a leaf of the tree, just replace it with null
				updatedNode := null;
			} else if (node.left == null) {
				//The node to remove doesn't have a left node, just replace it with the right one
				updatedNode := node.right;
			} else if (node.right == null) {
				//The node to remove doesn't have a right node, just replace it with the left one
				updatedNode := node.left;
			} else {
				//The node had had two leafs, we need to rotate it (we take the smallest node in the tree and we replace it with the node to remove. 
				//Then we take the remains of the tree (minus the min node) and we set it as the right tree of the current tree since it is larger than the min one.
				//This way the tree invariant is respected
				var min, minValue, updatedRightNode := private_removeMin(node.right);

				node.key := min;  
				node.value := minValue;
				node.right := updatedRightNode;

				node.KeyValueMap := MapsHelpers.excludeFromMap(node.KeyValueMap, keyToRemove);
				
				if (node.right != null) { 
					node.Repr := node.Repr + node.right.Repr; 
				}
			}
		}
	}

	//Recursive call used to remove and return the smallest key in a tree (generally a subtree)
	method private_removeMin(node: Node<T>) returns (min: int, minValue: T, updatedNode: Node<T>)
		requires node != null && node.Valid();
		modifies node.Repr;
		ensures fresh(node.Repr - old(node.Repr));
		ensures updatedNode != null ==> updatedNode.Valid();
		//If the returned node is null, then the old node's map only had a single mapping, the one we want to remove
		ensures updatedNode == null ==> min in old(node.KeyValueMap) && old(node.KeyValueMap) == map[min := minValue];
		//Otherwise, then the returned node's map must be equal to the old map minus the current mapping (the one we want to remove)
		ensures updatedNode != null ==> updatedNode.Repr <= node.Repr && updatedNode.KeyValueMap == MapsHelpers.excludeFromMap(old(node.KeyValueMap), min);
		//At any times, the smallest key must be in the old node and all the keys in the map must be superior or equal to the min key
		//This is complex, but it is simply a check that we really removed the minimal value and that it was the same one in every node
		ensures min in old(node.KeyValueMap) && (forall x :: x in old(node.KeyValueMap) ==> min <= x) && old(node.KeyValueMap)[min] == minValue;
		decreases node.Repr;
	{
		if (node.left == null) {
			min := node.key;
			updatedNode := node.right;
			minValue := node.value;
		} else {
			var newMinNode;
			min, minValue, newMinNode := private_removeMin(node.left); 
			node.left := newMinNode;
			
			updatedNode := node;
			
			node.KeyValueMap := MapsHelpers.excludeFromMap(node.KeyValueMap, min);
			
			if (node.left != null) { 
				node.Repr := node.Repr + node.left.Repr;
			}
		}
	}

}

class Node<T> {
	//Represents all the mapping in this node and the child ones
	ghost var KeyValueMap: map<int, T>;
	ghost var Repr: set<object>;

	var key: int;
	var value: T;
	var left: Node<T>;
	var right: Node<T>;

	predicate Valid()
		reads this, Repr;
	{
		(this in this.Repr) 
		&&
		(null !in this.Repr) 
		&&
		//If the left node is not null, it must be valid, have a correct dynamic frame, and all its keys must be lower to the current node's key
		(this.left != null ==>
			(this.left in this.Repr) 
			&&
			(this.left.Repr <= this.Repr) 
			&& 
			(this !in this.left.Repr) 
			&&
			(this.left.Valid()) 
			&&
			(forall y :: y in this.left.KeyValueMap ==> y < this.key)
		) 
		&&
		//If the right node is not null, it must be valid, have a correct dynamic frame, and all its keys must be superior to the current node's key
		(this.right != null ==>
			(this.right in this.Repr) 
			&&
			(this.right.Repr <= this.Repr) 
			&& 
			(this !in this.right.Repr) 
			&&
			(this.right.Valid()) 
			&&
			(forall y :: y in this.right.KeyValueMap ==> this.key < y)
		) 
		&&
		//If both nodes are null, then the map only contains a single mapping
		(this.left == null && this.right == null ==> KeyValueMap == map[this.key := this.value]) 
		&&
		//If only one node is not null, then the map contains all the non null node mappings plus the current one
		(this.left != null && this.right == null ==> KeyValueMap == this.left.KeyValueMap[this.key := this.value]) 
		&&
		(this.left == null && this.right != null ==> KeyValueMap == this.right.KeyValueMap[this.key := this.value]) 
		&&
		//If both nodes are not null, then no node must be present in both sides and the map must be equal to the union of both node's maps plus the current mapping
		(this.left != null && this.right != null ==>
			// left.Repr and right.Repr must have no objects in common
			(this.left.Repr !! this.right.Repr)
			&&
			(this.right.KeyValueMap !! this.left.KeyValueMap)
			&&
			(this.KeyValueMap == MapsHelpers.unionMaps(this.left.KeyValueMap, this.right.KeyValueMap)[this.key := this.value])
		)
	}

	constructor(key: int, value: T)
		modifies this;
		ensures Valid() && fresh(Repr - {this});
		ensures KeyValueMap == map[key := value];
	{
		this.key := key;
		this.value := value;
		this.left := null;
		this.right := null;
		this.KeyValueMap := map[key := value];
		this.Repr := {this};
	}
}

class Main {

		

  method Client0()
  {
    var s := new TreeMapInt<string>();
	var empty := s.isEmpty();
	var present := s.contains(12);
	assert !present;
	assert empty;
    s.put(12, "Hello");
	present := s.contains(12);
	assert present;
    s.put(24, "World");
	empty := s.isEmpty();
	assert !empty;
	var test := s.get(12);
	assert test == "Hello";
	test := s.get(24);
	assert test == "World";
	s.remove(12);
	present := s.contains(12);
	assert !present;
    s.put(12, "Hello");
	present := s.contains(12);
  }
}