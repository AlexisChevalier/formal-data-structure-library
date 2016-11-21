include "../../commons/MapsHelpers.dfy"

/*
 * This is a specific data structure which was designed to be used in the HashMap as extented chaining system, which is why 
 * the linked list provides a key-value system
 */

class KeyValueLinkedList<T> {
	//Top node of the list
	var top: Node<T>;
	//Size of the list
	var listSize: int;

	//Dynamic frame
	ghost var Repr: set<Node<T>>;
	//Current sequence of nodes in the list
	ghost var ListNodes: seq<Node<T>>;
	//Current key value map
	ghost var KeyValueMap: map<int, T>;

	//Initialize the list
	constructor()
		modifies this;
		//The list will be valid
		ensures Valid()
		//The list will be empty
		ensures Empty();
		//The dynamic frame will be empty
		ensures this.Repr == {};
		//The list size will be 0
		ensures this.listSize == 0;
	{
		this.top := null;
		this.listSize := 0;
		this.ListNodes := [];
		this.Repr := {};
		this.KeyValueMap := map[];
	}

	//Specification only: verifies the validity of the list
	predicate Valid()
		//The predicate reads the current object and all the objects in the dynamic frame of the stack
		reads this, this.Repr;
	{
		//When the top pointer is null, then the size must be zero and the ghost representation must be empty
		(top == null ==>	this.listSize == 0 
							&& 
							this.ListNodes == []
							&&
							this.Repr == {}
							&&
							this.KeyValueMap == map[]
		)
		&&
		//When the top pointer is not null, then :
		(top != null ==>
							//The top pointer and its dynamic frame must be accessible in the dynamic frame for the next statements
							(this.top in Repr)
							&&
							(this.top.Repr == this.Repr)
							&&
							(this.top.KeyValueMap == this.KeyValueMap)
							&& 
							//The nodes listed in the list must be the same than the one in the current top node's linked list
							(this.top.CurrentNodes == this.ListNodes)
							&&
							//The top node must be valid (This is recursive and will check all the linked list)
							(this.top.Valid())
		)
		&&
		//The listSize variable must be at all times the same than the cardinality of the current nodes set
		(this.listSize == |this.ListNodes| == |this.KeyValueMap|)
	}

	//Specification only: returns true if the list is supposed to be empty
	predicate Empty()
		//The predicate reads the current object
		reads this;
	{
		this.ListNodes == [] && this.KeyValueMap == map[]
	}

	//The method inserts the key and the value in the list
	method put(key: int, value: T)
		requires Valid();
		modifies this, this.Repr;
		ensures Valid() && fresh(this.Repr - old(this.Repr));
		ensures key in this.KeyValueMap && this.KeyValueMap[key] == value;
		//If the key wasn't in the map, then it has been added, so the size has increased by one
		ensures key !in old(this.KeyValueMap) ==> this.listSize == old(this.listSize) + 1;
		//If it was in the map, then the value has been updated, so no change of size
		ensures key in old(this.KeyValueMap) ==> this.listSize == old(this.listSize);
		//The map is the same than before, except that it includes the new mapping
		ensures this.KeyValueMap == old(this.KeyValueMap)[key := value];
	{
		this.top := private_put(this.top, key, value);

		this.Repr := this.top.Repr;
		this.KeyValueMap := this.top.KeyValueMap;
		this.ListNodes := this.top.CurrentNodes;
		this.listSize := this.top.size;
	}

	//Private recursive method for the put operation
	//See the TreeMap for more details about the validation logic, it follows the same principles
	method private_put(node: Node<T>, key: int, value: T) returns (updatedNode: Node<T>)
		requires node == null || node.Valid();
		modifies if node != null then node.Repr else {};
		ensures updatedNode != null && updatedNode.Valid();
		ensures node == null ==> fresh(updatedNode.Repr) && updatedNode.KeyValueMap == map[key := value];
		ensures node != null ==> updatedNode == node && node.KeyValueMap == old(node.KeyValueMap)[key := value];
		ensures node != null ==> fresh(node.Repr - old(node.Repr));
		ensures updatedNode.KeyValueMap[key] == value;
		decreases if node == null then {} else node.Repr;
	{
		if (node == null) {
			updatedNode := new Node<T>(key, value);
		} else if (node.key == key) {
			node.value := value;
			updatedNode := node;
			updatedNode.KeyValueMap := node.KeyValueMap[key := value];
		} else {
			updatedNode := private_put(node.next, key, value);
			node.next := updatedNode;
			node.KeyValueMap := node.next.KeyValueMap[node.key := node.value];
			node.CurrentNodes := [node] + node.next.CurrentNodes;
			node.Repr := node.next.Repr + {node};
			node.size := 1 + node.next.size;
			updatedNode := node;
		}
	}

	//Returns the element matching the given key
	method get(key: int) returns (value: T)
		requires Valid() && !Empty();
		//The method only works if the element is in the list
		requires |this.KeyValueMap| > 0 && key in this.KeyValueMap;
		ensures value == this.KeyValueMap[key];
	{
		value := private_get(this.top, key);
	}

	
	//Private recursive method for the get operation
	//See the TreeMap for more details about the validation logic, it follows the same principles
	method private_get(node: Node<T>, key: int) returns (value: T)
		requires Valid();
		requires node != null && node.Valid();
		requires node.key != key ==> key in node.KeyValueMap;
		requires node.key != key ==> node.next != null;
		ensures value == node.KeyValueMap[key];
		decreases node.Repr;
	{
		if (node.key == key) {
			value := node.value;
		} else {
			value := private_get(node.next, key);
		}
	}
	
	//Returns true if the given key is in the list, false otherwise
	method contains(key: int) returns (contain: bool)
		requires Valid();
		ensures contain <==> key in this.KeyValueMap;
	{
		contain := private_contains(this.top, key);	
	}
	
	//Private recursive method for the contains operation
	//See the TreeMap for more details about the validation logic, it follows the same principles
	method private_contains(node: Node<T>, key: int) returns (contain: bool)
		requires Valid();
		requires node == null || node.Valid();
		ensures contain <==> (node != null && key in node.KeyValueMap);
		decreases if node != null then node.Repr else {};
	{
		if (node == null) {
			contain := false;
		} else if (node.key == key) {
			contain := true;
		} else if (node.next != null) {
			contain := private_contains(node.next, key);
		} else {
			contain := false;
		}
	}
		
		
	//Removes the element mapped by the given key from the list
	method remove(key: int)
		//The key must be in the list
		requires Valid() && key in this.KeyValueMap;
		modifies this, this.Repr;
		ensures Valid() && fresh(this.Repr - old(this.Repr));
		ensures this.KeyValueMap == MapsHelpers.excludeFromMap(old(this.KeyValueMap), key);
		ensures this.listSize == old(this.listSize) - 1;
	{
		this.top := private_remove(this.top, key);

		if (this.top == null) {
			this.Repr := {};
			this.KeyValueMap := map[];
			this.ListNodes := [];
			this.listSize := 0;	
		} else {
			this.Repr := this.top.Repr;
			this.KeyValueMap := this.top.KeyValueMap;
			this.ListNodes := this.top.CurrentNodes;
			this.listSize := this.top.size;	
		}
	}
	
	//Private recursive method for the remove operation
	//See the TreeMap for more details about the validation logic, it follows the same principles
	method private_remove(node: Node<T>, key: int) returns (updatedNode: Node<T>)
		requires node != null && node.Valid();
		requires key in node.KeyValueMap;
		modifies node.Repr;
		ensures fresh(node.Repr - old(node.Repr));
		ensures updatedNode != null ==> updatedNode.Valid();
		ensures updatedNode == null ==> key in old(node.KeyValueMap) && old(node.KeyValueMap) == map[key := old(node.KeyValueMap)[key]];
		ensures updatedNode != null ==> updatedNode.Repr <= node.Repr && updatedNode.KeyValueMap == MapsHelpers.excludeFromMap(old(node.KeyValueMap), key);
		//If the node is the node to remove, and it has a non null next node, then we must ensure that all the list structure is maintained:
		ensures node.key == key && node.next != null ==> (
			(updatedNode != null)
			&& 
			(updatedNode == node.next)
			&& 
			(|node.CurrentNodes| >= 2)
			&& 
			(updatedNode.CurrentNodes == node.CurrentNodes[1..|node.CurrentNodes|])
			&& 
			(updatedNode.size == node.size - 1)
			&& 
			(key !in updatedNode.KeyValueMap)
		);
		ensures node.key == key && node.next == null ==> updatedNode == null;
		ensures updatedNode != null ==> updatedNode.size == old(node.size) - 1;
		decreases node.Repr;
	{
		if (node.key == key) {
			updatedNode := node.next;
		} else {
			updatedNode := private_remove(node.next, key);
			node.next := updatedNode;

			if (node.next == null) {
				node.KeyValueMap := map[node.key := node.value];
				node.CurrentNodes := [node];
				node.Repr := {node};
				node.size := 1;
			} else {
				node.KeyValueMap := node.next.KeyValueMap[node.key := node.value];
				node.Repr := node.next.Repr + {node};
				node.CurrentNodes := [node] + node.next.CurrentNodes;
				node.size := 1 + node.next.size;
			}

			updatedNode := node;
		}
	}

	//Returns the size of the list
	function method size() : int
		requires Valid();
		reads this, this.Repr;
		ensures size() == this.listSize == |this.ListNodes| == |this.KeyValueMap|;
	{
		this.listSize
	}

	//Returns true if the list is empty, false otherwise
	method isEmpty() returns (empty: bool)
		requires Valid();
		ensures empty <==> Empty();
	{
		empty := (this.top == null);
	}
}


//Node class for the linked list
class Node<T> {
	var key: int;
	var value: T;
	var next: Node<T>;
	var size: int;

	//Dynamic frame: allow read/modify access to all the elements in the linked list
	ghost var Repr: set<object>;
	//Current sequence of nodes in the linked list
	ghost var CurrentNodes: seq<Node<T>>;
	//Current key value map
	ghost var KeyValueMap: map<int, T>;

	//Specification only: verifies the validity of the node
	predicate Valid()
		//The predicate reads the current object and all the objects in the dynamic frame of the node
		reads this, Repr;
	{
		//The current object must be in the dynamic frame
		(this in this.Repr)
		&&
		(null !in this.Repr)
		&&
		(this.size == |this.CurrentNodes| == |this.KeyValueMap|)
		&&
		(null !in this.CurrentNodes)
		&&
		(forall node :: node in this.CurrentNodes ==> node in this.Repr && node.Repr <= this.Repr && node.key in this.KeyValueMap && this.KeyValueMap[node.key] == node.value)
		&&
		//There can't be two differet nodes with the same key in the list
		(forall n1, n2 :: n1 in this.CurrentNodes && n2 in this.CurrentNodes && n1 != n2 ==> n1.key != n2.key)
		&&
		//If the next node is null, then : There is no previous nodes
		(this.next == null ==>	(this.CurrentNodes == [this])
								&& 
								//And the current frame only contains this node
								(this.Repr == {this})
								&&
								(this.KeyValueMap == map[this.key := this.value])
								&&
								(this.size == 1)
		)
		&& 
		//If the next node is not null, then :
		(this.next != null ==> 
								//The next object should be in the dynamic frame
								(this.next in this.Repr)
								&&
								(this.Repr == {this} + this.next.Repr)
								&& //The current object should not already be in the previous nodes (in order to avoid infinite linked lists)
								(this !in this.next.Repr)
								&&
								(this.CurrentNodes == [this] + this.next.CurrentNodes)
								&&
								(this.KeyValueMap == this.next.KeyValueMap[this.key := this.value])
								&&
								(this.key !in this.next.KeyValueMap)
								&&
								(this.size == 1 + this.next.size)
								&&
								//The next node should be valid (Recursive)
								(this.next.Valid())
		)
	}
			

	//Initialize the node
	constructor(key: int, value: T)
		//The method will only modify the current object
		modifies this;
		//The correct values should have been assigned
		ensures this.value == value && this.key == key;
		ensures this.size == 1;
		//The current node should be valid
		ensures Valid();
	{
		this.value := value;
		this.key := key;
		this.next := null;
		//Populating the initial specification state
		this.Repr := {this};
		this.CurrentNodes := [this];
		this.KeyValueMap := map[this.key := this.value];
		this.size := 1;
	}

}

class MainTest {
	
	method Main() 
	{
		var list := new KeyValueLinkedList<string>();
		
		var size := list.size();

		assert size == 0;
		
		list.put(20, "Hello");
		var val := list.get(20);
		assert val == "Hello";

		list.put(1, "World");
		val := list.get(20);
		assert val == "Hello";
		val := list.get(1);
		assert val == "World";

		size := list.size();

		assert size == 2;
		list.put(2, "World");
		size := list.size();
		
		var contains := list.contains(2);
		assert contains;
		contains := list.contains(10);
		assert !contains;

		assert size == 3;

		list.put(2, "Hey");
		size := list.size();
		val := list.get(2);
		assert val == "Hey";
		
		list.remove(20);
		contains := list.contains(20);
		assert !contains;
		contains := list.contains(0);
		assert !contains;
		size := list.size();
		
		assert size == 2;
	}
}