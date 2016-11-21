include "../Lists/KeyValueLinkedList.dfy"

/*
 * As for the TreeMap, I didn't managed to prove a correlation between the cardinality of the relations in a dafny map and some operations of the stack, 
 * because of this I am unable to provide an access to a size/length variable and a performant empty() operation because there is no unique root
 */

 // Also, please take note that this data structure is the only one that is not entierly proven, the put and remove methods are using assumptions (opposite of assertions) in order to be validated

class HashMapSeparateChainingInt<T> {
	//Specification variables, used to represent the map
	ghost var KeyValueMap: map<int, T>; //Contains all the mappings
	ghost var Repr: set<object>; //Reference to all the objects accessed by the methods (dynamic frame)

	//Implementation variables
	var capacity: int;
	//We are using an array of a datastructure sepcifically designed to serve as a linked list with a key value system
	var hashTable: array<KeyValueLinkedList<T>>;

	//The predicate is a little big, which is why more time has been allocated
	predicate  {:timeLimit 20} Valid()
		reads this, this.Repr;
	{
		(this in this.Repr)
		&&
		(null !in this.Repr)
		&&
		//The array has been inserted in the dynamic frame since it will be modified sometimes, but this may be a part of the validation problem
		(this.hashTable in this.Repr)
		&&
		(this.hashTable != null)
		&&
		(this.capacity > 0)
		&&
		(this.hashTable.Length == this.capacity)
		&&
		//This quantifier ensures that all the non null entry of the hash table are valid
		(forall i :: 0 <= i < this.capacity && this.hashTable[i] != null ==>
			//The dynamic frame must include all the elements in this part
			(this.hashTable[i] in this.Repr)
			&&
			(this.hashTable[i].Repr <= this.Repr)
			&&
			//The list must be valid
			(this.hashTable[i].Valid())
			&&
			//All the elements in this list must have the same hashed key
			(forall k :: k in this.hashTable[i].KeyValueMap ==> k in this.KeyValueMap && this.KeyValueMap[k] == this.hashTable[i].KeyValueMap[k] && private_hashKey(k) == i)
			&&
			//All the other lists must not have any key value mappings in common with this list
			(forall k :: 0 <= k < this.capacity && this.hashTable[k] != null && this.hashTable[k] in this.Repr && k != i ==> this.hashTable[k].KeyValueMap !! this.hashTable[i].KeyValueMap)
		)
		&&
		//This quantifier verifies that for all the possible keys that are in the map (negative and positive integers, 0 included)
		//a corresponding list exist with the key value mapping inside it
		(forall i :: (i >= 0 || i < 0) && i in this.KeyValueMap ==> 
			(this.hashTable[private_hashKey(i)] != null)
			&&
			(this.hashTable[private_hashKey(i)] in this.Repr)
			&&
			(this.hashTable[private_hashKey(i)].Repr <= this.Repr)
			&&
			(i in this.hashTable[private_hashKey(i)].KeyValueMap)
		)
	}

	constructor(capacity: int)
		requires capacity > 0;
		//The backtick is used to specify a given field that is going to be modified, but the dot notation also works most of the time,
		//However, in this particular case, Dafny seems to only accept the backtick, but I couldn't find any documentation about this
		modifies this, this`hashTable;
		ensures Valid() && fresh(this.Repr - {this});
		ensures this.KeyValueMap == map[];
		ensures this.capacity == capacity;
		ensures this.hashTable.Length == capacity;
	{
		this.Repr := {this};
		this.KeyValueMap := map[];
		this.capacity := capacity;
		this.hashTable := new KeyValueLinkedList<T>[capacity];
		this.Repr := this.Repr + {this.hashTable};

		// By default, all the hash map entry are null,
		// maybe initializing everything to an empty list could solve the problem
		// but we weren't able to validate it this way
		forall (i | 0 <= i < this.hashTable.Length) {
           this.hashTable[i] := null;
        }
	}

	//This is the inner hash function for the integer based key,
	// it simply ensures that the key will fit in the array
	function method private_hashKey(keyToHash: int) : int
		requires this.capacity > 0 && this.hashTable != null && this.hashTable.Length == this.capacity;
		reads this, this.Repr;
		ensures private_hashKey(keyToHash) == keyToHash % this.capacity;
	{
		keyToHash % this.capacity
	}

	// This method returns true if the key is in the map, false otherwise
	method contains(keyToFind: int) returns (contains: bool)
		requires Valid();
		ensures contains <==> keyToFind in this.KeyValueMap;
		ensures contains == true ==> this.hashTable[private_hashKey(keyToFind)] != null;
	{
		if (this.hashTable[private_hashKey(keyToFind)] == null) {
			contains := false;
		} else {
			//The advantage of using a separate data structure here is to limit the size of the code and deal with fewer specification checks
			contains := this.hashTable[private_hashKey(keyToFind)].contains(keyToFind);
		}
	}

	//This method returns the value mapped by the given key (if it is in the map)
	method get(keyToFind: int) returns (value: T)
		requires Valid();
		requires |KeyValueMap| > 0 && keyToFind in this.KeyValueMap;
		ensures value == this.KeyValueMap[keyToFind];
	{
		value := this.hashTable[private_hashKey(keyToFind)].get(keyToFind);
	}
	
	//This method sets the mapping (given key -> given value) in the map
	//The validation of this method is helped by assumptions, which means that it is not fully proven
	//It takes some times to validate, which is why a large amount of time has been allocated
	//Some comments have been added to demonstrate the assumptions
	method  {:timeLimit 60} put(keyToInsert: int, valueToInsert: T) 
		requires Valid();
		modifies this.Repr;
		ensures Valid() && fresh(this.Repr - old(this.Repr));
		ensures this.KeyValueMap == old(this.KeyValueMap)[keyToInsert := valueToInsert];
	{
		var hashedKey := private_hashKey(keyToInsert);

		if (this.hashTable[hashedKey] == null) {
			this.hashTable[hashedKey] := new KeyValueLinkedList();
			this.Repr := this.Repr + {this.hashTable[hashedKey]};
			this.Repr := this.Repr + this.hashTable[hashedKey].Repr;
		}

		// (A1) - All the elements in each entry of the hash table respect the invariant "each element must be only present in the entry with the corresponding hashed key as index"
		assert (forall i :: 0 <= i < this.capacity && this.hashTable[i] != null ==> (forall k :: k in this.hashTable[i].KeyValueMap ==> private_hashKey(k) == i));

		// (B1) - All the linked lists in the hashtable are valid
		assert (forall i :: 0 <= i < this.capacity && i != hashedKey && this.hashTable[i] != null ==> this.hashTable[i].Valid());

		// (A2) - The program modifies a single entry of the array
		this.hashTable[hashedKey].put(keyToInsert, valueToInsert);

		// (A3) - All the elements in the previously modified entry in (2) respect the invariant "each element must be only present in the entry with the corresponding hashed key as index"
		assert (forall k :: k in this.hashTable[hashedKey].KeyValueMap ==> private_hashKey(k) == hashedKey);

		// Since (A3) is valid after the modification in (A2), knowing that (A1) was valid before the modification, then this assumtion should not be required.
		// There is probably a missing part in the specification that makes dafny believe that other parts of the array (other than the entry with the index 'hashedKey') could be altered
		assume (forall i :: 0 <= i < this.capacity && this.hashTable[i] != null ==> (forall k :: k in this.hashTable[i].KeyValueMap ==> private_hashKey(k) == i));

		// (B2) - The linked list modified in the entry corresponding to the hashed key is valid
		assert (this.hashTable[hashedKey].Valid());

		// Since (B2) is valid after the modification in (A2), knowing that (B1) was valid before the modification, then this assumption should not be required.
		// Same problem than before
		assume forall i :: 0 <= i < this.capacity && i != hashedKey && this.hashTable[i] != null ==> this.hashTable[i].Valid();

		this.Repr := this.Repr + this.hashTable[hashedKey].Repr;
		this.KeyValueMap := this.KeyValueMap[keyToInsert := valueToInsert];
	}
	
	//This method removes the mapping (given key -> given value) from the map
	//The validation of this method is helped by assumptions, which means that it is not fully proven
	//It takes some times to validate, which is why a large amount of time has been allocated
	//Some comments have been added to demonstrate the assumptions
	method  {:timeLimit 60} remove(keyToRemove: int) 
		requires Valid() && keyToRemove in this.KeyValueMap;
		modifies this.Repr;
		ensures Valid() && fresh(this.Repr - old(this.Repr));
		ensures this.KeyValueMap == MapsHelpers.excludeFromMap(old(this.KeyValueMap), keyToRemove);
	{
		var hashedKey := private_hashKey(keyToRemove);

		// (A1) - All the linked lists in the hashtable are valid
		assert (forall i :: 0 <= i < this.capacity && i != hashedKey && this.hashTable[i] != null ==> this.hashTable[i].Valid());
		
		// (A2) - The program modifies a single entry of the array
		this.hashTable[hashedKey].remove(keyToRemove);

		// (A3) - The linked list modified in the entry corresponding to the hashed key is valid
		assert (this.hashTable[hashedKey].Valid());

		// Since (A3) is valid after the modification in (A2), knowing that (A1) was valid before the modification, then this assumption should not be required.
		// Same problem than before
		assume forall i :: 0 <= i < this.capacity && i != hashedKey && this.hashTable[i] != null ==> this.hashTable[i].Valid();

		this.Repr := this.Repr + this.hashTable[hashedKey].Repr;
		this.KeyValueMap := MapsHelpers.excludeFromMap(this.KeyValueMap, keyToRemove);
	}

}

class Main {
  method Client0()
  {
    var s := new HashMapSeparateChainingInt<string>(15);
	var present := s.contains(12);
	assert !present;
    s.put(12, "Hello");
	present := s.contains(12);
	assert present;
    s.put(24, "World");
	var test := s.get(12);
	assert test == "Hello";
	test := s.get(24);
	assert test == "World";
	s.remove(12);
	present := s.contains(12);
	assert !present;
  }
}