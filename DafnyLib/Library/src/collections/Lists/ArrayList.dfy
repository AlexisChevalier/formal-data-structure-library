
//The keyword autocontracts means that the predicate called "Valid" will be required and ensured for every method in the class
class {:autocontracts} ArrayList<T> {
	//Those variables are on the implementation side, they will hold the main elements of the ArrayList
	var list: array<T>;
	var pointer: int;
	var maxSize: int;
	var resizeFactor: int;
	
	//Those variables are on the specification side, they will hold the elements which help to prove the validity of the ArrayList
	ghost var ListElements: seq<T>; //This will hold, in order, all the elements in the list
	ghost var Repr: set<object>; //This is the dynamic frame, it will hold all the elements which need to be accessed during the program

	//This predicate returns true if the list is in a valid state
	predicate Valid() 
		//It needs access to the current object and to the dynamic frame
		reads this, this.Repr;
	{
		(this in this.Repr)
		&&
		//The array can never be null, must be in the dynamic frame and its length should be equal to the max size
		(this.list != null && this.list.Length == this.maxSize && this.list in this.Repr)
		&&
		(this.resizeFactor > 0 && this.maxSize > 0)
		&&
		//The cardinality of the sequence holding the elements must be equal to the current pointer
		(|this.ListElements| == this.pointer)
		&&
		//The pointer must be inferior to the max size
		(this.pointer < this.maxSize)
		&&
		//For every integer between 0 and the current pointer (exclusive), the element at the ith position in the array must be the same than the element at the ith position in the sequence
		(forall i :: 0 <= i < this.pointer ==> this.list[i] == this.ListElements[i])
	}
	
	//This data structure offers two constructors, a simple one, which uses a default size and resize factor of 5 (this one), and another one, which offers the choice
	constructor() 
		modifies this;
		ensures this.pointer == 0;
	{
		this.Repr := {this};
		this.maxSize := 5;
		this.list := new T[this.maxSize];
		this.pointer := 0;
		this.resizeFactor := 5;
		this.ListElements := [];
		this.Repr := this.Repr + {this.list};
	}

	constructor WithSizeAndResizeFactor(size: int, resizeFactor: int)
		requires size > 0 && resizeFactor > 0;
		modifies this;
		ensures this.pointer == 0;
	{
		this.Repr := {this};
		this.maxSize := size;
		this.list := new T[size];
		this.pointer := 0;
		this.resizeFactor := resizeFactor;
		this.ListElements := [];
		this.Repr := this.Repr + {this.list};
	}

	//This method returns the current size of the list (the actual size, the number of elemets in the list)
	method size() returns (lSize: int)
		//The returned value must be equal to the cardinality of the list of elements
		ensures lSize == |ListElements|;
	{
		lSize := pointer;
	}

	//Returns true if empty, false otherwise
	method isEmpty() returns (lEmpty: bool)
		//The result must be true if the cardinality of the list of elements is equal to 0, it must be false otherwise
		ensures lEmpty <==> |ListElements| == 0;
	{
		return this.pointer == 0;
	}

	//This method returns the element located at the given position
	method get(position: int) returns (element: T) 
		//The position must be valid (between 0 and the current pointer)
		requires position >= 0 && position < this.pointer;
		ensures element == this.ListElements[position];
	{
		element := this.list[position];
	}

	//This method removes the element located at the given position and shifts the elements after its position by one position to the left in order to keep an array without holes
	method remove(position: int) 
		//The position must be valid (between 0 and the current pointer)
		requires position >= 0 && position < this.pointer;
		modifies this.Repr;
		ensures this.pointer == old(this.pointer) - 1;
		//Every elements between the given position (included) and the current pointer must be equal to the element on its right in the old array
		ensures forall k :: position <= k < this.pointer ==> this.list[k] == old(this.list[k + 1])
	{
		var i := position;
		this.ListElements := this.ListElements[0..position] + this.ListElements[position + 1..this.pointer];

		forall (i | position <= i < this.list.Length - 1) {
           this.list[i] := this.list[i+1];
        }

		this.pointer := this.pointer - 1;
	}

	//This method inserts an element at the end of the list, it also increases the size of the array if required
	//It also returns the position of the inserted element
	method add(element: T) returns (position: int)
		modifies this.Repr;
		ensures this.pointer == old(this.pointer) + 1;
		//The returned position must be equal to the old pointer before the increase
		ensures position == old(this.pointer);
		ensures this.list[position] == element;
		//All the elements that were in the array before the method must be the same ones than the updated list
		ensures forall k :: 0 <= k < position ==> this.list[k] == old(this.list[k])
		//If array was full, then the array must have been freshly instantiated and resized
		ensures old(this.pointer) == old(this.maxSize) - 1 ==> fresh(this.list) && this.list.Length == old(this.list.Length) + this.resizeFactor;
	{
		if (this.pointer == this.maxSize - 1) {
			private_resizeList();
		}

		this.list[this.pointer] := element;
		this.ListElements := this.ListElements + [element];

		position := this.pointer;
		this.pointer := this.pointer + 1;
	}

	//This method increases the size of the array and restores all the element present in the list before the resizing
	method private_resizeList()
		modifies Repr;
		//The array must have been freshly instantiated 
		ensures fresh(this.list);
		ensures this.maxSize == old(this.maxSize) + this.resizeFactor;
		ensures old(this.ListElements) == this.ListElements;
		//All the previously existing elements must be present in the resized array
		ensures forall i :: 0 <= i < this.pointer ==> old(this.list)[i] == this.list[i];
	{
		this.maxSize := this.maxSize + this.resizeFactor;
		var newList := new T[this.maxSize];

		forall (i | 0 <= i < this.pointer) {
           newList[i] := this.list[i];
        }

		this.Repr := this.Repr - {this.list};
		this.list := newList;
		this.Repr := this.Repr + {this.list};
	}
}

class MainProgram {
	method Main() {
		var list := new ArrayList<string>();

		var empty := list.isEmpty();

		assert empty;

		var pos := list.add("Hello");

		assert pos == 0;

		var el := list.get(pos);

		assert el == "Hello";

		var size := list.size();
		assert size == 1;

		list.remove(pos);

		size := list.size();
		assert size == 0;

		pos := list.add("World");
		assert pos == 0;
		pos := list.add("How");
		assert pos == 1;
		pos := list.add("Are");
		assert pos == 2;
		pos := list.add("You");
		assert pos == 3;

		size := list.size();
		assert size == 4;

		empty := list.isEmpty();

		assert !empty;

		el := list.get(pos);

		assert el == "You";

		el := list.get(0);

		assert el == "World";
		
		list.remove(0);
		list.remove(1);

		el := list.get(1);

		assert el == "You";

		pos := list.add("Test");
		assert pos == 2;
	}
}