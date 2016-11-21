class ArrayStack<T> {
	var arr: array<T>;
	var pointer: int;
	var maxSize: int;

	//Initialize the stack
	constructor(stackSize:int)
		//The size must be positive
		requires stackSize > 0;
		//It only modifies the current object
		modifies this;
		//The stack will be valid
		ensures Valid()
		//The stack will be empty
		ensures Empty();
		//The stack will have the correct size
		ensures this.arr.Length == maxSize == stackSize;
		//The pointer will be equal to -1
		ensures this.pointer == -1;
		//The array must be instantiated in this method
		ensures fresh(arr);
	{
		this.maxSize := stackSize;
		this.arr := new T[this.maxSize];
		this.pointer := -1;
	}

	//Specification only: verifies the validity of the stack
	predicate Valid()
		//The predicate reads the current object and all the objects in the dynamic frame of the stack
		reads this, arr;
	{
		//The array must not be null
		(this.arr != null)
		&&
		//The max array size must not be inferior or equal to zero
		(this.maxSize > 0)
		&&
		//The array length must be equal to the max array size
		(this.arr.Length == maxSize)
		&&
		//The pointer must always be maintained between -1 (inclusive) and the array max size (exclusive)
		(-1 <= this.pointer < this.maxSize)
	}


	//Specification only: returns true if the stack is supposed to be empty
	predicate Empty()
		//The predicate reads the current object
		reads this;
	{
		this.pointer == -1
	}

	//Specification only: returns true if the stack is supposed to be full
	predicate Full()
		//The predicate reads the current object
		reads this;
	{
		 getStackSizeFunction() == this.maxSize
	}
	
	//Specification only: returns the cardinality of the current nodes set (the supposed stack size)
	function getStackSizeFunction() : int 
		//The predicate reads the current object
		reads this;
	{
		this.pointer + 1
	}

	//Method returning true if the stack is empty, false otherwise
	method isEmpty() returns (result: bool)
		//The result will be equivalent to the predicate validating the emptiness of the stack
		ensures result <==> Empty();
	{
		result := this.pointer == -1;
	}

	//Method returning true if the stack is full, false otherwise
	method isFull() returns (result: bool)
		//The result will be equivalent to the predicate validating the fullness of the stack
		ensures result <==> Full();
	{
		result := this.pointer == this.maxSize - 1;
	}

	//Method returning the current size of the stack
	method size() returns (size: int)
		//The stack must be valid
		requires Valid();
		//The result will be the supposed stack size
		ensures size == getStackSizeFunction();
	{
		size := this.pointer + 1;
	}

	//Method inserting the given value to the top of the stack
	method push(value: T)
		//The stack must be valid
		requires Valid();
		//The stack must not be full
		requires !Full();
		//The stack modifies the pointer (it's a scalar type so ` is used instead of .) and the array
		modifies this`pointer, this.arr;
		//The stack will be valid after the method call
		ensures Valid();
		//The pointer will have increased by one
		ensures this.pointer == old(this.pointer) + 1
		//The part of the array at the left of the pointer (excluded) will be exactly the same than the previous version
		ensures this.pointer > 0 ==> forall k :: 0 <= k < this.pointer ==> arr[k] == old(arr[k])
		//The cell of the array pointed by the pointer will be now equal to the given value
		ensures arr[this.pointer] == value;
	{
		this.pointer := this.pointer + 1;
		this.arr[this.pointer] := value;
	}

	//Method removing and returning the top value of the stack
	method pop() returns (value: T)
		//The stack must be valid
		requires Valid();
		//The stack must not be empty
		requires !Empty();
		//The stack modifies the pointer (scalar type so ` instead of .)
		modifies this`pointer;
		//The stack will be valid after the method call
		ensures Valid();
		//The pointer will have decreased by one
		ensures this.pointer == old(this.pointer) - 1;
		//The returned value must be equal to the previously pointed value
		ensures value == this.arr[old(this.pointer)];
	{
		value := this.arr[this.pointer];
		this.pointer := this.pointer - 1;
	}

	//Method only returning the top value of the stack
	method peek() returns (value: T)
		//The stack must be valid
		requires Valid();
		//The stack must not be empty
		requires !Empty();
		//The returned value must be equal to the currently pointed value
		ensures value == this.arr[this.pointer];
	{
		value := this.arr[this.pointer];
	}
}

class MainProgram {
	method Main() {
		var stack1 := new ArrayStack<int>(10);
		var isEmpty: bool, poppedValue: int, peekedValue: int, stackSize: int, isFull: bool;

		isEmpty := stack1.isEmpty();
		stackSize := stack1.size();
		assert isEmpty == true;
		assert stackSize == 0;

		stack1.push(10);
		stack1.push(11);
		stackSize := stack1.size();
		assert stackSize == 2;

		peekedValue := stack1.peek();
		assert peekedValue == 11;
		
		poppedValue := stack1.pop();
		assert poppedValue == 11;

		stackSize := stack1.size();
		assert stackSize == 1;

		stack1.push(20);
		stackSize := stack1.size();
		assert stackSize == 2;

		isEmpty := stack1.isEmpty();
		assert isEmpty == false;

		poppedValue := stack1.pop();
		assert poppedValue == 20;
		
		poppedValue := stack1.pop();
		assert poppedValue == 10;
		
		stackSize := stack1.size();
		assert stackSize == 0;

		isEmpty := stack1.isEmpty();
		assert isEmpty == true;

		stack1.push(1);
		stack1.push(2);
		stack1.push(3);
		stack1.push(4);
		stack1.push(5);
		stack1.push(6);
		stack1.push(7);
		stack1.push(8);
		stack1.push(9);
		stack1.push(10);

		isFull := stack1.isFull();
		assert isFull == true;
	}
}