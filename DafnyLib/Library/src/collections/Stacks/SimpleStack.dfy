/*
 * This is the simplest example possible for a stack, it doesn't provide any state validation features, it only provides validation at the interface level for each operation
 *
 * For instance, there is no correlation between the stackSize and the emptiness of the stack, the fact that the top node is null doesn't means that the stackSize is 0
 */

class MainProgram {
	method Main() {
		var stack1 := new SimpleStack<int>();
		var stack2 := new SimpleStack<int>();
		
		var empty := stack1.isEmpty();
		assert empty;

		var size := stack1.size();
		assert size == 0;

		stack1.push(1);
		stack2.push(2);
		stack1.push(3);

		size := stack1.size();
		assert size == 2;

		size := stack2.size();
		assert size == 1;

		var test1 := stack1.pop();
		var test2 := stack2.pop();
		stack1.push(3);
		stack1.push(3);

		size := stack1.size();
		assert size == 3;
		
		empty := stack1.isEmpty();
		assert !empty;
		size := stack2.size();
		assert size == 0;
		empty := stack2.isEmpty();
		assert empty;


		assert test1 == 3;
		assert test2 == 2;

		test1 := stack1.peek();
		assert test1 == 3;

		test1 := stack1.pop();

		assert test1 == 3;
		test1 := stack1.pop();
		test1 := stack1.pop();
		assert test1 == 1;
	}
}

class SimpleStack<T> {
	//Top node of the stack
	var top: Node<T>;

	//Size of the stack
	var stackSize: int;

	//Initialize the stack
	constructor()
		modifies this;
		ensures this.stackSize == 0 && this.top == null;
	{
		this.top := null;
		this.stackSize := 0;
	}
	
	//Return the size of the stack
	method size() returns (s: int)
		ensures this.stackSize == s;
	{
		s := this.stackSize;
	}

	//Returns true if the stack is empty, false otherwise
	method isEmpty() returns (empty: bool)
		//The fact the top node is null must always be equivalent to the result
		ensures empty <==> this.top == null;
	{
		empty := this.top == null;
	}

	//Returns the top value of the stack without altering it
	method peek() returns (value: T)
		//The stack should not be empty
		requires this.top != null && this.stackSize != 0;
		//The returned value should be the topmost one
		ensures value == this.top.value;
	{
		value := this.top.value;
	}

	//Adds the value to the top of the stack
	method push(value: T)
		//This method will alter the current object
		modifies this;
		//The top node must be freshly instantiated, his value must be the given one and must be followed by the previous top node
		ensures fresh(top) && top.value == value && top.next == old(top);
		//The stackSize has been modified
		ensures this.stackSize == old(this.stackSize) + 1;
	{
		var tmp: Node<T>;
		tmp := new Node<T>(value, top);
		top := tmp;
		this.stackSize := this.stackSize + 1;
	}

	//Remove and returns the top value of the stack
	method pop() returns (value: T)
		//The stack should not be empty
		requires this.top != null && this.stackSize != 0;
		//This method will alter the current object
		modifies this;
		//The top node must be the previous next one (can be null) and the returned value must be the one of the previous next node
		ensures top == old(top).next && value == old(top).value;
		//The stackSize has been modified
		ensures this.stackSize == old(this.stackSize) - 1;
	{
		value := top.value;
		top := top.next;
		this.stackSize := this.stackSize - 1;
	}
}

//Node class for the linked list
class Node<T> {
	var value: T;
	var next: Node<T>;

	//Initialize the node
	constructor(value: T, next: Node<T>)
		modifies this;
		ensures this.next == next && this.value == value;
	{
		this.value := value;
		this.next := next;
	}
}