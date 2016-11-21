class MainProgram {
	method Main() {
		var stack1 := new LinkedListStack<int>();
		var isEmpty: bool, poppedValue: int, peekedValue: int, stackSize: int;

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

	}
}


class LinkedListStack<T> {
	//Top node of the stack
	var top: Node<T>;
	//Size of the stack
	var stackSize: int;

	//Dynamic frame: allow read/modify access to all the elements in the stack
	ghost var Repr: set<Node<T>>;
	//Current sequence of nodes in the stack
	ghost var CurrentNodes: seq<Node<T>>;

	//Initialize the stack
	constructor()
		//It only modifies the current object
		modifies this;
		//The stack will be valid
		ensures Valid()
		//The stack will be empty
		ensures isEmptyPredicate();
		//The dynamic frame will be empty
		ensures this.Repr == {};
		//The stack size will be 0
		ensures this.stackSize == 0;
	{
		this.top := null;
		this.stackSize := 0;
		this.CurrentNodes := [];
		this.Repr := {};
	}

	//Specification only: verifies the validity of the stack
	predicate Valid()
		//The predicate reads the current object and all the objects in the dynamic frame of the stack
		reads this, this.Repr;
	{
		//When the top pointer is null, then the size must be zero and the ghost representation must be empty
		(this.top == null ==>	
			(this.stackSize == 0)
			&&
			(isEmptyPredicate())
		)
		&&
		//When the top pointer is not null, then :
		(this.top != null ==>
			//The top pointer must be accessible in the dynamic frame for the next statements
			(this.top in this.Repr)
			&&
			//The dynamic frame of the top node must be the same than the one in the stack
			(this.top.Repr == this.Repr)
			&& 
			//The nodes listed in the stack must be the same than the one in the current top node's linked list
			(this.top.CurrentNodes == this.CurrentNodes)
			&&
			//The stackSize variable must be at all times the same than the cardinality of the currentNodes set
			(this.stackSize == getStackSizeFunction())
			&&
			//The top node must be valid (This is recursive and will check all the linked list)
			(this.top.Valid())
		)
	}


	//Specification only: returns true if the stack is supposed to be empty
	predicate isEmptyPredicate()
		//The predicate reads the current object
		reads this;
	{
		this.CurrentNodes == [] && getStackSizeFunction() == 0
	}
	
	//Specification only: returns the cardinality of the current nodes set (the supposed stack size)
	function getStackSizeFunction() : int 
		//The predicate reads the current object
		reads this;
	{
		|this.CurrentNodes|
	}

	//Method returning true if the stack is empty, false otherwise
	method isEmpty() returns (result: bool)
		//The stack must be valid
		requires Valid();
		//The result will be equivalent to the predicate validating the emptiness of the stack
		ensures result <==> isEmptyPredicate();
	{
		result := this.top == null && this.stackSize == 0;
	}

	//Method returning the current size of the stack
	method size() returns (size: int)
		//The stack must be valid
		requires Valid();
		//The result will be the supposed stack size
		ensures size == getStackSizeFunction();
	{
		size := stackSize;
	}

	//Method inserting the given value to the top of the stack
	method push(value: T)
		//The stack must be valid
		requires Valid();
		//The method will only modify the current object
		modifies this;	
		//The stack will be valid after the modification
		ensures Valid();
		//The specification sequence will be the same than before the modification except that the new top node will have been prepended to it
		ensures this.CurrentNodes == [top] + old(this.CurrentNodes)
		//The top object will have been instantiated in this method, its value will be equal to the given value and its next node will be the old top node
		ensures fresh(top) && top.value == value && top.next == old(top);
		//The size must have increased by 1
		ensures this.stackSize == old(this.stackSize) + 1;
	{
		top := new Node<T>(value, this.top);
		this.stackSize := this.stackSize + 1;
		this.CurrentNodes := [this.top] + this.CurrentNodes;
		this.Repr := this.top.Repr + {top};
	}

	//Method removing and returning the top value of the stack
	method pop() returns (value: T)
	//The stack must be valid
		requires Valid();
		//The stack must not be empty
		requires !isEmptyPredicate();
		//The method will only modify the current object
		modifies this;
		//The stack will be valid after the modification
		ensures Valid();
		//The specification sequence will be the same than before the modification except that the previous first node has been removed
		ensures this.CurrentNodes == old(this.CurrentNodes)[1..];
		//The returned value must be the previously first one in the specification sequence
		ensures value == old(this.CurrentNodes)[0].value;
		//The size must have reduced by 1
		ensures this.stackSize == old(this.stackSize) - 1;
	{
		var tmp := top;
		value := top.value;
		top := top.next;
		this.stackSize := this.stackSize - 1;
		this.CurrentNodes := this.CurrentNodes[1..];
		this.Repr := this.Repr - {tmp};
	}

	//Method only returning the top value of the stack
	method peek() returns (value: T)
		//The stack must be valid
		requires Valid();
		//The stack must not be empty
		requires !isEmptyPredicate();
		//The returned value must be the first one in the specification sequence
		ensures value == this.CurrentNodes[0].value;
	{
		value := top.value;
	}
}

//Node class for the linked list
class Node<T> {
	var value: T;
	var next: Node<T>;

	//Dynamic frame: allow read/modify access to all the elements in the linked list
	ghost var Repr: set<Node<T>>;
	//Current sequence of nodes in the linked list
	ghost var CurrentNodes: seq<Node<T>>;

	//Specification only: verifies the validity of the node
	predicate Valid()
		//The predicate reads the current object and all the objects in the dynamic frame of the node
		reads this, Repr;
	{
		//The current object must be in the dynamic frame
		(this in Repr)
		&&
		//If the next node is null, then : There is no previous nodes
		(this.next == null ==>	this.CurrentNodes == [this] 
								&& 
								//And the current frame only contains this node
								this.Repr == {this}
		)
		&& 
		//If the next node is not null, then :
		(this.next != null ==> 
								//The next object should be in the dynamic frame
								this.next in this.Repr
								&&
								this.Repr == {this} + this.next.Repr
								&& //The current object should not already be in the previous nodes (in order to avoid infinite linked lists)
								this !in this.next.Repr
								&&
								this.CurrentNodes == [this] + this.next.CurrentNodes
								&&
								//The next node should be valid (Recursive)
								this.next.Valid())
	}
			

	//Initialize the node
	constructor(value: T, next: Node<T>)
		//If next is not null, it should be valid and the current node should not be present in the next dynamic frame
		requires next != null ==> next.Valid() && this !in next.Repr;
		//The method will only modify the current object
		modifies this;
		//The correct values should have been assigned
		ensures this.next == next && this.value == value;
		//The current node should be valid
		ensures Valid();
	{
		this.value := value;
		this.next := next;

		if (this.next == null) {
			//Populating the initial specification state
			this.Repr := {this};
			this.CurrentNodes := [this];
		} else {
			//Populating the specification state when already defined
			this.Repr := {this} + this.next.Repr;
			this.CurrentNodes := [this] + this.next.CurrentNodes;
		}
	}

}