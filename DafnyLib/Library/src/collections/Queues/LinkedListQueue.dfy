/*
 *				  --------------------------------
 * HEAD (dequeue) ->O->O->O->O->O->O->O->O->O->O-> TAIL (enqueue)
 *				  --------------------------------
 */

//The keyword autocontracts means that the predicate called "Valid" will be required and ensured for every method in the class
class {:autocontracts} Queue<T> {
	//Those variables are on the implementation side, they will hold the main elements of the queue
	var head: Node<T>;
	var tail: Node<T>;
	var queueSize: int;

	//Those variables are on the specification side, they will hold the elements which help to prove the validity of the queue
	ghost var QueueContent: seq<T>; //A sequence of all the contained values
	ghost var Repr: set<object>; //A dynamic frame of all the objects in the system
	ghost var QueueNodes: set<Node<T>>; //A set of all the node objects in the queue

	//This predicate determines if the queue is empty or not, given that the class is marked as "{:autocontracts}", this predicate will be required and ensured for EVERY method in the class
	predicate Empty()
		reads this;
	{
		//The queue is empty if the size is equal to 0 and of the nodes and content are empty
		this.QueueContent == [] && this.QueueNodes == {} && this.queueSize == 0
	}

	//This predicate determines of the queue state is valid or not
	predicate Valid()
		//It needs a read access to the current object and to the dynamic frame
		reads this, this.Repr;
	{
		//The current object must always be in the dynamic frame for the other methods to read/modify it
		(this in this.Repr) 
		&&
		//All the nodes in the queue must always be in the dynamic frame for the same reason than before
		(this.QueueNodes <= this.Repr)
		&&
		//If the head is null it implies that the tail is null, and vice versa
		(this.head == null <==> this.tail == null)
		&&
		(this.head == null ==> Empty())
		&&
		//If the head is not null, then :
		(this.head != null ==>
			//Both the head and the tail must be in the dynamic frame
			(this.head in this.Repr && this.tail in this.Repr)
			&& 
			//Both the head and the tail must be in queue nodes
			(this.head in this.QueueNodes && this.tail in this.QueueNodes)
			&& 
			(this.tail.next == null)
			&&
			//For every node in the queue nodes :
			(forall node :: node in this.QueueNodes ==>
				(node != null)
				&& 
				(node.Repr <= this.Repr)
				&&
				//The node must be considered as Valid
				(node.Valid())
				&&
				//If the successor of the node is null, then the node must be the queue's tail
				(node.next == null ==> node == this.tail)
				&&
				//If the successor of the node is not null, then it must be in the whole queue's nodes
				(node.next != null ==> node.next in this.QueueNodes)
			)
			&&
			//The queue's content must always be the same than the head node's content
			(this.QueueContent == this.head.QueueContent)
			&&
			(this.queueSize == |this.QueueContent|)
		)
	}
	
	//This method will be called when the 'new' keyword is used to instantiate a Queue
	constructor()
		//It will alter the current object
		modifies this;
		//After the method, the queue will be valid (thanks to autocontracts), and the dynamic frame (minus the current object) must contain only elements instantiated during the method (or nothing)
		ensures fresh(this.Repr - {this});
		//The queue must also be empty
		ensures Empty();
	{
		this.head := null;
		this.tail := null;
		
		this.Repr := {this};
		this.QueueContent := [];
		this.QueueNodes := {};
		this.queueSize := 0;
	}

	//This method returns true if the queue is considered as empty, false other wise
	method isEmpty() returns (isEmpty: bool)
		//The returned value must be equivalent to the result of the Empty() predicate
		ensures isEmpty <==> Empty();
	{
		isEmpty := this.head == null;
	}

	//This method return the size of the queue
	method size() returns (qSize: int)
		//The returned valud must be equal to the cardinality of the queue's content set
		ensures qSize == |this.QueueContent|;
	{
		qSize := this.queueSize;
	}
	
	//This method will add an item at the tail of the queue
	method enqueue(item: T)
		modifies this.Repr;
		//New elements only can be added to the dynamic frame (helps to avoid infinite loops in the queue)
		ensures fresh(this.Repr - old(this.Repr));
		//The queue content must be equal to the old queue content with the enqueued item added at the end
		ensures this.QueueContent == old(this.QueueContent) + [item];
	{
		var newNode := new Node<T>(item);

		//If the queue was empty, it is necessary to set the head and the tail to the same value
		if (this.tail == null) {
			this.head := newNode;
		} else {
			this.tail.next := newNode;
		}

		this.tail := newNode;
		this.queueSize := this.queueSize + 1;
		
		//Restoring the state in the queue by adding the inserted node to all the specification variables in the existing queue
		forall node | node in this.QueueNodes {
			node.QueueContent := node.QueueContent + [this.tail.value];
		}
		this.QueueContent := this.head.QueueContent;
		
		forall node | node in this.QueueNodes {
			node.Repr := node.Repr + newNode.Repr;
		}
		this.Repr := this.Repr + newNode.Repr;

		this.QueueNodes := this.QueueNodes + {newNode};
	}

	//This method will only return the topmost element of the queue (the head)
	method peek() returns (value: T)
		requires !Empty();
		//The returned element must be equal to the first element in the queue contents sequence
		ensures value == QueueContent[0];
	{
		value := this.head.value;
	}
	
	//This method will remove and return the topmost element of the queue (the head)
	method dequeue()  returns (value: T)
		requires !Empty();
		modifies this.Repr;
		//The returned element must be equal to the first element in the queue contents sequence
		ensures value == old(this.QueueContent)[0];
		//The current queue content sequence must be equal to the old one minus the first element
		ensures this.QueueContent == old(this.QueueContent)[1..];
	{
		value := this.head.value;

		var oldHead := this.head;
		this.head := this.head.next;

		//If the queue is now empty, we clean the state
		if (this.head == null) {
			this.tail := null;
			this.QueueContent := [];
			this.QueueNodes := {};
		} else {
			//Note that the QueueNodes set is not cleaned when we remove a node without emptying the queue, this is not required because we don't have an equality check between the sets in our specification, only a subset check
			this.QueueContent := this.head.QueueContent;
		}

		//The queue size is reduced
		this.queueSize := this.queueSize - 1;
	}
}

class {:autocontracts} Node<T> {
	var value: T;
	var next: Node<T>;

	ghost var QueueContent: seq<T>;
	ghost var Repr: set<object>;

	predicate Valid()
		reads this, this.Repr;
	{
		(this in this.Repr)
		&&
		(null !in this.Repr) 
		&&
		(this.next != null ==>
			(this.next in this.Repr)
			&&
			(this.next.Repr <= this.Repr) 
			&&
			//In order to validate the continuity of the queue, we check that every node contains itself and the following nodes
			(this.QueueContent == [this.value] + this.next.QueueContent)
		) 

		&&
		(this.next == null ==>
			(this.QueueContent == [this.value])
		)
	}

	constructor(assignedValue: T)
		modifies this;
		ensures fresh(Repr - {this});
		ensures next == null;
		ensures this.value == assignedValue;
		ensures this.QueueContent == [assignedValue];
	{
		this.next := null;
		this.QueueContent := [assignedValue];
		this.Repr := {this};
		this.value := assignedValue;
	}
}

class Main<U> {
	method Main() {
		var dequeuedValue: int;
		var peekedValue: int;
		var size: int;
		var isEmpty: bool;
		var queue := new Queue<int>();
		
		size := queue.size();
		assert size == 0;
		isEmpty := queue.isEmpty();
		assert isEmpty;
		queue.enqueue(10);
		size := queue.size();
		assert size == 1;
		isEmpty := queue.isEmpty();
		peekedValue := queue.peek();
		assert peekedValue == 10;
		assert !isEmpty;
		dequeuedValue := queue.dequeue();
		assert dequeuedValue == 10;
		queue.enqueue(15);
		queue.enqueue(20);
		queue.enqueue(25);
		queue.enqueue(30);
		size := queue.size();
		assert size == 4;
		dequeuedValue := queue.dequeue();
		assert dequeuedValue == 15;
		assert queue.tail != null;
		assert queue.head != null;
		dequeuedValue := queue.dequeue();
		assert dequeuedValue == 20;
		dequeuedValue := queue.dequeue();
		assert dequeuedValue == 25;
		dequeuedValue := queue.dequeue();
		assert dequeuedValue == 30;
		queue.enqueue(25);
		dequeuedValue := queue.dequeue();
		assert queue.tail == null;
		assert queue.head == null;
		isEmpty := queue.isEmpty();
		assert isEmpty;
		queue.enqueue(25);
	}
}