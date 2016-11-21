class MainProgram {
	method Main()
	{
		var arrInt := new int[4];
		arrInt[0] := 2;
		arrInt[1] := 3;
		arrInt[2] := 4;
		arrInt[3] := 1;
    
		assert arrInt[..] == [2,3,4,1];
		
		BubbleSortInt.sort(arrInt);

		assert arrInt[..] == [1,2,3,4];
	}
}

class BubbleSortInt {

	//Returns true if array sorted between the given bounds, false otherwise
	static predicate sorted(arr:array<int>, low: int, high: int)
		requires arr != null;
		//The indices must be inside the array's bounds
		requires 0 <= low <= high <= arr.Length;
		reads arr;
	{
		forall a, b :: low <= a < b < high ==> lessOrEqual(arr[a], arr[b])
	}

	//Return true if the value a is inferior OR equal to the value b
	static predicate method lessOrEqual(a: int, b: int) 
	{
		a <= b
	}

	//Return true if the value a is inferior OR equal to the value b
	static predicate method less(a: int, b: int) 
	{
		a < b
	}

	static method sort(arr:array<int>)
		//The array must be valid
		requires arr != null && arr.Length > 1;
		modifies arr;
		//The array must be completely sorted
		ensures sorted(arr, 0, arr.Length);
		//The array must have the same values, in a possible different order
		ensures multiset(arr[..]) == multiset(old(arr[..]));
	{
		var outerCounter := arr.Length - 1;
		var innerCounter := 0;

		while(outerCounter > 0) 
			//The inner counter will always be between 0 (inclusive) and the array size
			invariant 0 <= outerCounter < arr.Length;
			//The end of the array is already sorted (from the outer counter inclusive to the end)
			invariant sorted(arr, outerCounter, arr.Length);
			//All the array elements at the right of the outer counter are superior to the elements at the left of the outer counter
			invariant forall a, b :: 0 <= a < outerCounter && outerCounter < b < arr.Length ==> arr[a] <= arr[b];
			//The operation is just a permutation, values are not changed
			invariant multiset(arr[..]) == multiset(old(arr[..]));
			//The termination condition is that the outer counter reduces at each iteration
			decreases outerCounter;
		{
			innerCounter := 0;

			while(innerCounter < outerCounter)
				//The inner counter will always be between 0 and the outer counter (both inclusive)
				invariant 0 <= innerCounter <= outerCounter;
				//The end of the array is already sorted (from the outer counter inclusive to the end)
				invariant sorted(arr, outerCounter, arr.Length);
				//All the array elements at the right of the outer counter are superior to the elements at the left of the outer counter
				invariant forall a, b :: 0 <= a < outerCounter && outerCounter < b < arr.Length ==> arr[a] <= arr[b];
				//The array element pointed by the inner counter is superior or equal to all the elements at the left of the inner counter
				invariant forall a :: 0 <= a < innerCounter ==> arr[a] <= arr[innerCounter];
				//The operation is just a permutation, values are not changed
				invariant multiset(arr[..]) == multiset(old(arr[..]));
				//The termination condition is that the difference between the outer counter and the inner counter reduces at each iteration
				decreases outerCounter - innerCounter;
			{
				if (arr[innerCounter] > arr[innerCounter + 1]) {
					arr[innerCounter], arr[innerCounter + 1] := arr[innerCounter + 1], arr[innerCounter];
				}

				innerCounter := innerCounter + 1;
			}


			outerCounter := outerCounter - 1;
		}
	}
}