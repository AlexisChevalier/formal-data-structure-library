class MainProgram {
	method Main()
	{
		var arrInt := new int[4];
		arrInt[0] := 2;
		arrInt[1] := 3;
		arrInt[2] := 4;
		arrInt[3] := 1;
    
		assert arrInt[..] == [2,3,4,1];
		
		InsertionSortInt.sort(arrInt);

		assert arrInt[..] == [1,2,3,4];
	}
}

class InsertionSortInt {

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
		var outerCounter := 0;
		var innerCounter := 0;

		while (outerCounter != arr.Length)
			//The outer counter will always be between 0 and the array size (both inclusive)
			invariant 0 <= outerCounter <= arr.Length;
			//The beginning of the array is already sorted (from 0 to outer counter (exclusive))
			invariant sorted(arr, 0, outerCounter);
			//The operation is just a permutation, values are not changed
			invariant multiset(arr[..]) == multiset(old(arr[..]));
		{
			innerCounter := outerCounter;
			while(innerCounter > 0 && less(arr[innerCounter], arr[innerCounter - 1]))
				//The inner counter will always be between 0 and the outer counter (both inclusive)
				invariant 0 <= innerCounter <= outerCounter;
				//The beginning of the array (before outer counter, inclusive) must be sorted, however, the element being permutted is ommitted
				//since it can break the sort invariant during this loop
				invariant forall a, b :: 0 <= a < b <= outerCounter && b != innerCounter ==> lessOrEqual(arr[a], arr[b]);
				//The operation is just a permutation, values are not changed
				invariant multiset(arr[..]) == multiset(old(arr[..]));
			{
				arr[innerCounter], arr[innerCounter -1] := arr[innerCounter - 1], arr[innerCounter];
				
				innerCounter := innerCounter - 1;
			}

			outerCounter := outerCounter + 1;
		}
	}
}

