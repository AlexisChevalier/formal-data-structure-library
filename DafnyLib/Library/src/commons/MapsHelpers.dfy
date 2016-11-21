class MapsHelpers {
	// This method returns the union of two maps (they must not overlap)
	// Source: http://www.lexicalscope.com/blog/2014/04/17/inverting-maps-in-dafny
	static function unionMaps<U, V>(m: map<U,V>, m': map<U,V>): map<U,V>
		requires m !! m'; // disjoint
		ensures forall i :: i in unionMaps(m, m') <==> i in m || i in m';
		ensures forall i :: i in m ==> unionMaps(m, m')[i] == m[i];
		ensures forall i :: i in m' ==> unionMaps(m, m')[i] == m'[i];
	{
		map i | i in (domainMap(m) + domainMap(m')) :: if i in m then m[i] else m'[i]
	}

	// This method returns the domain of a map
	// Source: http://www.lexicalscope.com/blog/2014/04/17/inverting-maps-in-dafny
	static function domainMap<U,V>(m: map<U,V>) : set<U>
		ensures domainMap(m) == set u : U | u in m :: u;
		ensures forall u :: u in domainMap(m) ==> u in m;
		ensures (map i | i in domainMap(m) :: m[i]) == m;
	{
			set u : U | u in m :: u
	}
	
	// This method removes the given key from the given map and returns the result
	static function excludeFromMap<U, V>(m: map<U, V>, e: U) : map<U, V>
		ensures e !in excludeFromMap(m, e);
		ensures domainMap(m) - {e} == domainMap(excludeFromMap(m, e));
		ensures excludeFromMap(m, e) == map i | i in m && i != e :: m[i];
		ensures e in m ==> |domainMap(m)| == |domainMap(excludeFromMap(m, e))| + 1;
		ensures e !in m ==> |domainMap(m)| == |domainMap(excludeFromMap(m, e))|;
		ensures forall u :: u in m && u != e ==> u in excludeFromMap(m, e);
 	{
		map i | i in m && i != e :: m[i]
	}
}