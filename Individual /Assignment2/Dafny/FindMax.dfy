method findMax(s: seq<int>) returns(lo: int)
requires |s| > 0
ensures isMax(s, lo)
{
    assert(|s| > 0);
    assert(0 < 1 <= |s| && isMax(s[..1], 0));
    lo := 0;
    assert(0 <= lo < |s| && isMax(s[..1], lo)); 
    var hi : int := |s| - 1 ;
    assert(0 <= hi < |s| && isMax(s[hi..], 0));
    assert(hi - lo >= 0);
    while (lo < hi) 
        decreases hi - lo
        invariant 0 <= lo <= hi < |s|
        invariant (isMax2(s, 0, lo, lo) && isMax2(s, hi, |s|-1 , lo)) || (isMax2(s, 0, lo, hi) && isMax2(s, hi, |s|-1 , hi))
    {
        if(s[lo] <= s[hi])
        {
            lo := lo + 1;
        }
        else
        {
            hi := hi - 1;   
        }
    }   
}

predicate isMax2(s: seq<int>, lo: int, hi: int, max: int){
    0 <= max < |s| && 0 <= lo <= hi < |s| && forall x : int :: lo <= x <= hi ==> s[max] >= s[x]
}

predicate isMax(s : seq<int>, lo: int){
    0 <= lo < |s| && forall x: int :: 0 <= x < |s| ==> s[lo] >= s[x]
}
