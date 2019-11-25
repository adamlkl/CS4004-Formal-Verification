method checkPalindrome(s: seq<int>) returns (res: bool)
requires |s| >= 0 
ensures isPalindrome(s) <==> res == true 
{
    res := true;
    var i := 0 ;
    var j := | s | - 1 ;
    while ( i < j && res == true)
    invariant i == |s| -1 - j && i <= |s| && ((forall k :: 0 <= k < i ==> s[k] == s[|s|-k-1]) <==> res == true) 
    decreases |s| - i
    {
        if (s[i] != s[j]) 
        {
            res := false;
        } 
        else {
            
        }
        i := i + 1 ;
        j := j - 1;
    }
}

predicate palindrome(s1: seq<int>, s2: seq<int>)
{
    |s1| == |s2| && forall x : int :: 0 <= x < |s1| ==> s1[x] == s2[|s2|-x-1]
}

predicate isPalindrome(s: seq<int>)
{
    forall x : int :: 0 <= x < |s| ==> s[x] == s[|s|-x-1]
}