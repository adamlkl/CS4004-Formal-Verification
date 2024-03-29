predicate isPrefixPred(pre:string, str:string)

{

	(|pre| <= |str|) && 

	pre == str[..|pre|]

}



predicate isNotPrefixPred(pre:string, str:string)

{

	(|pre| > |str|) || 

	pre != str[..|pre|]

}



lemma PrefixNegationLemma(pre:string, str:string)

	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)

	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)

{}



method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)

{
    //TODO: insert your code here
    if(|pre| == 0){
        return true;
    }
    
    if (|pre| > |str|){
        return false;
    }
    
    res := pre == str[..|pre|];
    return res;
}

predicate isSubstringPred(sub:string, str:string)

{

	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))

}



predicate isNotSubstringPred(sub:string, str:string)

{

	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))

}



lemma SubstringNegationLemma(sub:string, str:string)

	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)

	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)

{}



method isSubstring(sub: string, str: string) returns (res:bool)
	
    ensures  res <==> isSubstringPred(sub, str)
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.

{
    //TODO: insert your code here
    res := false;

    if (|str| < |sub|){
        return res;
    }
    assert(|str| >= |sub|);
    
    var i:= 0;
    var substr: string;
    
    while (i <= |str| && res == false)
        decreases |str| - i
        invariant 0 <= i < |str| + 2 && ((forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])) <==> res == false) 
    {
        substr := str[i..];
        res := isPrefix(sub, substr);
        i := i + 1; 
    }
    return res;
}





predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)

{

	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)

}



predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)

{

	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)

}



lemma commonKSubstringLemma(k:nat, str1:string, str2:string)

	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)

	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)

{}



method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)

	ensures found  <==> haveCommonKSubstringPred(k,str1,str2)
    ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.

{
    //TODO: insert your code here
    if (k > |str1| || k > |str2|){
        return false;
    }

    var i := 0;
    found := false;

    while(i <= |str1| - k && found == false)
        decreases |str1| - i 
        invariant 0 <= k <= |str1|
        invariant 0 <= i <= |str1| - k + 1  && (found == false <==> forall j, l :: 0 <= j < i && l == j + k ==> isNotSubstringPred(str1[j..l], str2))
    {
        var substr : string := str1[i..i+k];
        found := isSubstring(substr, str2);
        i := i + 1;
    }
    return found;
}



method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)

	requires (|str1| <= |str2|)

	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))

	ensures haveCommonKSubstringPred(len,str1,str2)

{

    //TODO: insert your code here
    assert(|str1| <= |str2|);
    assert(0 <= |str1|);
    assert(0 <= |str2|);

    len := |str1|;
    var res : bool := true;
    
    while(len > 0)
        decreases |str1| - (|str1| - len)
        invariant 0 <= len <= |str1| + 1
        invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2)
    {
        res := haveCommonKSubstring(len, str1, str2);
        if(res){
            break;
        }
       len := len - 1;
    }
    assert isPrefixPred(str1[|str1|..|str1|], str2[0..]);
    return len;
}