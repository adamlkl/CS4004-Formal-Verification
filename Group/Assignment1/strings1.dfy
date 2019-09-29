method isPrefix(pre: string, str: string) returns (res: bool){
  
  if(|pre| == 0){
    return true;
  }
  
  if (|pre| > |str|){
    return false;
  }
  
  var i: nat := 0;
  while(i < |pre|){
    if(pre[i] != str[i]){
      return false;
    }
    i := i + 1;
  }
  return true;
}

method isSubstring(sub: string, str: string) returns (res: bool){
  
  if(|sub| == 0){
    return true;
  }
 
  var i: nat := 0;
  var substr: string;
  var isPref : bool;
  while (i < |str| - |sub|){
    substr := str[i..];
    isPref := isPrefix(sub, substr);
    if(isPref){
      return true;
    }
    i := i + 1; 
  }
  return false;
}

method haveCommonKSubstring(k: nat, str1: string, str2:string) returns (res: bool){
  if (k == 0){
    return true;
  }
  
  if (k > |str1| || k > |str2|){
    return false;
  }
  
  var i: nat := 0;
  while(i < |str1| - k){
    var substr : string := str1[i..i+k-1];
    var isSubStr : bool := isSubstring(substr, str2);
    if(isSubStr){
      return true;
    }
    i := i + 1;
  }
  return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat){
  var short : string := str1;
  var long : string := str2;
  
  if(|str1| > |str2|){
    short := str2;
    long := str1;
  }
  
  var k : nat := 0;
  var haveCommonSubstring : bool := true;
  
  while(k < |short|){
    haveCommonSubstring := haveCommonKSubstring(k, short, long);
    if(!haveCommonSubstring){
      break;
    }
    k := k + 1;
  }
  return k;
}


