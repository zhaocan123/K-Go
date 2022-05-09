require "rs-semantics-common.k" 
module RS-SEMANTICS-ARRAY
    imports RS-SEMANTICS-COMMON

    // typed array declaration
    context let X:Id : [T:Type; HOLE:Exp] ;
    // 1. let a: [i32;2];
    rule <k> let X:Id : [T:Type;N:Int]; => . ... </k> 
         <env> Env => Env[X <- L] </env>
         <tempEnv> Env => Env[X <- L] </tempEnv>
         <typeEnv> ... .Map => L |-> [T;N] ... </typeEnv>
         <mutType> ... .Map => L |-> immutable ...  </mutType> 
         <tempMutType> ... .Map => L |-> immutable ...  </tempMutType> 
         //<store> Store =>  Store[L <- array(L +Int 1, N, T)] </store>
         <store> ...  .Map => L |-> array(L +Int 1, N, T)
                (L +Int 1)....(L +Int N) |-> undefined ... </store>
         <moved> ... .Map => L |-> 0 ... </moved>
         <borrow> ... .Map => L |-> undefined ... </borrow>
         <nextLoc> L => L +Int 1 +Int N  </nextLoc>
         requires N >=Int 0 

    // 2. let mut a: [i32;2];
    rule <k> let mut X:Id : [T:Type;N:Int]; => . ... </k> 
         <env> Env => Env[X <- L] </env>
         <tempEnv> Env => Env[X <- L] </tempEnv>
         <typeEnv> ... .Map => L |-> [T;N] ... </typeEnv>
         <mutType> ... .Map => L |-> mutable ... </mutType> 
         <tempMutType> ... .Map => L |-> mutable ... </tempMutType> 
         //<store> Store =>  Store[L <- array(L +Int 1, N, T)] </store>
         <store> ...  .Map => L |-> array(L +Int 1, N, T)
                (L +Int 1)....(L +Int N) |-> undefined ... </store>
         <moved> ... .Map => L |-> 0 ... </moved>
         <borrow> ... .Map => L |-> undefined ... </borrow>
         <nextLoc> L => L +Int 1 +Int N  </nextLoc>
         requires N >=Int 0 

    // 3. let a: [i32;2] = [9,10];
    // rule let X:Id : [T:Type; N:Int]  = V:ArrayValues ; => let X:Id : [T:Type; N:Int]; X=V;
    // 4. let mut a: [i32;2] = [9,10];
    // rule let mut X:Id : [T:Type; N:Int]  = V:ArrayValues ; => let mut X:Id : [T:Type; N:Int]; X=V;
    
    // implement X = [1,2,3,4];
    // 需要改assign的语义，按照Location赋值，而不是按照变量名赋值
    //@ syntax Stmts ::= "size" "(" ArrayValuesOnly ")"   [function] // size(1,2,3)

    //@ rule size(V:ArrayValuesOnly) => Int 
    //@ rule size(.ArrayValuesOnly) => 0
    //@ rule (size(V, Vs:ArrayValuesOnly)) =>  (size(Vs:ArrayValuesOnly)  +Int  1 )
    //rule <k> let X:Id = V:ArrayValues; => . </k>
    // assign
    // L the address of the first element 
    //@ rule <k> lambda(L,N,T)[i] = V:Val ; => . ... </k>
    //@      <store> ... .Map => (L +Int i) |-> (undefined => V) ... </store>
    //@      when getType(V) ==K T andBool i <= N - 1 andBool i >= 0 

    // x[0] = 10; either mutable or immutable
    rule <k> X[I:Int] = V:Val ; => . ... </k>
         <env> ... X |-> L ... </env>
         <typeEnv> ... L |-> [T:Type;N] ... </typeEnv>
         <store> ... (L +Int 1 +Int I) |-> (undefined => V) ... </store>
         when I <Int N andBool I >=Int 0 andBool getType(V) ==K T

    // mutable only
    rule <k> X[I:Int] = V:Val ; => . ... </k>
         <env> ... X |-> L ... </env>
         <mutType> ... L |-> mutable ... </mutType>
         <typeEnv> ... L |-> [T:Type;N] ... </typeEnv>
         <store> ... (L +Int 1 +Int I) |-> (_ => V) ... </store>
         when I <Int N andBool I >=Int 0 andBool getType(V) ==K T

    // evaluation
    //@ rule <k> X:Id[I:Int] => V </k>
    //@      <env> ... X |-> L ... </env>
    //@      <store> ... L |-> array(L +Int 1, N, T)
    //@               (L +Int 1 +Int I) |-> V:Val ... </store>
    //@      when I <Int N andBool I >=Int 0
    syntax Exp ::= lookup(Int)
    rule <k> lookup(L) => V ... </k> <store> ... L |-> V:Val ... </store>
    
    //@ rule <k> X:Id[Y:Id] = V:Val; => X[I] = V; ... </k>
    //@      <env> ... Y |-> L ... </env>
    //@      <store> ... L |-> I:Int ... </store>

    rule array(L,N,_)[I:Int] => lookup(L +Int I)
         when I <Int N andBool I >=Int 0   
         [structural, anywhere]
    // array length
    rule <k> X.len() => N ... </k>
         <env> ... X |-> L ... </env>
         <typeEnv> ... L |-> [T;N] ... </typeEnv>

    // array: initialized with values
    rule let X = [Vs:Vals]; => let X : [getTypeOfElements(Vs); getNumOfElements(Vs)]  =  [Vs];
    rule let mut X = [Vs:Vals]; => let mut X: [getTypeOfElements(Vs); getNumOfElements(Vs)] = [Vs];
    
    // Typed
    rule let X : [T:Type; N:Int] = [Vs:Vals]; => let X: [T;N]; X = [Vs];
    rule let mut X : [T:Type; N:Int] = [Vs:Vals]; => let mut X : [T;N]; X = [Vs];
    
    rule let X = [V:Val; N:Int]; => let X : [getType(V);N] = [V;N];
    rule let mut X = [V:Val; N:Int]; => let X : [getType(V);N] = [V;N];
    // array variable assignment

    // In this case, X is declared without initial value no matter it is mutable or immutable,
    // this assignment will be executed.
    syntax K ::= StoreArrayValues(Int, Vals) // Int is the location
    rule StoreArrayValues(L:Int, .Vals) => .
    rule StoreArrayValues(L:Int, V, Vs:Vals) => StoreValueAtLocation(L, V) ~> StoreArrayValues(L +Int 1, Vs)
    
    syntax K ::= StoreValueAtLocation(Int, Val)
    rule <k> StoreValueAtLocation(L:Int, V:Val) => . ... </k>
         <store> ... L |-> (_ => V) ... </store> 
    
    rule  <k> X:Id = [Vs:Vals]; => StoreArrayValues(L+Int 1, Vs) ... </k>
          <env> ... X |-> L ... </env>
    // let x:[isize;4] = [100;4];
    rule let X : [T:Type; N:Int] = [V:Val; N]; => let X : [T;N]; X = [V;N];
    syntax K ::= StoreValueAtLocationNTimes(Int, Val, Int)
    rule StoreValueAtLocationNTimes(L:Int,V:Val, 0) => .
    rule StoreValueAtLocationNTimes(L:Int, V:Val, N:Int) 
         => StoreValueAtLocation(L,V) ~> StoreValueAtLocationNTimes(L +Int 1,V, N -Int 1)
         when N >Int 0
    rule <k> X = [V;N]; => StoreValueAtLocationNTimes(L +Int 1, V, N) ... </k>
         <env> ... X |-> L ... </env>
    rule static X : [T:Type ; N:Int] = [V:Val ; N]; =>  let X : [T:Type ; N:Int] = [V:Val ; N];
    rule static X : [T:Type ; N:Int] = [Vs:Vals];   =>  let X : [T:Type ; N:Int] = [Vs];
    rule const X : [T:Type ; N:Int] = [Vs:Vals]; =>  let X : [T:Type ; N:Int] = [Vs];
    rule const X : [T:Type ; N:Int] = [V:Val ; N]; =>  let X : [T:Type ; N:Int] = [V:Val ; N];

   // rule const X  = [V:Val; N:Int]; => let X = [V;N];

endmodule