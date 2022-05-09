require "rs-semantics-common.k" 
module RS-SEMANTICS-ASSIGNMENT
  imports RS-SEMANTICS-COMMON
  // assign
  // 如果X是undefined的，也就是说只声明，没赋值
  // 1. 声明的时候，定义了类型
  rule <k> X:Id = V:Val; => . ...</k>
       <env>... X |-> L ...</env>
       <typeEnv> ... L |-> T ... </typeEnv>
       <store> ... L  |-> (undefined => V) ... </store> 
       when equalType(T, getType(V)) ==K true
       //when  T ==K getType(V)

  // 2. 声明的时候， 没有定义类型
  rule <k> X:Id = V:Val; => . ...</k>
       <env>... X |-> L ...</env>
       <typeEnv> ... L |-> (undefined => getType(V)) ... </typeEnv>
       <store> ... L |-> (undefined => V) ... </store> 

  // 如果X不是undefined的，也就是说，X已经有了一个值
  // 那么只有当X是mutable的时候，才能赋值成功
  rule <k> X:Id = V:Val; => . ...</k>
       <env>... X |-> L ...</env>
       <typeEnv> ... L |-> T ... </typeEnv>
       <mutType> ... L |-> mutable ... </mutType>
       <store> ... L |-> ( _ => V) ... </store> 
       when  equalType(T, getType(V)) ==K true 
  // reference
 
  // 1. mutable reference 
  // 1) Y must be mutable
  // 2) Y is not borrowed before
  
  // X is mutable or immutable, and not assigned and Y has not been borrowed before
  rule <k>  X:Id = &mut Y:Id; => . ... </k>
       <env> ... X |-> L ... </env> // exists X
       <tempEnv> ... Y |-> T ... </tempEnv>
       <ref> ...  L |-> ( _ => T) ... </ref> 
       <mutType> ... T |-> mutable ... </mutType> // Y is mutable
       <refType> ... L |-> ( undefined => mutableRef) ... </refType> // X has no refence history
       <borrow> ... T |-> (undefined => mutableBorrowed) ... </borrow> // Y has to be not borrowed before in this case
       <store> ... L |-> (undefined => mutRef(Y)) ... </store>
       //<store> ... .Map => L |-> mutRef(Y) ... </store>
       when L >Int T     


  // X is mutable and is already a mutable reference and Y has not been borrowed before
  rule <k>  X:Id = &mut Y:Id; => . ... </k>
       <env> ... X |-> L ... </env> // exists X
       <tempEnv> ... Y |-> T ... </tempEnv>
       <ref> ...  L |-> ( _ => T) ... </ref> // re-assign ref map
       <mutType> ... T |-> mutable ... </mutType> // Y is mutable
       <tempMutType> ... L |-> mutable ... </tempMutType> // X is mutable
       <refType> ... L |-> mutableRef ... </refType> // X is already mutable refence
       <borrow> ... T |-> (undefined => mutableBorrowed) ... </borrow> // Y is not borrowed before
       <store> ...  L |-> mutRef(_ => Y) ... </store>
       when L >Int T  

  // X is mutable and is already a immutable reference and Y has not been borrowed before
  rule <k>  X:Id = &mut Y:Id; => . ... </k>
       <env> ... X |-> L ... </env> // exists X
       <tempEnv> ... Y |-> T ... </tempEnv>
       <ref> ...  L |-> ( _ => T) ... </ref> // re-assign ref map
       <mutType> ... T |-> mutable ... </mutType> // Y is mutable
       <tempMutType> ... L |-> mutable ... </tempMutType> // X is mutable
       <refType> ... L |-> (immutableRef => mutableRef) ... </refType> // X is already mutable refence
       <borrow> ... T |-> (undefined => mutableBorrowed) ... </borrow> // Y is not borrowed before
       <store> ... L |-> (ref(_) => mutRef(Y)) ... </store>
       //<store> ...  L |-> mutRef(_ => Y) ... </store>
       when L >Int T


  // 2. immutable reference
  // 1) Y is not mutabled borrowed before
  // 2) X is immutable refence type
  // X is mutable or immutable and has not been assigned with a reference and Y has not been borrowed yet
  rule <k> X:Id = &(Y:Id); => . ... </k>
       <env> ... X |-> L ... </env>  
       <tempEnv> ... Y |-> T ... </tempEnv>
       <borrow> ... T |-> (undefined => immutableBorrowed) ... </borrow>
       <ref> ... L |-> (_ => T) ... </ref>
       //<ref> ... .Map => L |-> T ... </ref> // update X's reference location
       <refType> ... L |-> ( undefined => immutableRef) ... </refType>
       <store> ...  L |-> (undefined => ref(Y)) ... </store>
       when L >Int T 
  // X is mutable or immutable and not assigned yet. Y has already been immutablely borrowed
  rule <k> X:Id = &(Y:Id); => . ... </k>
       <env> ... X |-> L ... </env>  
       <tempEnv> ... Y |-> T ... </tempEnv>
       <borrow> ... T |-> immutableBorrowed ... </borrow>
       <ref> ... L |-> (_ => T) ... </ref>
       //<ref> ... .Map => L |-> T ... </ref> // update X's reference location
       <refType> ... L |-> ( undefined => immutableRef) ... </refType>
       <store> ...  L |-> (undefined => ref(Y)) ... </store>
       when L >Int T 
  // 如果X是可变的话，可以对X进行mutable ref和immutable两种引用的赋值，都没有问题。但必须是引用
  // X之前引用过其它变量（对X重新赋值）
  // 1 - (这里的Y还没有被引用(不可变引用)过)
  // X is mutable and has already had a reference. Y is not borrowed yet.
  rule <k> X:Id = &(Y:Id); => . ... </k>
       <env> ... X |-> L ... </env>  
       <tempEnv> ... Y |-> T ... </tempEnv>
       <mutType> ... L |-> mutable ... </mutType> // X is mutable
       <borrow> ... T |-> (undefined => immutableBorrowed) ... </borrow>
       <ref> ...  L |-> (_ => T) ... </ref> // update X's reference location
       <refType> ... L |-> immutableRef ... </refType>
       <store> ...  L |-> ref(_ => Y) ... </store>
       when L >Int T

  // X is already a mutable reference. Y is not borrowed yet.      
  rule <k> X:Id = &(Y:Id); => . ... </k>
       <env> ... X |-> L ... </env>  
       <tempEnv> ... Y |-> T ... </tempEnv>
       <mutType> ... L |-> mutable ... </mutType> // X is mutable
       <borrow> ... T |-> (undefined => immutableBorrowed) ... </borrow>
       <ref> ...  L |-> (_ => T) ... </ref> // update X's reference location
       <refType> ... L |-> (mutableRef => immutableRef) ... </refType>
       <store> ...  L |-> ref( _ => Y) ... </store>
       when L >Int T 
  
  // X is a immutable reference. Y is immutablely borrowed.
  rule <k> X:Id = &(Y:Id); => . ... </k>
       <env> ... X |-> L ... </env>  
       <tempEnv> ... Y |-> T ... </tempEnv>
       <mutType> ... L |-> mutable ... </mutType> // X is mutable
       <borrow> ... T |-> immutableBorrowed ... </borrow>
       <ref> ...  L |-> (_ => T) ... </ref> // update X's reference location
       <refType> ... L |-> immutableRef ... </refType>
       <store> ...  L |-> ref( _ => Y) ... </store>
       when L >Int T   
 
  // X is a mutable reference. Y is immutablely borrowed.
  rule <k> X:Id = &(Y:Id); => . ... </k>
       <env> ... X |-> L ... </env>  
       <tempEnv> ... Y |-> T ... </tempEnv>
       <mutType> ... L |-> mutable ... </mutType> // X is mutable
       <borrow> ... T |-> immutableBorrowed ... </borrow>
       <ref> ...  L |-> (_ => T) ... </ref> // update X's reference location
       <refType> ... L |-> (mutableRef => immutableRef) ... </refType>
       <store> ...  L |-> (mutRef(_) => ref(Y)) ... </store>
       when L >Int T 
  // not work. don't know why
  //@ rule <k> X:Id = ref(L:Int); => X = &Y; ... </k>
  //@      <env> ... Y |-> L ... </env>
  rule <k> X:Id = ref(Y:Id); => X = &Y; ... </k>
  rule <k> let X:Id = ref(Y:Id); =>let X = &Y; ... </k>
  rule <k> let mut X:Id = ref(Y:Id); => let X = &Y; ... </k>
       //<env> ... Y |-> L ... </env>

  rule <k> X:Id = &Y:Id[N:Int]; => . ... </k>
       <env> ... X |-> L ... </env>
       <tempEnv> ... Y |-> T ... </tempEnv>
       //<borrow> ... T |-> (undefined => immutableBorrowed) ... </borrow>
       <ref> ... L |-> (undefined => T +Int 1 +Int N) ... </ref>
       //<ref> ... .Map => L |-> T +Int 1 +Int N ... </ref> // update X's reference location
       //@ <refType> ... L |-> ( undefined => immutableRef) ... </refType>
       when L >Int (T +Int 1 +Int N) andBool N >=Int 0

  // derefence  
  rule <k> *X = V:Val ; => . ... </k>
       <env> ... X |-> L ... </env>
       <ref> ... L |-> T ... </ref>
       //<borrow> ... T |-> mutableBorrowed ... </borrow> // *X must be mutable
       <refType> ... L |-> mutableRef ... </refType>
       <store> ... T |-> ( _ => V) ... </store>

  rule <k> X:Id = &V:Val; => . ... </k>
       <env> ...  X |-> L0 ... </env>
       <mutType> ... L0 |-> immutable ... </mutType>
       <store> Store => Store[L <- V] </store>
       <ref> ...  L0 |-> (undefined => L )  ... </ref>
       <refType> ... L0 |-> (undefined => immutableRef) ... </refType>
       <moved> ...  L0 |-> 0 ... </moved>
       <nextLoc> L  => L +Int 1 </nextLoc>

  rule X:Id = Y:Id = V:Val; =>  X = (); Y = V; 
  rule X:Id = Y:Id += V:Val; => X = (); Y += V; 
  rule X:Id = Y:Id -= V:Val; => X = (); Y -= V;
  rule X:Id = Y:Id /= V:Val; => X = (); Y /= V; 
  rule X:Id = Y:Id *= V:Val; => X = (); Y *= V;  
endmodule 