require "rs-semantics-common.k" 
module  RS-SEMANTICS-FUNCTION
  imports RS-SEMANTICS-COMMON 


  rule pub fn F(TypedIds) -> T { S:Stmts }  => fn F(TypedIds) -> T { S } 
  // 1. function with return type 
  rule <k> fn F(TypedIds) -> T { S:Stmts } => . ... </k>
       <env> Env => Env[F <- L] </env>
       <tempEnv> TempEnv => TempEnv[F <- L] </tempEnv>
       <mutType> ... .Map => L |-> immutable ... </mutType>
       <tempMutType> ... .Map => L |-> immutable ... </tempMutType>
       <store> Store => Store[L <- lambda(TypedIds, S, T)] </store>
       <nextLoc> L => L +Int 1 </nextLoc>

  // with return type 
  syntax KItem ::=  (Map, Map, Map, K, Type)
  // 不知道有没有办法检测出S里面有没有return语句
  // 额，如果S里面有return 语句的话，后面的return ()不会被执行
  //syntax Ints ::= List{Int,","}
  // the parameters are all simple values

  // 普通函数调用
  rule <k> lambda(TypedIds, S:Stmts, T)(Vs:Parameters) ~> K => mkDecls(TypedIds,Vs) S return (); </k>
       //<control>
         <fstack> .List => ListItem((Env, BEnv, REnv, K, T)) ...</fstack>
       //</control>
       <env> Env </env>
       <borrow> BEnv </borrow>
       <ref> REnv </ref>
  
  // 包含引用的成员函数调用
  // lambda ( ( self : & Point ) , .StructValues , println! ( "{}" , ( self . x * 100 ) , .StructValues ) ; , () ) ( ( & p ) , .StructValues )
  // 成员函数
  rule <k> lambda(TypedIds, S:Stmts, T)(V:Id, Vs:Parameters) ~> K => mkDeclsForMethods(TypedIds, V, Vs) S return (); </k>
       //<control>
         <fstack> .List => ListItem((Env, BEnv, REnv, K, T)) ...</fstack>
       //</control>
       <env> Env </env>
       <borrow> BEnv </borrow>
       <ref> REnv </ref>
  rule <k> lambda(TypedIds, S:Stmts, T)(&V:Id, Vs:Parameters) ~> K => mkDeclsForMethods(TypedIds, & V, Vs) S return (); </k>
       //<control>
         <fstack> .List => ListItem((Env, BEnv, REnv, K, T)) ...</fstack>
       //</control>
       <env> Env </env>
       <borrow> BEnv </borrow>
       <ref> REnv </ref>
  rule <k> lambda(TypedIds, S:Stmts, T)(&mut V:Id, Vs:Parameters) ~> K => mkDeclsForMethods(TypedIds, &mut V, Vs) S return (); </k>
       //<control>
         <fstack> .List => ListItem((Env, BEnv, REnv, K, T)) ...</fstack>
       //</control>
       <env> Env </env>
       <borrow> BEnv </borrow>
       <ref> REnv </ref> 

  // return V; 舍弃掉return后面的语句
  //context return(HOLE:Exp); 
  rule <k> return(V:Val); ~> _ => V ~> K </k>
       //<control>
         <fstack> ListItem((Env, BEnv, REnv, K, T)) => .List ...</fstack>
       //</control>
       <env> _ => Env </env>
       <tempEnv> _ => Env </tempEnv>
       <borrow> _ => BEnv </borrow>
       <ref> _ => REnv </ref>
       when equalType(T,getType(V)) ==K true
       //when T ==K getType(V)

  rule <k> return(V:ComplexVal); ~> _ => V ~> K </k>
       //<control>
         <fstack> ListItem((Env, BEnv, REnv, K, T)) => .List ...</fstack>
       //</control>
       <env> _ => Env </env>
       <tempEnv> _ => Env </tempEnv>
       <borrow> _ => BEnv </borrow>
       <ref> _ => REnv </ref>
       //when equalType(T,getType(V)) ==K true


  syntax Stmts ::= mkDecls(TypedIds, Parameters)  [function]
  
  rule mkDecls((X : T , Xs:TypedIds), (V:Parameter, Vs:Parameters)) => let X : T = V; mkDecls(Xs,Vs)
  rule mkDecls(.TypedIds, .Parameters) => {}


  // for struct methods   impl实现的method 
  // case one: P will be moved 
  syntax Stmts ::= mkDeclsForMethods(TypedIds, Id, Parameters)   [function]
  rule mkDeclsForMethods((X : T:Id, Xs:TypedIds), P:Id, Vs:Parameters)  // P is a struct instance 
       => let X : T = P; mkDecls(Xs, Vs)
  // case two : immutable reference
  // T is not a trait , T is a struct 
  // P 必须是T类型的结构体变量
  // example:  mkDecls ( ( self : & Point ) , .StructValues , ( & p ) , .StructValues )
  syntax Stmts ::= mkDeclsForMethods(TypedIds, RefExp, Parameters)   [function]
  rule <k> mkDeclsForMethods((X : & T:Id, Xs:TypedIds), & P:Id, Vs:Parameters)  // P is a struct instance 
       => let X = &P; mkDecls(Xs, Vs) ... </k>
       //@ <env> ... T |-> L ... </env> // T is a struct. If T is a trait, there is no such mapping
       //@ <tempEnv> ... P |-> L0 ... </tempEnv>
       //@ <typeEnv> ... L0 |-> T ... </typeEnv> 
  // case three : mutable reference T分为struct和trait两种 TODO 
  rule mkDeclsForMethods((X : &mut T:Id, Xs:TypedIds), &mut P:Id, Vs:Parameters)  // P is a struct instance 
       => let X = &mut P; mkDecls(Xs, Vs)

  // case four : & T where T is a trait
  // P是一个结构体变量，必须实现了trait T
  rule <k> mkDeclsForMethods((X : & T:Id, Xs:TypedIds), & P:Id, Vs:Parameters)  // P is a struct instance 
       => let X = &P; mkDecls(Xs, Vs)... </k>
       <env> ... P |-> L0 ... </env>
       <typeEnv> ... L0 |-> S:Id ... </typeEnv>
       <interfaces> ... T |-> M:TraitMethods ... </interfaces>
       <traitImplemented> ... S |-> traits(L:List) ... </traitImplemented>
       when T in Setify(L) 
       
  // make sure that $LF \subseteq \bigcap LFs$
  // Lifetimes : 'a, 'b : 'a , 'c: 'b
  // Lifetimes如果等于 'a, 'b : 'a 则应该直接替换为 'a, 'a
  syntax K ::= CheckLifetimes(Lifetime, List)
  
  // First case : CheckLifetimes('a, ('a))
  rule CheckLifetimes(LF0:Lifetime, ListItem(LF1:Lifetime)) => . when LF0 ==K LF1 
  // Second case : CheckLifetimes('a, 'a, 'b : 'a) 
  rule CheckLifetimes(LF0:Lifetime, ListItem(LF1:Lifetime) ListItem(LF2:Lifetime : LF3:Lifetime))
       => CheckLifetimes(LF0, ListItem(LF1)) when LF1 ==K LF3 
  
  syntax List ::= toList( Lifetimes )    [function]
  rule toList(.Lifetimes) => .List 
  rule toList(LF:Lifetime) => ListItem(LF)
  rule toList(LF:Lifetime, LFs:Lifetimes) => ListItem(LF) toList(LFs)
  
  // lookup Lifetime in a List and return the index
  syntax Int ::= lookup(Lifetime, List)   [function]
  rule lookup(LF:Lifetime, ListItem(LF1:Lifetime) Left:List) => 0 when LF ==K LF1 
  rule lookup(LF:Lifetime, ListItem(LF1:Lifetime) Left:List) => 1 +Int lookup(LF, Left) when LF =/=K LF1 
  // get left List 
  // 0..2 4..end  3-th is removed
  syntax List ::= getLeft(List, Int)   [function]
  rule getLeft(ListItem(_) L, N:Int) => L when N ==Int 0
  rule getLeft(L:List, N:Int) 
       => getRange(L,0,N -Int 1) getRange(L, N +Int 1, getNumOfElementsInList(L) -Int 1) 
       when N >Int 0 andBool N <Int getNumOfElementsInList(L)
  

  // remove Lifetime in Lifetimes 
  syntax List ::= remove(Lifetime, List)  [function] 
  rule remove(LF:Lifetime, LFs:List) => getLeft(LFs, lookup(LF,LFs))
  //rule remove(LF:Lifetime, ListItem(LF) Left:List) => Left 

  // function with lifetime annotations
  rule fn X:Id<LFs:Lifetimes>(TypedIds) -> & LF:Lifetime Type {E:Exp}
       => fn X:Id<LFs:Lifetimes>(TypedIds) -> & LF:Lifetime Type {return E;}
  rule fn X:Id<LFs:Lifetimes>(TypedIds) -> & LF:Lifetime Type {S:Stmts}
       => CheckLifetimes(LF, toList(LFs)) ~> fn X(TypedIds) -> & Type {S}
  
  rule fn X:Id<LFs:Lifetimes>(TypedIds) -> & LF:Lifetime Type where LF1:Lifetime : 'static {E:Exp}
       => fn X:Id<LFs:Lifetimes>(TypedIds) -> & LF:Lifetime Type where LF1:Lifetime : 'static {return E;}
  rule fn X:Id<LFs:Lifetimes>(TypedIds) -> & LF:Lifetime Type where LF1:Lifetime : 'static {S:Stmts}
       => CheckLifetimes(LF, remove(LF1, toList(LFs))) ~> fn X(TypedIds) -> & Type {S}  


  rule pub fn F:Id(TypedIds) { S:Stmts }=> fn F:Id(TypedIds) { S } 
  // 2. without return type 
  rule fn F:Id(TypedIds) { S:Stmts }  => fn F(TypedIds) -> () { S } 

  rule return; => return ();   [macro]
  // function may have void block
  rule fn F(TypedIds)  { }  => fn F(TypedIds) -> () { return ; }
  rule pub fn F(TypedIds)  { }  => fn F(TypedIds) -> ()  { return ; } 
  // expression as return
  // 1: pub
  rule pub fn F(TypedIds) -> T { S:Stmts V:Exp} => fn F(TypedIds) -> T { S return V;}
  rule pub fn F(TypedIds) -> T { V:Exp} => fn F(TypedIds) -> T { return V;}
  rule pub fn F(TypedIds) { S:Stmts V:Exp} => fn F(TypedIds) -> () { S return ; } 
  rule pub fn F(TypedIds) { V:Exp } => fn F(TypedIds) -> () { return V;}
  // 2. no pub
  rule fn F(TypedIds) -> T { S:Stmts V:Exp} => fn F(TypedIds) -> T { S return V;}
  rule fn F(TypedIds) -> T { V:Exp } => fn F(TypedIds) -> T { return V;}
  rule fn F(TypedIds) { V:Exp } => fn F(TypedIds) -> () { return V;}
  rule fn F(TypedIds) { S:Stmts V:Exp} => fn F(TypedIds) -> () { S return V;}
  
  // for a very simple closure
  rule let Y:Id = |TypedIds| -> T {S:Stmts} ; => fn Y(TypedIds) -> T {S}
  rule let Y:Id = |TypedIds| -> T {V:Exp} ; => fn Y(TypedIds) -> T {V}
  rule let mut Y:Id = |TypedIds| -> T {S:Stmts} ; => fn Y(TypedIds) -> T {S}
  rule let mut Y:Id = |TypedIds| -> T {V:Exp} ; => fn Y(TypedIds) -> T {V}

  // ! means return nothing
  rule fn F(TypedIds) -> ! { S:Stmts } => fn F(TypedIds) { S:Stmts }
  rule pub fn F(TypedIds) -> ! { S:Stmts } => fn F(TypedIds) { S:Stmts }
  rule let X:Id = {|Y:Id| E:Exp}; => fn X(Y:i32) -> i32 {return E;}
  rule let X:Id = |.Ids| {S:Stmts} ; => fn X(.TypedIds) {S}
  rule let X:Id = |.Ids| { } ; => fn X(.TypedIds) { }
  rule let mut X:Id = |.Ids| { } ; => fn X(.TypedIds) { }
  rule let X:Id = |Y:Id| E:Exp ; => fn X(Y:i32) -> i32 {return E;}
  rule const fn F(TypedIds) -> T {V:Exp} => fn F(TypedIds) -> T {return V;} 
endmodule 