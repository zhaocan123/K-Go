require "rs-semantics-common.k" 
module  RS-SEMANTICS-STRUCT
  imports RS-SEMANTICS-COMMON 

  rule <k> struct X:Id {TypedIds} => . ... </k>
       <env> ... .Map => X |-> L ... </env>
       <tempEnv> ... .Map => X |-> L ... </tempEnv>
       <store> ... .Map => L |-> structFields(TypedIds) ... </store>
       <nextLoc> L => L +Int 1 </nextLoc>
       <traitImplemented> ... .Map => X |-> traits(.List) ... </traitImplemented>
  // empty fields
  rule pub struct X; => struct X;
  rule <k> struct X:Id ; => . ... </k>
       <env> ... .Map => X |-> L ... </env>
       <tempEnv> ... .Map => X |-> L ... </tempEnv>
       <store> ... .Map => L |-> structFields(.TypedIds) ... </store>
       <nextLoc> L => L +Int 1 </nextLoc>

  rule let X:Id = Y:Id { SVs }; => let X; X = Y { SVs }; // SVs是StructValues类型
  rule let mut X:Id = Y:Id { SVs }; => let mut X; X = Y { SVs }; // SVs是StructValues类型
  rule let X:Id : Y:Id = Y:Id { SVs }; => let X; X = Y { SVs }; // SVs是StructValues类型
  rule let mut X:Id : Y:Id = Y:Id { SVs }; => let mut X; X = Y { SVs }; // SVs是StructValues类型

  syntax Stmts ::= "structInit" "(" ComplexVal "," Id "," StructValues ")" ";"
  // Initial assign 
  rule <k> X:Id = Y:Id { SVs } ; => structInit(structFields(TIds), X, SVs); ... </k> // TIds是TypedIds类型
       <env> ... Y |-> L ... </env>
       <tempEnv> ... X |-> LX ... </tempEnv>
       <typeEnv> ... LX |-> (undefined => Y) ... </typeEnv> // X's type ? 
       <store>... L |-> structFields(TIds) LX |-> (undefined => struct(X, Y)) ... </store> 
  //@ // Initial assign : X is mutable 
  //@ rule <k> X:Id = Y:Id { SVs } ; => structInit(structFields(TIds), X, SVs); ... </k> // TIds是TypedIds类型
  //@      <env> ... Y |-> L ... </env>
  //@      <tempEnv> ... X |-> L0 ... </tempEnv>
  //@      <mutType> ... L0 |-> mutable ... </mutType>
  //@      <typeEnv> ... L0 |-> (undefined => Y) ... </typeEnv> // X's type ? 
  //@      <store>... L |-> structFields(TIds)  L0 |-> (undefined => struct(X, Y)) ... </store> 
  // re-assgin
  rule <k> X:Id = Y:Id { SVs } ; => structInitAgain(structFields(TIds),X,SVs); ... </k> // TIds是TypedIds类型
       <env> ... Y |-> L ... </env>
       <tempEnv> ... X |-> L0 ... </tempEnv>
       <mutType> ... L0 |-> mutable ... </mutType>
       <typeEnv> ... L0 |->  Y ... </typeEnv> // X's type ? 
       <moved> ...  L0 |-> 0 ... </moved> // X is alive
       <store>... L |-> structFields(TIds)  ... </store> 

  rule <k> X:Id = Y:Id { SVs } ; => structInitAgain(structFields(TIds),X,SVs); ... </k> // TIds是TypedIds类型
       <env> ... Y |-> L ... </env>
       <tempEnv> ... X |-> L0 ... </tempEnv>
       <mutType> ... L0 |-> mutable ... </mutType>
       <typeEnv> ... L0 |->  Y ... </typeEnv> // X's type ? 
       <moved> ...  L0 |-> (1 => 0) ... </moved> // X is alive again
       <store>... L |-> structFields(TIds)  ... </store> 
    
  
  rule <k> structInit(structFields(.TypedIds), X:Id, .StructValues); => . ... </k>
  rule <k> structInit(structFields(((Y:Id) : (T:Type), LeftIds)), X, ((Y:Id) : (V:Val), LeftSVs)); 
         => structInit(structFields(LeftIds), X, LeftSVs); ... </k>
       <env> ... .Map => X.Y |-> L ... </env>
       <tempEnv> ... .Map => X.Y |-> L ... </tempEnv>
       <store> ... .Map => L |-> V ... </store>
       <nextLoc> L => L +Int 1 </nextLoc>
  
  // meet reference 
  rule <k> structInit(structFields(((Y:Id) : (T:Type), LeftIds)), X, ((Y:Id) : (& Z:Id), LeftSVs)); 
           => let X.Y = ref(Z); ~> structInit(structFields(LeftIds), X, LeftSVs); ... </k>
       //@ <env> ... .Map => X.Y |-> L ... </env>
       //@ <tempEnv> ... .Map => X.Y |-> L ... </tempEnv>
       //@ <ref> ... .Map => L |-> 
       //@ <store> ... .Map => L |-> ref(Z) ... </store>
       //@ <nextLoc> L => L +Int 1 </nextLoc>

  syntax Stmts ::= "structInitAgain" "(" ComplexVal "," Id "," StructValues ")" ";"
  rule <k> structInitAgain(structFields(.TypedIds), X:Id, .StructValues); => . ... </k>
  rule <k> structInitAgain(structFields(((Y:Id) : (T:Type), LeftIds)), X, ((Y:Id) : (V:Val), LeftSVs)); 
         => structInitAgain(structFields(LeftIds), X, LeftSVs); ... </k>
       <env> ... X.Y |-> L ... </env>
       <store> ...  L |-> (_ => V) ... </store>

  // evaluation
  rule <k> X:Id . Y:Id => V ... </k>
       <env> ... X.Y |-> L:Int  ... </env>
       <tempEnv> ... X |-> LX:Int ... </tempEnv>
       <store> ... L |-> V ... </store>
       <moved> ... LX |-> 0 ... </moved> // X is not moved
  // assignment of struct
  rule <k> X:Id . Y:Id = V:Val; => . ... </k>
       <tempEnv> ... X |-> LX ... </tempEnv>
       <mutType> ... LX |-> mutable ... </mutType>
       <env> ... X.Y |-> L ... </env>
       <store> ... L |-> (_ => V) </store>
       <moved> ... LX |-> 0 ... </moved> // X is not moved
  // assignment of a whole struct instance
  // Y is a struct instance 
  // case one: X is mutable 
  syntax Stmts ::= "AssignTypeAndValue" "(" Id "," Id ")" ";"
  rule <k> AssignTypeAndValue(X:Id, S:Id); => . ... </k>
       <env> ... X |-> L ... </env>
       <typeEnv> ... L |-> (undefined => S) ... </typeEnv>
       <store> ... L |-> (undefined => struct(X,S)) ... </store>
  // let mut X = Y; => let mut X = struct(Y,S);
  rule <k> let mut X:Id = struct(Y:Id,S:Id); => let mut X; AssignTypeAndValue(X,S); CopyStructFields(X,Y,TIds); MoveVariable(Y); ... </k>
       //<env> ... Y |-> L0:Int ... </env>
       <env> ... S |-> L ... </env> 
       <store> ... L |-> structFields(TIds)  ... </store> // 
       //<typeEnv> ... L0 |-> S:Id ... </typeEnv> // Y is a struct instance 
  
  syntax Stmts ::= "CopyStructFields" "(" Id "," Id "," TypedIds ")" ";"
  rule  CopyStructFields(X,Y, .TypedIds); => .
  rule  CopyStructFields(X,Y, (((Z:Id) : (T:Type)), Vs)); 
       => let X.Z = Y.Z; CopyStructFields(X,Y,Vs); 
  
  rule <k> let X:Id . Y:Id = V:Val; => . ...</k>
       <env> ... .Map => X.Y |-> L ... </env>
       <tempEnv> ... .Map => X.Y |-> L ... </tempEnv>
       <store> ... .Map => L |-> V ... </store>
       <nextLoc> L => L +Int 1 </nextLoc>

  // a variable is moved
  syntax Stmts ::= "MoveVariable" "(" Id ")" ";"
  rule <k> MoveVariable(X); => . ...</k>
       <env> ... X |-> L ... </env>
       <moved> ... L |-> (0 => 1) ... </moved>
  
  // case two : X is immutable 
  rule <k> let X:Id  = struct(Y:Id,S:Id) ; 
       => let X; AssignTypeAndValue(X, S); CopyStructFields(X,Y,TIds); MoveVariable(Y); ... </k>
       <env> ... S |-> L ... </env>
       <store> ... L |-> structFields(TIds) ... </store>
  // typed declaration
  rule let mut X:Id : S:Id = struct(Y:Id, S:Id); => let mut X = struct(Y,S);
  rule let X:Id : S:Id = struct(Y:Id, S:Id); => let X = struct(Y,S); 

  // assignment
  // X = Y; => X = struct(Y,S);
  rule <k> X:Id = struct(Y:Id, S:Id); => CopyStructFields2(X,Y,TIds); MoveVariable(Y); ... </k>
       <env> ... S |-> L ... </env>
       <tempEnv> ... X |-> L0 ... </tempEnv>
       <mutType> ... L0 |-> mutable ... </mutType>  // x is mutable
       <typeEnv> ... L0 |-> S ... </typeEnv>
       <moved> ... L0 |-> 0 ... </moved> // X is alive currently.
       <store> ... L |-> structFields(TIds) ... </store>

  
  // X = Y; but X is moved 
  rule <k> X:Id = struct(Y:Id, S:Id); => CopyStructFields2(X,Y,TIds); MoveVariable(Y); ... </k>
       <env> ... S |-> L ... </env>
       <tempEnv> ... X |-> L0 ... </tempEnv>
       <mutType> ... L0 |-> mutable ... </mutType> 
       <typeEnv> ... L0 |-> S ... </typeEnv>
       <moved> ... L0 |-> (1 => 0) ... </moved> // X becomes alive now.
       <store> ... L |-> structFields(TIds) ... </store>

  
  syntax Stmts ::= "CopyStructFields2" "(" Id "," Id "," TypedIds ")" ";"
  rule  CopyStructFields2(X,Y, .TypedIds); => .
  rule  CopyStructFields2(X,Y, (((Z:Id) : (T:Type)), Vs)); 
       => X.Z = Y.Z; CopyStructFields2(X,Y,Vs); // It is not "let X.Z = Y.Z;"
  

  // comma at ending
  rule struct X:Id {Y:Id : T:Type , } => struct X {Y : T}
  rule struct X:Id {Z:Id : T1:Type , Y:Id : T2:Type , } => struct X {Z : T1, Y : T2}
  rule pub struct X:Id {pub Z:Id : T1:Type , pub Y:Id : T2:Type , } => struct X {Z : T1, Y : T2}
  //rule struct X:Id {TypedIds , Y:Id : T:Type ,} => struct X {TypedIds, Y : T}
  rule struct X:Id <LFs:Lifetimes> {Y:Id : T:Type, } => struct X {Y : T}
  rule struct X:Id <LFs:Lifetimes> {TIds:TypedIds} => struct X {TIds}

  // 1. associated methods 
  rule <k> impl S:Id {fn X:Id (TypedIds) Body F:ImplFunctions } 
       => fn S::X (TypedIds) Body ~> impl S {F} ... </k>
  rule <k> impl S:Id {fn X:Id (TypedIds) -> T:Type Body F:ImplFunctions } 
       => fn S::X (TypedIds) -> T Body ~> impl S {F} ... </k>


  // function definition should be updated
  // 2. normal methods
  // 1) self : without return type
  rule <k> impl S:Id {fn X:Id (self, TypedIds) Body F:ImplFunctions}
       => fn S::X (self : S, TypedIds) Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> take ... </mType>
  rule <k> impl S:Id {fn X:Id (self) Body F:ImplFunctions}
       => fn S::X (self : S) Body ~> impl S {F} ... </k>
        <mType> ... .Map => S::X |-> take ...  </mType>

  // 2) self : with return type 
  rule <k> impl S:Id {fn X:Id (self, TypedIds) -> T:Type Body F:ImplFunctions } 
       => fn S::X (self : S, TypedIds) -> T Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> take ... </mType>
  rule <k> impl S:Id {fn X:Id (self) -> T:Type Body F:ImplFunctions } 
       => fn S::X (self : S) -> T Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> take ... </mType>
  // for &self
  // 1) &self : without return type
  rule <k> impl S:Id {fn X:Id (&self, TypedIds) Body F:ImplFunctions}
       => fn S::X (self : &S, TypedIds) Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> immutableRef ... </mType>

  rule <k> impl S:Id {fn X:Id (&self) Body F:ImplFunctions}
       => fn S::X (self : &S) Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> immutableRef ... </mType>
  // 2) &self : with return type  
  rule <k> impl S:Id {fn X:Id (&self, TypedIds) -> T:Type Body F:ImplFunctions } 
       => fn S::X (self : &S, TypedIds) -> T Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> immutableRef ... </mType>
  rule <k> impl S:Id {fn X:Id (&self) -> T:Type Body F:ImplFunctions } 
       => fn S::X (self : &S) -> T Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> immutableRef ... </mType>
  // for &mut self
  // 1) &self : without return type
  rule <k> impl S:Id {fn X:Id (&mut self, TypedIds) Body F:ImplFunctions}
       => fn S::X (self : &mut S, TypedIds) Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> mutableRef ... </mType>

  rule <k> impl S:Id {fn X:Id (&mut self) Body F:ImplFunctions}
       => fn S::X (self : &mut S) Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> mutableRef ... </mType>
  // 2) &self : with return type  
  rule <k> impl S:Id {fn X:Id (&mut self, TypedIds) -> T:Type Body F:ImplFunctions } 
       => fn S::X (self : &mut S, TypedIds) -> T Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> mutableRef ... </mType>

  rule <k> impl S:Id {fn X:Id (&mut self) -> T:Type Body F:ImplFunctions } 
       => fn S::X (self : &mut S) -> T Body ~> impl S {F} ... </k>
       <mType> ... .Map => S::X |-> mutableRef ... </mType>

  // updated semantics for function with self, &self, &mut self
  // find an easy way ...

  rule <k>  impl S:Id {.ImplFunctions} => . ... </k>
  rule <k>  impl S:Id { } => . ... </k>
  
  // impl with trait
  // TO BE FIXED : should check the method type with trait
  syntax K ::= CheckSignatures(TraitMethods, ImplFunctions) [function]
  rule CheckSignatures((T:TraitFunType  Ts:TraitMethods),(F:Function  Fs:ImplFunctions))
       => CheckSignature(T, F) ~> CheckSignatures(Ts, Fs)
  rule CheckSignatures(.TraitMethods, .ImplFunctions) => . 
  // TODO 
  syntax K ::= CheckSignature(TraitFunType, Function)  [function]
  rule CheckSignature(T:TraitFunType, F:Function)  => . 
  //@ rule CheckSignature(fn X:Id(Ts:TraitFunParaTypes) -> T:Type; , fn X(Ts) -> T Body) => .
  //@ rule CheckSignature(fn X:Id(Ts:TraitFunParaTypes); , fn X(Ts) Body) => .  
  
  rule <k> impl X:Id for S:Id {F:ImplFunctions} => CheckSignatures(M,F) ~> impl S {F} ... </k>
       <interfaces> ... X |-> M:TraitMethods ... </interfaces> 
       <traitImplemented>... S |-> traits(L:List => AddTrait(L,X)) ... </traitImplemented>
       <father> ... X |-> undefined ... </father>
  // for supertraits
  rule <k> impl X:Id for S:Id {F:ImplFunctions} => CheckSignatures(M,F) ~> impl S {F} ... </k>
       <interfaces> ... X |-> M:TraitMethods ... </interfaces> 
       <traitImplemented>... S |-> traits(L:List => AddTrait(L,X)) ... </traitImplemented>
       <father> ... X |-> Y:Id ... </father>
       when Y in Setify(L)  // S is required to impl Y already
  

  syntax List ::= "AddTrait" "(" List "," Id ")"  [function]
  rule AddTrait(L:List, V:Id) => L ListItem(V)
    

  //rule X:Id . F:Id(Vs:Parameters) => .   [macro]
  // method call
  // need to know the first paremeter is self, &self or &mut self
  //@ syntax K ::= findMethod(Id, Id)
  
  //@ syntax K ::= exist(Id)   [function]
  //@ rule <k> exist(X:Id) => . ... </k>
  //@      <env> ...  X |-> L ... </env>
  
  // let p =&q; p.x
  rule <k> X:Id . F:Id => Y.F ... </k>
       <env> ... X |-> L ... </env>
       <store> ... L |-> ref(Y:Id) ... </store>
       <moved> ... L |-> 0 ... </moved>
  rule <k> X:Id . F:Id => Y.F ... </k>
       <env> ... X |-> L ... </env>
       <store> ... L |-> mutRef(Y:Id) ... </store>
       <moved> ... L |-> 0 ... </moved>
  rule <k> X:Id . F:Id = V:Val; => Y.F = V;... </k>
       <env> ... X |-> L ... </env>
       <store> ... L |-> mutRef(Y:Id) ... </store>
       <moved> ... L |-> 0 ... </moved>
  // take ownership
  rule <k> X:Id . F:Id => findMethod(S::F, X)  ... </k> 
       <env> ... X |-> L ... </env> 
       <typeEnv> ... L |-> S:Id ... </typeEnv>
       <moved> ... L |-> 0 ... </moved>
       <mType> ...  S::F |-> take ... </mType> // X is already moved in mkDecls()
  // 上面规则中的X传入到F中，在mkDecl中会把X赋值给V，X就会被move
  rule findMethod(F:Id, V:Id)(Vs:Parameters) => F(V, Vs)

  // immutable ref
  rule <k> X:Id . F:Id => findMethod(S::F, ref(X))  ... </k> 
       <env> ... X |-> L ... </env> 
       <typeEnv> ... L |-> S:Id ... </typeEnv>
       <moved> ... L |-> 0 ... </moved>
       <mType> ...  S::F |-> immutableRef ... </mType>
    
  rule findMethod(F:Id, ref(X:Id))(Vs:Parameters) => F(&X, Vs)

  // mutable ref
  rule <k> X:Id . F:Id => findMethod(S::F, mutRef(X))  ... </k> 
       <env> ... X |-> L ... </env> 
       <typeEnv> ... L |-> S:Id ... </typeEnv>
       <moved> ... L |-> 0 ... </moved>
       <mType> ...  S::F |-> mutableRef ... </mType>
     
  rule findMethod(F:Id, mutRef(X:Id))(Vs:Parameters) => F(&mut X, Vs)

  // tuple struct
  // 1. tuple struct definition
  rule <k> struct X:Id (Ts:Types); => . ... </k>
       <env> ... .Map => X |-> L ... </env>
       <tempEnv> ... .Map => X |-> L ... </tempEnv>
       <nextLoc>  L => L +Int 1  </nextLoc>
       <store> ... .Map => L |-> tupleStruct(X,Ts) ... </store> 

  // 2. tuple struct assignment
  rule let  X  = S:Id(Vs:Vals); => let X; X = S(Vs); // S will be evaluated
  rule let mut X = S:Id(Vs:Vals); => let mut X; X = S(Vs); // S will be evaluated
  
  // TODO : Check Types
  rule <k> tupleStruct(S:Id, Ts:Types)(Vs:Vals) => tupleStructValue(S, Vs) ... </k>
  
  rule <k> X = tupleStructValue(S:Id, Vs:Vals); => . ... </k>
       <env> ... X |-> L ... </env>
       <moved> ... L |-> 0 ... </moved>
       <typeEnv> ... L |-> (undefined => S) ... </typeEnv>
       <store> ... L |-> (undefined => tuple(L,Vs)) ... </store>  // should not be tuple(L,Vs) ? 
  // end tuple struct

endmodule


