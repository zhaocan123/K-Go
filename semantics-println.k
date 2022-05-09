require "rs-semantics-common.k"
module RS-SEMANTICS-PRINT
  imports RS-SEMANTICS-COMMON
  context print(HOLE:Exp, Eps:Exps);
  rule <k> print(V:Val, Eps); => print(Eps); ... </k>
       <out> ... .List => ListItem(V) </out>        [print]
       
  rule <k> print(string(L:Int, S:String),Eps); => print(Eps); ... </k>
       <out> ... .List => ListItem(S) </out>        [print]

  rule print(ref(Y:Id), Eps); => print(Y, Eps); 

  //@ rule <k> print(ref(Y:Id), Eps => Eps); ... </k>
  //@      <out> ... .List => ListItem(S) </out>        [print]
  rule print(.Exps); => .                           [structural]                              
  //rule println!("{}", V:Val); => print(V);
  rule println!(E:String); => print(E);
  rule println!(E:String, Eps:Exps); => print(Eps);
  rule println!(E:String, (Eps:Exps)); => print(Eps);
  
endmodule