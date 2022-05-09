require "rs-semantics-common.k"
module RS-SEMANTICS-WHILE
  imports RS-SEMANTICS-COMMON
  //@ syntax Stmts ::= "BeginLoop" | "EndLoop"
  //@ rule <k> while E { S:Stmts } ~> K => BeginLoop while E { S } ... </k>
  //@      <xstack> ... .List => ListItem(K) </xstack>
  //@      <lstack> ... .List => ListItem(while E {S}) </lstack>
  //@ //rule while E { S:Stmts }; => Begin while E { S:Stmts }
  //@ rule while E { S:Stmts }; => while E {S}
  //@ rule BeginLoop while E { S:Stmts } => if E { S while E { S } } else { EndLoop }  [structural] 
  //@ //rule while E { S:Stmts }; => if E { S while E { S } }  [structural] 
  //@ rule while E {A:AugAssign} => while E {A;}   [structural]                          
  //@ rule loop S:Block => while true S [structural]
  //@ // continue to execute the following computations
  //@ rule <k> EndLoop  => REST </k>
  //@      <xstack> ... ListItem(REST:K) => .List </xstack>
  //@      <lstack> ... ListItem(_:K) => .List </lstack> 
  //@ // break statement 
  //@ rule <k> break ; ~> _  => REST:K </k>
  //@      <xstack> ... ListItem(REST:K) => .List  </xstack>
  //@      <lstack> ... ListItem(_:K) => .List </lstack> 
  //@ // continue statement 
  //@ rule <k> continue; ~> _ => REST:K </k>
  //@      <lstack> ... ListItem(REST:K)  </lstack>  


  // original version
  rule while E { S:Stmts } => if E { S while E { S } }  [structural] 
  rule while E { S:Stmts }; => if E { S while E { S } }  [structural] 
  rule while E {A:AugAssign} => while E {A;}   [structural]                          
  rule loop S:Block => while true S [structural]
  rule while true {S:Stmts ~> break; ~> LS:Stmts} => S
  // end original
endmodule