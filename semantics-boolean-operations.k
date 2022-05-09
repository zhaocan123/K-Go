require "rs-syntax.k"
module RS-SEMANTICS-BOOLEAN-OPERATIONS
  imports RS-SYNTAX
  
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int > I2:Int => I1 >Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2
   
  rule I1:Float > I2:Float => I1 >Float I2
  rule I1:Float < I2:Float => I1 <Float I2
  rule I1:Float >= I2:Float => I1 >=Float I2
  rule I1:Float <= I2:Float => I1 <=Float I2
  
  rule V1:Int == V2:Int => V1 ==Int V2
  rule V1:Float == V2:Float => V1 ==Float V2
  rule V1:Int != V2:Int => V1 =/=K V2

  rule ! T:Bool => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E
endmodule 