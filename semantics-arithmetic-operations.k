require "rs-syntax.k"

module RS-SEMANTICS-ARITHMETIC-OPERATIONS
  imports RS-SYNTAX
  rule - I:Int => 0 -Int I:Int
  rule -I:Float => 0.0 - I
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Float + I2:Float => I1 +Float I2   
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Float - I2:Float => I1 -Float I2

  rule I1:Int * I2:Int => I1 *Int I2
  rule A:Float * B:Float => A *Float B
  

  rule I1:Int / I2:Int => I1 /Int I2  requires I2 =/=K 0
  rule I1:Float / I2:Float => I1 /Float I2
  // /= needs to add [structural]  *= += -= %= don't have to add it. I don't know why...
  

  rule I1:Int % I2:Int => I1 %Int I2  requires I2 =/=K 0
  
  rule X:Id += I; => X = X + I;                   [structural]
  rule X:Id -= I; => X = X - I;                   [structural]
  rule X:Id *= I; => X = X * I;                   [structural]
  rule X:Id /= I; => X = X / I;      requires I =/=K 0           [structural]
  rule X:Id %= I; => X = X % I;      requires I =/=K 0            [structural]
  rule *X:Id += I; => *X = *X + I;                   [structural]
  rule *X:Id -= I; => *X = *X - I;                   [structural]
  rule *X:Id *= I; => *X = *X * I;                   [structural]
  rule *X:Id /= I; => *X = *X / I;      requires I =/=K 0           [structural]
  rule *X:Id %= I; => *X = *X % I;      requires I =/=K 0            [structural]
  
  rule I1:Int << I2:Int => I1 <<Int I2
  rule I1:Int >> I2:Int => I1 >>Int I2
  rule I1:Int & I2:Int => I1 &Int I2
  rule I1:Int | I2:Int => I1 |Int I2
  rule ! I:Int => ~Int I
endmodule