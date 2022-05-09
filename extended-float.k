// Copyright (c) 2013-2016 K Team. All Rights Reserved.
module FLOAT-SYNTAX
  syntax Float [hook(FLOAT.Float)]
  syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]d+))?" [token]
  //syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]d+))?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
  syntax Float ::= r"[\\+-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
  syntax Float ::= r"NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
endmodule

module FLOAT
  imports FLOAT-SYNTAX
  imports BOOL
  imports INT-SYNTAX

  syntax Int ::= precisionFloat(Float) [function, hook(FLOAT.precision)]
               | exponentFloat(Float) [function, hook(FLOAT.exponent)]
               | exponentBitsFloat(Float) [function, hook(FLOAT.exponentBits)]

  syntax Bool ::= signFloat(Float)      [function, hook(FLOAT.sign)]
                | isNaN(Float)          [function, smtlib((not (== #1 #1))), hook(FLOAT.isNaN)]
                | isInfinite(Float)     [function]
  syntax MInt ::= significandFloat(Float) [function, hook(FLOAT.significand)]

  syntax Float ::= fpNaN(Int, Int)              [smtlib((as NaN (_ FP #1 #2)))]
                 | plusInfinity(Int, Int)       [smtlib((as plusInfinity (_ FP #1 #2)))]
                 | minusInfinity(Int, Int)      [smtlib((as minusInfinity (_ FP #1 #2)))]

  syntax Float ::= "--Float" Float             [function, smtlib(-), hook(FLOAT.neg)]
                 > Float "^Float" Float        [function, left, latex({#1}^{#2}), hook(FLOAT.pow)]
                 > left:
                   Float "*Float" Float        [function, left, smtlib((* roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(FLOAT.mul)]
                 | Float "/Float" Float        [function, left, smtlib((/ roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(FLOAT.div)]
                 | Float "%Float" Float        [function, left, smtlib((remainder roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(FLOAT.rem)]
                 > left:
                   Float "+Float" Float        [function, left, smtlib((+ roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(FLOAT.add)]
                 | Float "-Float" Float        [function, left, smtlib((- roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(FLOAT.sub)]

  syntax Float ::= rootFloat(Float, Int)        [function, hook(FLOAT.root)]
                 | absFloat(Float)              [function, smtlib(abs), hook(FLOAT.abs)]
                 | roundFloat(Float, Int, Int)  [function, hook(FLOAT.round)]
                 | floorFloat(Float)            [function, hook(FLOAT.floor)]
                 | ceilFloat(Float)             [function, hook(FLOAT.ceil)]
                 | expFloat(Float)              [function, hook(FLOAT.exp)]
                 | logFloat(Float)              [function, hook(FLOAT.log)]
                 | sinFloat(Float)              [function, hook(FLOAT.sin)]
                 | cosFloat(Float)              [function, hook(FLOAT.cos)]
                 | tanFloat(Float)              [function, hook(FLOAT.tan)]
                 | asinFloat(Float)             [function, hook(FLOAT.asin)]
                 | acosFloat(Float)             [function, hook(FLOAT.acos)]
                 | atanFloat(Float)             [function, hook(FLOAT.atan)]
                 | atan2Float(Float, Float)     [function, hook(FLOAT.atan2)]
                 | maxFloat(Float, Float)       [function, smtlib(max), hook(FLOAT.max)]
                 | minFloat(Float, Float)       [function, smtlib(min), hook(FLOAT.min)]
                 | sqrtFloat(Float)             [function]
                 | maxValueFloat(Int, Int)      [function, hook(FLOAT.maxValue)]
                 | minValueFloat(Int, Int)      [function, hook(FLOAT.minValue)]

  syntax Bool ::= Float "<=Float" Float       [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.le)]
                | Float "<Float" Float        [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(FLOAT.lt)]
                | Float ">=Float" Float       [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.ge)]
                | Float ">Float" Float        [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(FLOAT.gt)]
                | Float "==Float" Float       [function, left, smtlib(==), latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(FLOAT.eq)]
                | Float "=/=Float" Float      [function, left, smtlib((not (== #1 #2))), latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]


  rule F1:Float =/=Float F2:Float => notBool (F1 ==Float F2)

  syntax Float ::= Int2Float(Int, Int, Int)    [function, latex({\\it{}Int2Float}), hook(FLOAT.int2float)]
  syntax Int ::= Float2Int(Float)    [function, latex({\\it{}Float2Int}), hook(FLOAT.float2int)]

  rule sqrtFloat(F:Float) => rootFloat(F, 2)

  rule isInfinite(F:Float) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))

endmodule
module EXTENDED-FLOAT
   imports FLOAT
endmodule
