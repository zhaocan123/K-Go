requires"bpmn-syntax.k"
module SEQUENCEFLOW
imports BPMN-SYNTAX
rule [sequenceFlow-definition]:
    <k> #sequence(Ut:Id, sequenceflowStart(N:Names,Na:Names,Nb:Names) conditionexpression(Con:condition) conditionexpressionEnd sequenceflowEnd)
            => . ... </k>
    <flow>
        <sid> St </sid>
        (.Bag =>
            <sequenceflow>
            <sname> N </sname>
            <sourceRef> Na   </sourceRef>
            <targetRef> Nb  </targetRef>
            <extension> .List  </extension>
            </sequenceflow>)
        ...
    </flow>
syntax BPMNItem::= "#inputStream" | "#outputStream" | 

rule [sourceRef]:
       <k> #sourceref =>. ... </K>
       <Stream> ref </Stream>
       <Stream> (.List => ListItem(ref) ) ... </Stream>

rule [targetRef]:
       <K>#targetref =>. ...</K>
       <Stream> _ => ref </Stream>
       <Stream> (ListItem(ref) => .List ) ... </Stream>


rule
    <k> #CData(.CData) => . ... </K>
