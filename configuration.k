
module CONFIGURATION

imports BPMN-SYNTAX


syntax START


configuration
    <k> $PGM:START </k>
    <exit-code exit=""> 0 </exit-code>

    <ethereum>   //以太坊

        <bpmn>
            <execEngine>
                <output>          .K                             </output>
                <statusCode>      .K                             </statusCode>
                <callStack>       .List                          </callStack>
                <interimStates>   .List                          </interimStates>
                <touchedAccounts> .K                             </touchedAccounts>

                <currentAccount>  #account(0, #Testing-Engine#)  </currentAccount>
                <result>          #undef_Value                   </result>
                <mode>            .K                             </mode>

                <callState>

                    <program> .K </program>              // currently running <contract>

                   
                    <id>         0 </id>        // Currently executing contract
                    <caller>    .K </caller>    // Contract that called current contract
                    <callData>  .K </callData>  // .WordStack Copy of register arguments (?)
                    <callValue>  0 </callValue> // Value in funds passed to contract

                
                    <env> .Map </env>     // Map of names to references

                  
                    <tenv> .Map </tenv>         // Map names to types

                   
                    <localMem> .Map </localMem>
                    <memorySlots> 0 </memorySlots>

                   
                    <gas>         0:Int </gas>
                    <memoryUsed>  0:Int </memoryUsed>
                    <previousGas> 0:Int </previousGas>

                    
                    <static>    false:Bool </static>
                    <callDepth> 0          </callDepth>

                    
                    <abnormalMode>     false:Bool      </abnormalMode>
                    <abnormalCode>     .K              </abnormalCode>

                    <isExternalFunctionCall> false:Bool </isExternalFunctionCall>
                </callState>

                <substate>
                    <selfDestruct> .Set  </selfDestruct>            // A_s
                    <log>          .List </log>                     // A_l
                    <refund>       0     </refund>                  // A_r
                </substate>

                

                <gasPrice> 0 </gasPrice>                          // I_p
                <origin>   0 </origin>                            // I_o

                
                <block>
                    <hashes>     .List      </hashes>
                    <coinbase>   0          </coinbase>   // H_c
                    // <logsBloom>  .WordStack </logsBloom>  // H_b
                    <difficulty> 0          </difficulty> // H_d
                    <number>     0          </number>     // H_i
                    <gasLimit>   0          </gasLimit>   // H_l
                    <timestamp>  0          </timestamp>  // H_s
                </block>
            </execEngine>

        

            <tasks>
                <task multiplicity = "*" type="Map">
                    <tid> .K </tid>

                      <userTask>
                          <uname> .K </uname>
                          <documentation> .K </documentation>
                          <inputStream> .K   </inputStream>
                          <outputStream> .K  </outputStream>
                          <extension> .List  </extension>
                      </userTask>
                    

                </task>
            </tasks>

    <flow multiplicity = "*" type="Map">
        <sid> .K </sid>
            <sequenceflow>
              <sname> .K </sname>
              <sourceRef> .K  </sourceRef>
              <targetRef> .K  </targetRef>
              <extension> .List  </extension>
            </sequenceflow>
    </flow>

      <gate multiplicity = "*" type="Map">
        <gid> .K </gid>
            <exclusiveGateway>
              <sname> N </sname>
              <inputStream> .List   </inputStream>
              <outputStream> .List  </outputStream>
              <extension> .List  </extension>
            </exclusiveGateway>)
        
     </gate>






        </bpmn>


        <network>


            <activeAccounts> .Set </activeAccounts>


            <accounts>
                <account multiplicity="*" type="Map">

                    

                    <acctID> 0 </acctID>
                    <contractName> #Testing-Engine# </contractName>
                    <balance>  0 </balance>


                    <acctEnv> .Map </acctEnv>

                    

                    <code>
                        <associatedContract> .K </associatedContract>    // contract deployed on this account
                        <availableContracts> .K </availableContracts>    // contracts that can be created by this account's contract
                    </code>

                    

                    <acctStorage> .Map </acctStorage>
                    <acctSlots> 0 </acctSlots>

                    

                    <nonce> 0:Int </nonce>

                </account>
            </accounts>

           
            <txOrder>   .List </txOrder>
            <txPending> .List </txPending>

            

            <messages>
                <message multiplicity="*" type="Map">
                <msgID>       0 </msgID>      // Unique ID of transaction
                <txNonce>     0 </txNonce>    // Nonce of transaction (not checked)
                <txGasPrice>  0 </txGasPrice> // Gas price of transaction
                <txGasLimit>  0 </txGasLimit> // Gas limit of transaction
                <sendto>     .K </sendto>     // Destination of transaction (.Account for account creation)
                <func>       .K </func>       // Function to call by transaction
                <value>       0 </value>      // Value in funds to transfer by transaction
                <from>        0 </from>       // Sender of transaction
                <data>       .K </data>       // .WordStack Arguments to function called by transaction
                <args>       .K </args>       //.Ints
                </message>
            </messages>

        </network>

    </ethereum>

endmodule
