USING: utils kernel hashtables restruct locals fry sequences arrays lists lists.lazy assocs strings ;
IN: chp5

TUPLE: assign reg-name expr ;
C: <assign> assign
                
TUPLE: perform op inputs ;
C: <perform> perform
                
TUPLE: test expr ;
C: <test> test
                
TUPLE: branch label ;
C: <branch> branch
                
TUPLE: goto location ;
C: <goto> goto
                
TUPLE: assign reg label ;
C: <assign> assign
                
TUPLE: save reg-name ;
C: <save> save
                
TUPLE: restore reg-name ;
C: <restore> restore                

! all quots produced by the following methods take a machine as argument
M: assign <exec> ( instr -- quot )
    [ reg 

                ;

M: test <exec> ( test -- quot )
           ;

M: branch <exec> ( branch -- quot )
           ;
          
M: goto <exec> ( goto -- quot )
          ;

M: save <exec> ( save -- quot )
          ;

M: restore <exec> ( save -- quot )
          ;

M: perform <exec> ( perform -- quot )
          ;
                
M: <exeq> assign ( -- quot ) ;
                
                

                    
! we aren't going to keep the text around for now
: update-insts! ( insts labels machine -- )
    '[ [ instr-text _ _ make-exec-proc ] ] each ;
                    
: assemble ( contoller-text machine -- )
    [ [ string? ] partition swap ] dip update-insts! ;
                    
: <machine> ( reg-names ops controller-text -- machine )
        <new-machine>
        [ '[ _ "allocate-reg" sm ] each ]
        [ "install-ops" sm ]
        [ assemble ] tri-curry tri 
        dup "install-instr-seq" sm ; ! dup might not be necessary

: gcd-machine ( -- quot )
{ a b temp }
{ { rem [ rem ] } { = [ = ] } }
{ test-b
  { b <reg> 0 <const> = <op> "test" }
  { gcd-done <branch> }
  { "a" <reg>" "b" <reg>  "rem" "op" "temp" "assign" }
  { "b" "reg" "a" "assign" }
  { "temp" "reg" "b" "assign" }
  { "test-b" "label" "goto" }
"gcd-done" } <machine> ;
