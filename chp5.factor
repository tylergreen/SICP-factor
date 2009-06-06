USING: utils kernel hashtables restruct sequences arrays lists lists.lazy assocs strings quotations locals fry ;
IN: chp5

! !!!!!
! Data 

TUPLE: op { args array } quot ;
: <op> ( args quot -- op )
    [ >quotation { } swap with-datastack ] dip op boa ;

TUPLE: const val ;
C: <const> const

! should the slot be called reg-name instead?
TUPLE: reg reg-name ;
C: <reg> reg

TUPLE: label lname ;
C: <label> label

! !!!!!!!!!!!!!
! Instructions

TUPLE: assign expr reg-name ;
C: <assign> assign
                
TUPLE: perform inputs op ;
C: <perform> perform

TUPLE: mtest expr ;
C: <mtest> mtest
                
TUPLE: branch label ;
C: <branch> branch
                
TUPLE: goto location ;
C: <goto> goto
                
TUPLE: msave reg-name ;
C: <msave> msave
                
TUPLE: restore reg-name ;
C: <restore> restore

TUPLE: machine stack regs ops ;
: <machine> ( reg-names ops ctext -- machine )
    [ { pc flag } append [ f 2array ] map ]
    [ 2 nsplit ]
    [ assemble ] tri* machine boa ;

! need to figure out how we're going to do this one, but I think this is correct
: assemble ( controller-text -- instrs )
    2 nsplit [ <exec> ] assoc-map ;

! maybe should call this asm
GENERIC: <exec> ( instruction -- quot )

! all quots produced by the following methods take a machine as argument and return a modified machine   
! M: assign <exec> ( instr -- quot )
!    [ <assign> ] undo '[ [ _ value ] [ regs>> ] bi _ swap set-at ] ;

! would like to come up with a more elegant solution to advancing the pc
M: assign <exec> ( instr -- quot )
    [ <assign> ] undo '[ [ _ value ] [ regs>> ] bi _ swap set-at ] advance-pc ;

GENERIC: get-value ( machine obj -- value )
! M: op get-value ( machine op -- v ) ; 
M: const get-value ( machine const -- v ) nip val>> ;  ! works 
M: reg get-value ( machine reg -- v ) [ regs>> ] [ rname>> ] bi* swap at ;   ! works
! M: label get-value ( machine label -- v ) ;

M: mtest <exec> ( test -- quot )
    expr>> dup op?
    [ make-operation-expr '[ _ swap >>flag ] ] 
    [ "Bad Test Instr -- ASSEMBLE" throw ] if
    ;

! should add error checking
M: branch <exec> ( branch -- quot )
    label>> ;
          
M: goto <exec> ( goto -- quot )
    ;

M: save <exec> ( save -- quot )
          ;

M: restore <exec> ( save -- quot )
          ;

M: perform <exec> ( perform -- quot )
          ;

! obviously this will need to be different if pc is stationary and instr-seq moves      
: advance-pc ( quot -- quot )
    [ keep dup regs>> pc at cdr >>regs ] curry ;

: make-operation-exp ( expr -- quot )
    [ aprocs [ call ] map op ] ; ! something like this

SYMBOLS: a b temp test-b gcd-done ; ! would like to eventually incorporate this line into the machine spec if possible
: gcd-machine ( -- machine )
    { a b temp }
    { rem [ rem ] = [ = ] }
    { test-b  [ { b <reg> 0 <const> } [ = ] <op> <mtest>
                gcd-done <branch>
                { a <reg> b <reg> } [ rem ] <op> temp <assign>
                b <reg> a <assign>
                temp <reg> b <assign>
                test-b <label> <goto> ]
      gcd-done [ ]
    } <machine> ;
