USING: accessors math utils kernel hashtables restruct sequences arrays lists lists.lazy assocs strings quotations continuations locals fry ;
IN: chp5

SYMBOLS: flag pc ;

! !!!!!
! Data 

TUPLE: op { args array } prim ;
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

TUPLE: mtest pred ;
C: <mtest> mtest
                
TUPLE: branch label ;
C: <branch> branch
                
TUPLE: goto location ;
C: <goto> goto
                
TUPLE: msave reg-name ;
C: <msave> msave
                
TUPLE: restore reg-name ;
C: <restore> restore

! !!!!! Machine

TUPLE: register conts ;
: <register> ( -- register ) register new ;

: set-contents! ( register x -- ) swap >>conts drop ;

TUPLE: stack s ;
: <stack> ( -- stack ) nil stack boa  ;

: spush ( elem stack -- ) [ s>> cons ] keep swap >>s drop ;
: spop ( stack -- elem ) [ s>> uncons ] keep swap >>s drop ;

: advance ( pc -- )
    dup conts>> rest-slice set-contents! ;

! maybe should call this asm
GENERIC: <exec> ( labels machine intr -- quot )
GENERIC: <op-expr> ( labels machine instr -- quot )

M: const <op-expr> ( labels machine instr -- quot )
    val>> '[ _ ] 2nip ;

M: label <op-expr> ( labels machine instr -- quot )
    nip lname>> swap at '[ _ ] ;

M: register <op-expr> ( labels machine instr -- quot )
    [ regs>> ] [ reg-name>> ] bi* swap at '[ _ conts>> ] nip ;

! don't like the second line but can't come up with anything better yet
! not sure if not distinguishing between primitives and ops screws up our language
M: op <op-expr> ( labels machine instr -- quot )
    [let | op [ dup prim>> ] 
           aprocs [ [ '[ _ _ rot <op-expr> ] ] dip args>> swap map ] |
        [ aprocs [ call ] each op call ] ] ;

! all quots produced by the following methods take a machine as argument and return a modified machine   
! M: assign <exec> ( instr -- quot )
!    [ <assign> ] undo '[ [ _ value ] [ regs>> ] bi _ swap set-at ] ;

! would like to come up with a more elegant solution to advancing the pc
M: assign <exec> ( labels machine instr -- quot )
    [let | pc [ over regs>> pc swap at ]
           target [ 2dup [ regs>> ] [ reg-name>> ] bi* swap at ]
           value-proc [ expr>> <op-expr> ] |
        [ target value-proc call set-contents! pc advance ] ] ;

M: mtest <exec> ( labels machine test -- quot )
    [let | pc [ over regs>> pc swap at ]
           flag [ over regs>> flag swap at ]
           condition-proc [ pred>> <op-expr> ] |
        [ flag condition-proc call set-contents! pc advance ] ] ;

M: branch <exec> ( labels machine branch -- quot )
    [let | pc [ over regs>> pc swap at ]
           flag [ over regs>> flag swap at ]
           insts [ nip label>> swap at ] |
        [ flag conts>>
          [ pc insts set-contents! ]
          [ pc advance ] if ] ] ;

GENERIC: <goto-exec> ( labels machine data -- quot )      
      
M: label <goto-exec> ( labels machine label -- quot )
    [let | pc [ over regs>> pc swap at ]
           insts [ nip lname>> swap at ] |
        [ pc insts set-contents! ] ] ;

M: register <goto-exec> ( labels machine register -- quot )
    [let | pc [ over regs>> pc swap at ]
           r [ [ regs>> ] [ reg-name>> ] bi* swap at nip ] |
        [ pc r conts>> set-contents! ] ] ;

M: goto <exec> ( labels machine goto -- quot ) <goto-exec> ;

M: msave <exec> ( labels machine save -- quot )
    [let | pc [ over regs>> pc swap at ]
           stack [ over stack>> ]
           r [ [ regs>> ] [ reg-name>> ] bi* swap at nip ] |
        [ r conts>> stack spush
          pc advance ] ] ;

M: restore <exec> ( labels machine save -- quot )
    [let | pc [ over regs>> pc swap at ]
           stack [ over stack>> ]
           r [ [ regs>> ] [ reg-name>> ] bi* swap at nip ] |
        [ reg stack spop set-contents! 
          pc advance ] ] ;

M: perform <exec> ( labels machine perform -- quot )
    [let | pc [ over regs>> pc swap at ]
           action-proc [ <op-expr> ] |
        [ action-proc call
          pc advance ] ] ;

! read page 520 to review how to fix this final problem      
: update-insts! ( machine labels insts -- )
    ;

! this is more complicated than you thought
! need to assemble from the end to the beginning so 
: assemble ( machine controller-text -- instrs )
    2 nsplit dup values update-insts! ;

! huge problem here
TUPLE: machine regs stack instr-seq ;

: <machine> ( reg-names ctext -- machine )
    [ { pc flag } append [ <register> 2array ] map
      <stack> f machine boa
    ] keep
    [ assemble ] keep swap >>instr-seq ;
      
SYMBOLS: a b temp test-b gcd-done ; ! would like to eventually incorporate this line into the machine spec if possible
: gcd-machine ( -- machine )
    { a b temp }
    { test-b  [ { b <reg> 0 <const> } [ = ] <op> <mtest>
                gcd-done <branch>
                { a <reg> b <reg> } [ rem ] <op> temp <assign>
                b <reg> a <assign>
                temp <reg> b <assign>
                test-b <label> <goto> ]
      gcd-done [ ]
    }  <machine> ;
