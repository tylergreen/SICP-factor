USING: accessors prettyprint math utils kernel hashtables restruct sequences arrays lists lists.lazy assocs strings quotations continuations locals fry ;
IN: sicp.chp5

SYMBOLS: flag pc ;

! !!!!!
! Data 

TUPLE: op { args array } prim ;
: <op> ( args quot -- op )
    [ >quotation { } swap with-datastack ] dip op boa ;

TUPLE: const val ;
C: <const> const

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

TUPLE: machine regs stack instr-seq ;

TUPLE: register conts ;
: <register> ( -- register ) register new ;

: set-contents! ( register x -- ) >>conts drop ;

TUPLE: stack s ;
: <stack> ( -- stack ) nil stack boa  ;

: spush ( elem stack -- ) [ s>> cons ] keep swap >>s drop ;
: spop ( stack -- elem ) [ s>> uncons ] keep swap >>s drop ;

: advance ( pc -- )
    dup conts>> rest-slice set-contents! ;

GENERIC: <exec> ( labels machine intr -- quot )
GENERIC: <op-expr> ( labels machine instr -- quot )

M: const <op-expr> ( labels machine instr -- quot )
    val>> '[ _ ] 2nip ;

M: label <op-expr> ( labels machine instr -- quot )
    nip lname>> swap at 1q ;

M: reg <op-expr> ( labels machine instr -- quot )
    [ regs>> ] [ reg-name>> ] bi* swap at '[ _ conts>> ] nip ;

! don't like the second line but can't come up with anything better yet
! not sure if not distinguishing between primitives and ops screws up our language
M: op <op-expr> ( labels machine instr -- quot )
    [let | op [ dup prim>> ] 
           aprocs [ [ '[ _ _ rot <op-expr> ] ] dip args>> swap map ] |
        [ aprocs [ call ] each op call ] ] ;

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

M: reg <goto-exec> ( labels machine register -- quot )
    [let | pc [ over regs>> pc swap at ]
           r [ [ regs>> ] [ reg-name>> ] bi* swap at nip ] |
        [ pc r conts>> set-contents! ] ] ;

M: goto <exec> ( labels machine goto -- quot ) location>> <goto-exec> ;

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
        [ r stack spop set-contents! 
          pc advance ] ] ;

M: perform <exec> ( labels machine perform -- quot )
    [let | pc [ over regs>> pc swap at ]
           action-proc [ <op-expr> ] |
        [ action-proc call
          pc advance ] ] ;

TUPLE: instruction text quot ;
: <instr> ( instr-text -- instr ) instruction new swap >>text ;

:: update-insts! ( machine labels insts -- insts )
    insts [ dup text>> labels machine rot <exec> >>quot ] map ;

: assemble ( machine controller-text -- insts )
    2 nsplit [ { } swap with-datastack [ <instr> ] map
    ] assoc-map dup values concat update-insts! ;

: <machine> ( reg-names ctext -- machine )
    [ { pc flag } append [ <register> 2array ] map
      <stack> f machine boa dup
    ] dip assemble >>instr-seq dup [ regs>> pc swap at ] [ instr-seq>> ] bi set-contents! ;

: exec ( machine -- machine )
    dup regs>> pc swap at conts>> dup empty?
    [ drop "done" . ]
    [ first quot>> call exec ] if ; inline

:: set-reg ( machine reg-name value -- machine )
    reg-name machine regs>> at value set-contents! machine ;

: get-reg ( machine reg-name -- value ) swap regs>> at ;
      
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
    } <machine> ;

SYMBOLS: n val cont start fact-loop after-fact base-case fact-done ;
: fact-machine ( -- machine )
    { n val cont }
    { start [ fact-done <label> cont <assign> ]
      fact-loop [ { n <reg> 0 <const> } [ = ] <op> <mtest>
                  base-case <branch>
                  cont <msave>
                  n <msave>
                  { n <reg> 1 <const> } [ - ] <op> n <assign>
                  after-fact <label> cont <assign>
                  fact-loop <label> <goto> ]
      after-fact [ n <restore>
                   cont <restore>
                   { n <reg> val <reg> } [ * ] <op> val <assign>
                   cont <reg> <goto> ]
      base-case [ 1 <const> val <assign>
                  cont <reg> <goto> ]
      fact-done [ ] } <machine> ;
