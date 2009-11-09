USING: accessors grouping namespaces prettyprint math math.order kernel hashtables sequences arrays lists lists.lazy assocs strings quotations continuations locals fry ;
IN: sicp.chp5

SYMBOLS: flag pc ;

CONSTANT: heap-size 500

! *********************
! Primitive Data Types

TUPLE: op { args array } prim ;
: <op> ( args quot -- op )
    [ >quotation { } swap with-datastack ] dip op boa ;

TUPLE: const val ;
C: <const> const

TUPLE: reg reg-name ;
C: <reg> reg

TUPLE: label lname ;
C: <label> label

! ******************
! Primitive Instruction Syntax

TUPLE: assign expr reg-name ;
C: <assign> assign
                
TUPLE: perform expr ;
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


! ****************
!  Machine Specification

TUPLE: machine regs stack instr-seq ;

TUPLE: register conts ;
: <register> ( -- register ) register new ;

: set-contents! ( register x -- ) >>conts drop ;

TUPLE: stack s push-count max-depth depth ;
: <stack> ( -- stack ) nil 0 0 0 stack boa ;

! **********
! Machine actions -- clearly not turing complete without random access memory store

: spush ( elem stack -- )
    [ cons ] change-s
    [ 1 + ] change-push-count 
    [ 1 + ] change-depth
    dup [ max-depth>> ] [ depth>> ] bi max >>max-depth drop ;
 
: spop ( stack -- elem )
    dup nil?
    [ "Empty Stack -- SPOP" throw ]
    [ [ 1 - ] change-depth
      [ uncons ] change-s drop
    ] if ; 

! regular eager list- can we make it lazy?  if so what then?
: advance ( pc -- )
    [ rest-slice ] change-conts drop ; inline

! *********
! MachineLanguage->Factor Compiler
! could have made these macros instead -- should try it

! what is this doing?
GENERIC: <op-expr> ( labels machine instr -- quot )

M: const <op-expr> ( labels machine instr -- quot )
    val>> '[ _ ] 2nip ;

M: label <op-expr> ( labels machine instr -- quot )
    nip lname>> swap at '[ _ ] ;

M: reg <op-expr> ( labels machine instr -- quot )
    [ regs>> ] [ reg-name>> ] bi* swap at '[ _ conts>> ] nip ;

M: op <op-expr> ( labels machine instr -- quot )
    [let dup prim>> :> op
        [ '[ _ _ rot <op-expr> ] ] dip args>> swap map :> aprocs
        [ aprocs [ call ] each op call ] ] ;

! What does this do?
GENERIC: <exec> ( labels machine instr -- quot )

M: assign <exec> ( labels machine instr -- quot )
    [let
        over regs>> pc swap at :> pc
        2dup [ regs>> ] [ reg-name>> ] bi* swap at :> target
        expr>> <op-expr> :> value-proc
        [ target value-proc call set-contents! pc advance ] ] ; inline

M: perform <exec> ( labels machine perform -- quot )
    [let over regs>> pc swap at :> pc
        expr>> <op-expr>  :> action-proc
        [ action-proc call pc advance ] ] ; inline

M: mtest <exec> ( labels machine test -- quot )
    [let over regs>> pc swap at :> pc 
         over regs>> flag swap at :> flag
         pred>> <op-expr> :> condition-proc
        [ flag condition-proc call set-contents! pc advance ] ] ; inline

M: branch <exec> ( labels machine branch -- quot )
    [let
        over regs>> pc swap at :> pc
        over regs>> flag swap at :> flag
        nip label>> swap at :> insts
        [ flag conts>>
          [ pc insts set-contents! ]
          [ pc advance ] if ] ] ; inline

GENERIC: <goto-exec> ( labels machine data -- quot )      
      
M: label <goto-exec> ( labels machine label -- quot )
    [let over regs>> pc swap at :> pc
         nip lname>> swap at :> insts
        [ pc insts set-contents! ] ] ; inline

M: reg <goto-exec> ( labels machine register -- quot )
    [let over regs>> pc swap at :> pc
        [ regs>> ] [ reg-name>> ] bi* swap at nip :> r
        [ pc r conts>> set-contents! ] ] ; inline

M: goto <exec> ( labels machine goto -- quot ) location>> <goto-exec> ; inline

M: msave <exec> ( labels machine save -- quot )
    [let over regs>> pc swap at :> pc
        over stack>>  :> stack
        [ regs>> ] [ reg-name>> ] bi* swap at nip :> r
        [ r conts>> stack spush
          pc advance ] ] ; inline

M: restore <exec> ( labels machine save -- quot )
    [let over regs>> pc swap at  :> pc 
        over stack>> :> stack
        [ regs>> ] [ reg-name>> ] bi* swap at nip :> r
        [ r stack spop set-contents! 
          pc advance ] ] ; inline

! *********
! Assembling and machine construction
TUPLE: instruction text quot ;
: <instr> ( instr-text -- instr ) instruction new swap >>text ; inline

:: update-insts! ( machine labels insts -- insts )
    insts [ dup text>> labels machine rot <exec> >>quot ] map ; inline

: assemble ( machine controller-text -- insts )
    2 group [ { } swap with-datastack [ <instr> ] map
    ] assoc-map dup values concat update-insts! ; inline

: <machine> ( reg-names ctext -- machine )
    [ { pc flag } append [ <register> 2array ] map
      <stack> f machine boa dup
    ] dip assemble >>instr-seq
dup [ regs>> pc swap at ] [ instr-seq>> ] bi set-contents! ; inline


! ***********************
! User-machine interface

:: set-reg ( machine reg-name value -- machine )
    reg-name machine regs>> at value set-contents! machine ;

: get-reg ( machine reg-name -- value ) swap regs>> at conts>> ;

! this is where you would hook up the macro -- see call
: exec ( machine -- machine )
    dup pc get-reg dup empty?
    [ drop "done" . ]
    [ first quot>> call( -- ) exec ] if ; inline recursive


! *********************
! Pre-Defined machines
      
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

:: gcddemo ( a1 b1 -- c )
    gcd-machine
    a a1 set-reg 
    b b1 set-reg 
    exec
    a get-reg ; inline
    
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
  
:: factdemo ( x -- a )
    fact-machine
    n x set-reg
    exec
    val get-reg ; inline

SYMBOLS: fib-loop afterfib-n-1 afterfib-n-2  immediate-answer fib-done ;
: fib-machine ( -- machine )
    { n val cont }
    { start [ fib-done <label> cont <assign> ]
      fib-loop [ { n <reg> 2 <const> } [ < ] <op> <mtest>
                 immediate-answer <branch>
                 cont <msave>
                 afterfib-n-1 <label> cont <assign>
                 n <msave>
                 { n <reg> 1 <const> } [ - ] <op> n <assign>
                 fib-loop <label> <goto> ]
      afterfib-n-1 [ n <restore>
                     cont <restore>
                     { n <reg> 2 <const> } [ - ] <op> n <assign>
                     cont <msave>
                     afterfib-n-2 <label> cont <assign>
                     val <msave>
                     fib-loop <label> <goto> ]
      afterfib-n-2 [ val <reg> n <assign>
                     val <restore>
                     cont <restore>
                     { val <reg> n <reg> } [ + ] <op> val <assign>
                     cont <reg> <goto> ]
      immediate-answer [ n <reg> val <assign>
                         cont <reg> <goto> ]
      fib-done [ ] } <machine> ; 

:: fibdemo ( x -- a )
    "fib(5):" .
    fib-machine 
    n x set-reg
    exec
    val get-reg ; inline

! ex. 5.21 (a)
SYMBOLS: tree count-done count-loop count-left count-right base-zero base-one ;
: leaf-counter ( -- machine )
    { tree val cont temp }
    { start [ count-done <label> cont <assign> ]
      count-loop [ { tree <reg> } [ nil? ] <op> <mtest>
                   base-zero <branch>
                   { tree <reg> } [ cons? ] <op> temp <assign>
                   { temp <reg> } [ not ] <op> <mtest>
                   base-one <branch>
                   cont <msave>
                   count-left <label> cont <assign>
                   tree <msave>
                   { tree <reg> } [ car ] <op> tree <assign>
                   count-loop <label> <goto> ]
      count-left [ tree <restore>
                   cont <restore>
                   { tree <reg> } [ cdr ] <op> tree <assign>
                   cont <msave>
                   count-right <label> cont <assign>
                   val <msave>
                   count-loop <label> <goto> ]
      count-right [ val <reg> temp <assign>
                    val <restore>
                    cont <restore>
                    { val <reg> temp <reg> } [ + ] <op> val <assign>
                    cont <reg> <goto> ]
      base-zero [ 0 <const> val <assign>
                  cont <reg> <goto> ]
      base-one [ 1 <const> val <assign>
                  cont <reg> <goto> ]
      count-done [ ] } <machine> ;

:: count-leaves-demo ( cons-tree -- n )
    leaf-counter
    tree cons-tree set-reg
    exec
    val get-reg ;

! ex. 5.21 (b)

SYMBOLS: found-leaf ;
: count-leaves2 ( -- machine )
    { tree n temp }
    { count-loop [ { tree <reg> } [ nil? ] <op> <mtest>
                   count-done <branch>
                   { tree <reg> } [ cons? ] <op> temp <assign>
                   { temp <reg> } [ not ] <op> <mtest>
                   found-leaf <branch>
                   ! not done
    ] } <machine> ;
