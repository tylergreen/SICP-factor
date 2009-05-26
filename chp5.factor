USING: utils kernel hashtables restruct sequences arrays lists lists.lazy assocs strings locals fry ;
IN: chp5

! can refine this as necessary
TUPLE: machine stack regs ops ;
C: <machine> machine

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

! !!!!!
! Data 

TUPLE: const val ;
C: <const> const

TUPLE: op inputs opname ;
C: <op> op

TUPLE: reg rname ;
C: <reg> reg

TUPLE: label lname ;
C: <label> label

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
                
: advance-pc ( quot -- quot )
    [ keep dup regs>> pc at cdr >>regs ] curry ;

! work in progress
SYMBOLS: a b temp ;
: gcd-machine ( -- quot )
{ a b temp }
{ { rem [ rem ] } { = [ = ] } }
test-b <label>
  { b <reg> 0 <const> } = <op> <mtest>
  gcd-done <branch>
  { a <reg> b <reg> } rem <op> temp <assign>
  b <reg> a <assign> 
  temp <reg> b assign
  test-b <label> <goto>
gcd-done <label>  <some-machine> ;
