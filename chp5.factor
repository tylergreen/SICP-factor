USING: utils kernel vstack hashtables restruct ;

IN: fmachine

TUPLE: machine
    { registers hashtable }
    { stack vector } 
    ops
    instr-seq ;

SINGLETON: unset

! basic machine creation 
: <bare-machine> ( -- machine )
    machine new
    [ H{ } clone >>registers ]
    [ V{ } clone >>stack ] bi ;

! creates an unset register
: <register> ( name -- reg ) unset 2array ;

: <operation> ;

! analagous to make-machine + make-new-machine in text
: <machine> ( register-names ops controller-text  -- machine )
    [ { "pc" "flag" } append
      [ <register> ] map >hashtable ]
    [ [ <operation> ] map >hashtable ]
    [ assemble ] tri@ ;

! instead of an object, we are going to implement
! the machine as a quotation that takes messages as
! arguments

: start ( machine -- )
    "start" swap call ;

: get-reg-contents ( reg-name machine -- conts )
    get-register conts>> ;

! check this
: set-reg-contents! ( reg-name machine -- conts )
    dup get-register >>contents ;

: get-register ( reg-name machine -- )
    "get-register" swap call ;

! end object oriented style


: allocate-reg ( machine string -- )
    unset 2array swap registers>> set-at ;

: access ( machine reg-name -- value )
    swap registers>> at ;

! use lazy list
! need to look more closely at this
: execute ( machine -- machine )
    [ "pc" access dup empty? ]
    [ first execution-proc>> ]
    [ drop ] do while ;

! probably not right
: assemble ( controller-text machine -- )
    [ update-insts! ] curry extract-labels ;

: extract-labels ( receive text -- )
    dup empty?
    [ drop '[ { } { }  _ ] call ]
    [ unclip ] ;

! not right but general idea. I'm tired jeez
: extract-labels ( text )
    { { } { } }
    [ dup string?
      [ make-label-entry
        [ swons ] curry
        [ ] abi ]
      [ make-instr
        [ swons ] curry
        [ ] swap abi ]
      if ] reduce ;

! test this
: update-insts! ( insts labels machine -- )
    '[ [ instr-text _ _ make-execution ] keep
       set-instruction-proc! ] each  ;

: make-execution-proc ( inst labels machine -- )
    dup instr>> first
    { "assign" [ make-assign ]
      "test" [ make-test ]
      "branch" [ make-branch ]
      "goto" [ make-goto ]
      "save" [ make-save ]
      "restore" [ make-restore ]
      "perform" [ make-perform ]
      [ "Unknown instruction type" throw ]
    } case ;

: make-assign
    { ops>> pc>> } cleave .... ;



      
      

      
      

  
{ "a" "b" "temp" }
{ { rem rem } { = = } }
{ "test-b"
  [ "b" reg 0 = test ]
  [ "gcd-done" branch ]
  [ "a" reg "b" reg  "rem" op "temp" assign ]
  [ "b" reg "a" assign ]
  [ "temp" reg "b" assign ]
  [ "test-b" label goto ]
"gcd-done" } <controller>
