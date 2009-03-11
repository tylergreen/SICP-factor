USING: utils kernel vstack hashtables restruct locals ;
IN: fmachine

SINGLETON: unset

: make-register ( -- )
    [let | contents! [ unset ] |
        [ { "get" [ contents ]
            "set" [ contents! ]
            [ "Unkown request -- REGISTER " prepend throw ]
        } mycase ] ] ;

: make-stack ( -- stack )
    [let* | s! [ nil ]
            spush [ [ s cons s! ] ]
            spop [ [ s nil?
                     [ "Empty stack -- POP" throw ]
                     [ s [ car ] [ cdr ] bi s! ] if ] ]
            init [ [ nil s! ] ]
            | [ { "push" [ spush call ]
                  "pop" [ spop call ]
                  "init" [ init call ]
                  [ "Unknown request -- STACK " prepend throw ]
            } mycase ] ] ;

! send message
! experimenting with these two
: sm ( quot -- ) swap call ;
: sm1 ( quot -- ) rot call ;            

: mpop ( stack -- obj ) "pop" sm ;

: mpush ( obj stack -- ) "push" sm ;

: start ( machine -- ) "start" sm ;

: get-contents ( register -- obj ) "get" sm ;

: set-contents! ( obj register -- ) "set" sm ;

: get-reg ( machine reg-name -- ) "get-register" sm1 ;

: get-reg-conts ( reg-name machine -- ) get-register get-contents ;

: set-reg-conts ( obj reg-name machine -- ) "get-register" sm set-contents! ;

: <new-machine> ( -- machine )
            [let* | pc [ make-register ]
                    flag [ make-register ]
                    stack [ make-stack ]
                    instr-seq [ nil ]
                    ops [ { { "init-stack" [ stack "init" sm ] } } ]
                    reg-table [ H{ { "pc" pc } { "flag" flag } } ]
                    allocate-reg [ [ dup reg-table at
                                     [ "Multiply defined register: " prepend throw ]
                                     [ make-register swap reg-table set-at ] if ] ]
                    lookup-reg [ [ reg-table at
                                   [ "Unknown register: " prepend throw ]
                                   unless* ] ]
                    exec [ [ get-contents pc dup nil?
                             [ "done" ]
                             [ car instr-exec-proc exec [ call ] bi@ ]
                             if ] ]
                    | [ { "start" [ instr-seq pc set-content! exec call ]   ! check this
                          "install-instr-seq" [ instr-seq! ]
                          "allocate-reg" [ allocate-reg call ]
                          "get-register" [ lookup-reg call ]
                          "install-ops" [ ops append ops! ]  ! can we use push?
                          "stack" [ stack ]
                          "ops" [ ops ]
                          [ Unknown request -- MACHINE" prepend throw ] } mycase ] ] ;
            ] ] ] ]

                    
: assemble ( contoller-text machine -- )
    [ [ string? ] partition swap ] dip update-insts! ;


: update-insts! ( insts labels machine -- )
    '[ [ instr-text _ _ make-exec-proc ] keep set-instr-exec-proc! ] each ;

: make-exec-proc ( labels machine instr  -- quot )
    dup first
    { "assign"  [ make-assign ]
      "test"    [ make-test ]
      "branch"  [ make-branch ] 
      "goto"    [ make-goto ]
      "save"    [ make-save ]
      "restore" [ make-restore ]
      "perform" [ make-perform ]
      [ "Unknown instruction type -- ASSEMBLE " prepend throw ]
    } mycase ;

: make-assign ( labels machine instr -- quot )
    over
    [ assign-value-expr  
      dup operation-exp?
      [ make-operation-expr ]
      [ first make-primitive-expr ] if ] keep
      assign-reg-name get-register 
      '[ @ _ set-contents! ]                 ! this might involve "call" instead of @
    ] dip "pc" get-reg '[ @ _ advance-pc ] ;

: assign-reg-name ( assign-instr -- name ) second ;

: assign-value-expr ( assign-istr -- expr ) 2 tail ;

: advance-pc ( pc -- ) get-contents rest set-content! ;

: make-test ( labels machine instr -- quot )
    over 
    [ test-condition dup operation-exp?
      [ make-operation-expr ]
      [ "Bad TEST instruction -- ASSEMBLE" prepend throw ]
      if ] dip
      "flag" "pc" [ get-reg ] bi-curry@ bi
      '[ @ _ set-contents! _ advance-pc ] ;

: make-test1
    [ test-condition ]
    [ operation-exp? ] ! test 
    [ make-operation-exp ]     ! true 
    [ "Bad TEST instruction" ] ! false
    [ something reg ] make-X ;        ! set-register

MACRO: make-X ( accessor test quot1 quot2 register -- quot )
    '[ over
      [ @ dup @ 
        _ _ if
      ] dip
      _ "pc" [ get-reg ] bi-curry@ bi
      '[ @ _ set-contents! _ advance-pc ] ] ;

      
      
    
    
    

: test-condition ( test-instr -- ) rest ;

: make-branch ( labels machine instr -- quot )


  
      
      
      
    


: make-primitive-expr ( labels machine exp -- quot )
    {
    [ constant? ] [  constant-expr-value '[ _ ] 2nip ]        ! double check these accessors
    [ label-expr? ] [ label-expr-label lookup-labels '[ _ ] nip ] ! "
    [ register-expr? ] [ register-expr-reg get-register '[ _ get-contents ] nip ]
    } mycond ;

: make-operation-expr ( labels machine exp -- quot ) ;







               
             
           


                    


           

            

            
                  

        















! basic machine creation 
: <machine> ( registers instructions -- machine )
    H{ } V{ } [ clone ] bi@
    machine boa ;

! creates an unset register
: <register> ( name -- reg ) unset 2array ;

! what is an operation? a assoc of names to quots?
: <operation> ;

: <machine1> ( register-names ops controller-text  -- machine )
    [ { "pc" "flag" } append [ <register> ] map >hashtable ]
    [ [ <operation> ] map >hashtable ]
    [ assemble ] tri* <machine> ;

! instead of an object, we are going to implement
! the machine as a quotation that takes messages as
! arguments

: start ( machine -- ) ;

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

: make-execution-proc ( labels machine instr -- quot )
    dup first 
    { "assign" [ make-assign ]
      "test" [ make-test ]
      "branch" [ make-branch ]
      "goto" [ make-goto ]
      "save" [ make-save ]
      "restore" [ make-restore ]
      "perform" [ make-perform ]
      [ "Unknown instruction type" throw ]
    } case ;

: make-assign ( pc operations labels machine inst -- )
    [ assign-reg-name get-register ]  [ assign-value-exp ] bi
    dup operation-exp?
    [ make-operation ]     ! flesh out
    [ make-primitive ] if  ! flesh out
    swap [ set-content! advance-pc ] 2curry ;  ! advance-pc

: get-register ( machine name -- register ) ;

: assign-reg-name ( inst -- reg-name ) ;
    
    
                



      
      

      
      

  
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
