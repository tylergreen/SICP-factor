USING: utils kernel hashtables restruct locals fry sequences arrays lists lists.lazy assocs strings ;
IN: chp5

SINGLETON: unset

: <instr> ( text -- instr ) [ ] 2array ;
: instr-text ( instr -- text ) first ;                    
: instr-exec-proc ( inst -- code ) second ;
: set-instr-exec-proc! ( proc instr -- instr ) instr-text swap 2array ;

: make-register ( -- quot )
    [let | contents! [ unset ] |
        [ { "get" [ contents ]
            "set" [ contents! ]
            [ "Unkown request -- REGISTER " throw/m ]
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
                  [ "Unknown request -- STACK " throw/m ]
            } mycase ] ] ;


: operation-expr-op ( operation-expr -- op )
        first second ;

: operation-expr-operands ( operation-expr -- operands ) rest ;

: lookup-prim ( symbol operations -- quot )
        at dup
        [ second ]
        [ "Unknown operation -- ASSEMBLE " throw/m ]
        if ;

! send message
! experimenting with these two
: sm ( quot -- ) swap call ;
: sm1 ( quot -- ) rot call ;            

: mpop ( stack -- obj ) "pop" sm ;

: mpush ( obj stack -- ) "push" sm ;

: start ( machine -- ) "start" sm ;

: get-contents ( register -- obj ) "get" sm ;

: set-contents! ( obj register -- ) "set" sm ;

: get-reg ( machine reg-name -- reg ) "get-register" sm1 ;

: get-reg-conts ( reg-name machine -- obj ) get-reg get-contents ;

: set-reg-conts! ( obj reg-name machine -- ) "get-register" sm set-contents! ;


: assign-reg-name ( assign-instr -- name ) second ;

: assign-value-expr ( assign-istr -- expr ) 2 tail ;

: advance-pc ( pc -- ) get-contents rest set-contents! ;

: <new-machine> ( -- machine )
            [let* | pc [ make-register ]
                    flag [ make-register ]
                    stack [ make-stack ]
                    instr-seq! [ nil ]
                    ops! [ { { "init-stack" [ stack "init" sm ] } } ]
                    reg-table [ H{ { "pc" pc } { "flag" flag } } ]
                    allocate-reg [ [ dup reg-table at
                                     [ "Multiply defined register: " throw/m ]
                                     [ make-register swap reg-table set-at ] if ] ]
                    lookup-reg [ [ reg-table at
                                   [ "Unknown register: " throw/m ]
                                   unless* ] ]
                    exec [ [ pc [ get-contents ] lazy-map [ instr-exec-proc call ] each "done" ] ]
                    |  [ { "start" [ instr-seq pc set-contents! exec call ]   ! check this
                          "install-instr-seq" [ instr-seq! ]
                          "allocate-reg" [ allocate-reg call ]
                          "get-register" [ lookup-reg call ]
                          "install-ops" [ ops append ops! ]  ! can we use push?
                          "stack" [ stack ]
                          "ops" [ ops ]
                          [ "Unknown request -- MACHINE" throw/m ] } mycase ] ] ;

: tagged? ( seq tag -- bool )
     '[ _ swap first = ] [ array? ] swap bi-curry andq ;

: operation-expr? ( expr -- bool )
     [ sequence? ] [ "op" tagged? ] bi-curry andq ;

: constant ( expr -- bool ) "const" tagged? ;
                    
: make-primitive-expr ( labels machine expr -- quot )
    { [ constant? ] [ constant-expr-value 1q 2nip ]        ! double check these accessors
      [ label-expr? ] [ label-expr-label lookup-labels 1q nip ] ! "
      [ register-expr? ] [ register-expr-reg get-reg '[ _ get-contents ] nip ]
    } mycond ;
                    
: make-operation-expr ( labels machine expr -- quot )
        [ operation-expr-operands [ '[ _ _ make-primitive-expr ] ] dip swap map ] 2keep
        [ "ops" sm ] [ operation-expr-op ] bi* lookup-prim
        [ [ call ] map ] dip call ; ! be sure op is applied to list
                    
: make-assign ( labels machine instr -- quot )
    over
    [ assign-value-expr  
      dup operation-expr?
      [ make-operation-expr ]
      [ first make-primitive-expr ] if ] keep
      assign-reg-name get-reg 
      '[ @ _ set-contents! ]                 ! this might involve "call" instead of @
    ] dip "pc" get-reg '[ @ _ advance-pc ] ;

: make-test ( labels machine instr -- quot )
    over 
    [ test-condition dup operation-exp?
      [ make-operation-expr ]
      [ "Bad TEST instruction -- ASSEMBLE" throw/m ]
      if ] dip
    "flag" "pc" [ get-reg ] bi-curry@ bi
    '[ @ _ set-contents! _ advance-pc ] ;
                    

: make-branch ( labels machine instr -- quot )
    swap
    [ branch-dest dup label-expr?
      [ label-expr-label lookup-label ] 
      [ "Bad BRANCH instruction -- ASSEMBLE" throw/m ]
      if
    ] dip swap
    [ "flag" "pc" [ get-reg ] bi-curry@ bi ] dip
    '[ _ get-contents
       _ [ _ swap set-contents! ] [ advance-pc ] bi-curry ] ;

: branch-dest ( branch-instr -- ) second ;

: make-goto ( labels machine instr -- quot )
    goto-dest
    { [ label-expr? ] [ label-expr-label swapd lookup-label
                       [ "pc" get-reg ] dip '[ _ _ set-contents! ] ]
      [ register-expr? ] [ register-expr-reg "pc" [ get-reg ] bi-curry@ bi 
                           '[ _ _ set-contents! ] nip ]
      [ "Bad GOTO instr -- ASSEMBLE " throw/m ]
    } mycond ;  ! is this the right conditional?

: goto-dest ( goto-instr -- ) second ;

: make-save ( labels machine instr -- )
    [ drop ] 2dip
     stack-instr-reg-name "stack" "pc" 3array
     [ get-reg ] with each                       ! "with" might not be correct
    '[ _ get-contents _ push _ advance-pc ] ;

: make-restore ( labels machine instr -- )
    [ drop ] 2dip
      stack-instr-reg-name "stack" swap "pc" 3array
      [ get-reg ] with each                      ! "with" might not be correct
    '[ _ pop _ set-contents! _ advance-pc ] ;

: make-perform ( labels machine instr -- )
    over
    [ perform-action dup operation-exp?
      [ make-operation-expr 1q ]
      [ "Bad Perform instruction -- ASSEMBLE " throw/m ]
      if 
    ] dip "pc" get-reg '[ @ _ advance-pc ] ; ! not sure if exception is in the right place

: perform-action rest ;
  
: make-test1
    [ test-condition ]
    [ operation-expr? ] ! test 
    [ make-operation-expr ]     ! true 
    [ "Bad TEST instruction" ] ! false
    [ something reg ] make-X ;        ! set-register

! these accessors should be automatically generated
: test-condition ( test-instr -- ) rest ;

: make-branch ( labels machine instr -- quot )

                   
: make-exec-proc ( labels machine instr  -- quot )
    dup first
    { "assign"  [ make-assign ]
      "test"    [ make-test ]
      "branch"  [ make-branch ] 
      "goto"    [ make-goto ]
      "save"    [ make-save ]
      "restore" [ make-restore ]
      "perform" [ make-perform ]
      [ "Unknown instruction type -- ASSEMBLE " throw/m ]
    } mycase ;

                    
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
{ "a" "b" "temp" }
{ { "rem" [ rem ] } { "=" [ = ] } }
{ "test-b"
  { "b" "reg" 0 "=" "test" }
  { "gcd-done" "branch" }
  { "a" "reg" "b" "reg"  "rem" "op" "temp" "assign" }
  { "b" "reg" "a" "assign" }
  { "temp" "reg" "b" "assign" }
  { "test-b" "label" "goto" }
"gcd-done" } <machine> ;
