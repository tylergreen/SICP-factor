

{ a b temp }
{ { rem rem } { = = } }
{ test-b
    [ b 0 = test ]
    [ gcd-done branch ]
    [ a b rem temp assign ]
    [ b a assign ]
    [ temp b assign ]
    [ test-b goto ]
gcd-done } <machine>

{ a b temp }
{ { rem rem } { = = } }
{ test-b
    [ R{ b } 0 = test ]
    [ gcd-done branch ]
    [ R{ a } R{ b } rem temp assign ]
    [ R{ b } a assign ]
    [ R{ temp } R{ b } assign ]
    [ L{ test-b } goto ]
gcd-done } <machine>


{ a b temp }
{ { rem rem } { = = } }
{ test-b
    [ R{ b } 0 = test ]
    [ gcd-done branch ]
    [ { reg a } { reg b } rem temp assign ]
    [ { reg b } a assign ]
    [ R{ temp } R{ b } assign ]
    [ L{ test-b } goto ]
gcd-done } <machine>

Machine:
{ a b temp }
{ { rem rem } { = = } }
{ test-b
    [ [ b reg ]  0 = test ]
    [ gcd-done branch ]
    [ [ a reg ] [ b reg ] rem temp assign ]
    [ [ b reg ] a assign ]
    [ [ temp reg ]  b assign ]
    [ [ test-b label ] goto ]
gcd-done } ;

{ "a" "b" "temp" }
{ { rem rem } { = = } }
{ test-b
    [ [ b reg ]  0 = test ]
    [ gcd-done branch ]
    [ [ a reg ] [ b reg ] rem temp assign ]
    [ [ b reg ] a assign ]
    [ [ temp reg ]  b assign ]
    [ [ test-b label ] goto ]
gcd-done } ;


! 
: <machine> ( register-names ops controller-text  -- machine )
    [ [ <register> ] map ]
    [ [ <operation> ] map ]
    [ assemble ] tri
    machine new boa ;

TUPLE: machine regs ops instr-seq ;
        
        
        
    
    
    


