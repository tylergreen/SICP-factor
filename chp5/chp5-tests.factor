USING: random math.functions grouping assocs tools.test sicp.chp5 lists accessors ;

{ 
    [ 0 ] 
    [ nil count-leaves-demo ]

    [ 1 ]
    [ 100 1list count-leaves-demo ]
    
    [ 2 ]
    [ 10 20 cons count-leaves-demo ]

    [ 3 ]
    [ "a" "b" "c" 3list count-leaves-demo ]

    [ t ]
    [ 10 8 ^ dup [ random ] bi@
      [ gcddemo ] [ gcd nip ] 2bi = ]

    [ { 1 1 2 6 24 120 720 5040 40320 362880 } ]
    [ 10 [ factdemo ] map ]

    [ { 0 1 1 2 3 5 8 13 21 34 55 89 144 233 377 } ]
    [ 15 [ fibdemo ] map ]

} 2 group [ unit-test ] assoc-each
