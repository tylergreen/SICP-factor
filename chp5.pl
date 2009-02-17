gcdm(machine([a,b,t],[b(rem, rem), b(=, =)],
	     [test-b,
	       test(op(=), reg(b), const(0)),
	       branch(label(gcd-done)),
	       assign(t,op(rem),reg(a),reg(b)),
	       assign(a,reg(b)),
	       assign(b,reg(t)),
	       goto(label(test-b))
	     gcd-done])).

make_machine(Description,M) :- % build a machine from description
set_reg(M,R,V,M1) :- % :- return a new machine
run(M,M1). :- % run the machine, output new machine
get_reg(M,R,V) :- 

	       
	   

	     
	
	


