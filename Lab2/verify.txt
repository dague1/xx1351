verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

%chech that you have all premises and goal in proof

valid_proof(Prems, Goal, Proof) :-
	valid_goal(Goal, Proof),
	valid_lines(Prems,[], Proof).

valid_goal(Goal, [[_, X, _]]) :- X == Goal.		%check that goal is last segment in proof
valid_goal(Goal, [_|Lines]) :-
	valid_goal(Goal, Lines).
	
	
valid_lines(_,_,[]).		%check validity of each line
valid_lines(Prems,VProof, [Line|Lines]) :-	
	valid_line(Prems,VProof, Line),
	valid_lines(Prems,[Line|VProof], Lines).

 
valid_box(_,[]).
valid_box(VProof, [H|T]) :-
	valid_line(_,VProof, H),!,
	valid_box([H|VProof], T).  
	
valid_line(_,VProof, [H|T]) :- 
	H =[_N, _P, assumption],	
	valid_box([H|VProof], T).
	
valid_line(Prems, _, [_,X, premise]) :-
	member(X, Prems).
	
	
%implication elimination
valid_line(_,VProof, [_Ln3, Q, impel(Ln2,Ln1)]) :-
	member([Ln1, imp(P,Q), _], VProof),
	member([Ln2, P, _], VProof).

%MT
valid_line(_,VProof, [_Ln3, neg(P), mt(Ln1, Ln2)]) :-
	member([Ln1, imp(P,Q), _], VProof),
	member([Ln2, neg(Q), _], VProof).

%and elimination 1
valid_line(_,VProof, [_Ln2, P, andel1(Ln1)]) :-
	member([Ln1, and(P,_Q), _], VProof).

%and elimination 2
valid_line(_,VProof, [_Ln2, Q, andel2(Ln1)]) :-
	member([Ln1, and(_P,Q), _], VProof).

%and introduction
valid_line(_,VProof, [_Ln3, and(P,Q), andint(Ln1,Ln2)]) :-
	member([Ln1, P, _], VProof),
	member([Ln2, Q, _], VProof).

%or introduction 1
valid_line(_,VProof, [_Ln2, or(P,_Q), orint(Ln1)]) :-
	member([Ln1, P, _],VProof).

%or ntroduction 2
valid_line(_,VProof, [_Ln2, or(_P,Q), orint(Ln1)]) :-
	member([Ln1, Q, _],VProof).

%copy	
valid_line(_,VProof, [_Ln2, P, copy(Ln1)]) :-
	member([Ln1, P, _], VProof).

%double negation introdduction	
valid_line(_,VProof, [_Ln2, neg(neg(P)), negnegint(Ln1)]) :-
	member([Ln1, P, _],VProof).
	
%double negation elimination
valid_line(_,Proof, [_Ln2, P, negnegel(Ln1)]) :-
	member([Ln1, neg(neg(P)), _],Proof).
	
%LEM
valid_line(_,_Proof, [_Ln, or(P,neg(P)), lem]).

%negation elimination
valid_line(_,Proof, [_Ln3, cont, negel(Ln1,Ln2)]) :-
	member([Ln1, P, _], Proof),
	member([Ln2, neg(P), _], Proof).
	
%cont elimination
valid_line(_,Proof, [_Ln, _P, contel(Ln1)]) :-
	member([Ln1, cont, _], Proof). 

	
%implicaton introduction
valid_line(_,Proof, [_Ln3, imp(P,Q), impint(Ln1,Ln2)]) :-
	member([[Ln1, P, assumption]|_],Proof),
	member(List, Proof),member([Ln2, Q, _], List),
	valid_goal(Q, List).

%negation introduction
valid_line(_,Proof, [_Ln3, neg(P), negint(Ln1, Ln2)]) :-
	member([[Ln1, P, assumption]|_],Proof),
	member(List, Proof), member([Ln2, cont, _], List),
	valid_goal(cont, List).

%or elimination
valid_line(_,Proof,[_Ln, X, orel(Ln1,Ln2,Ln3,Ln4,Ln5)]) :-
	member([Ln1, or(P, Q), _], Proof),
    member(List1, Proof), member([Ln2, P, assumption], List1),
    member(List2, Proof), member([Ln3, X, _], List2),
	member(List3, Proof), member([Ln4, Q, assumption], List3),
    member(List4, Proof), member([Ln5, X, _], List4).

%PBC
valid_line(_,Proof, [_Ln, P, pbc(Ln1,Ln2)]) :-
	member([[Ln1, neg(P), assumption]|_],Proof),
	member(List, Proof), member([Ln2, cont, _], List),
	valid_goal(cont, List).	



