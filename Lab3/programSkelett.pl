verifyEasy(T, L, S, F):-
  check(T, L, S, [], F).
% For SICStus, uncomment line below: (needed for member/2)
%:- use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
see(Input), read(T), read(L), read(S), read(F), seen,
check(T, L, S, [], F).
% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S |- F
% U
% To execute: consult(’your_file.pl’). verify(’input.txt’).
% Literals
%check(_, L, S, [], X) :- ...
%check(_, L, S, [], neg(X)) :- ...
% And
%check(T, L, S, [], and(F,G)) :- ...
% Or
% AX
% EX
% AG
% EG
% EF
% AF

% Stödfunktion för AX. Kollar om check är legal för alla states vi kan gå till.
fullCheck(_, _, [], _, _).
fullCheck(T, L, [S|Rest], U, X)  :- 
check(T, L, S, U, X),
fullCheck(T, L, Rest, U, X).


% Regel1 Finns P i L? Formeln giltling i tillståndet S?

check(_, L, S, [], X) :- 
member([S,LS], L), % om 
member(X,LS).

% Regel2 Finns !P i L?

check(_, L, S, [], neg(X)) :- 
member([S,LS], L),
not(member(X,LS)).

% Regel3 Finns P&Q i L?

check(T, L, S, [], and(X,Y)) :- 
check(T, L, S, [], X),
check(T, L, S, [], Y).


% Regel4 Finns P|Q i L?

check(T, L, S, [], or(X,_)) :- 
check(T, L, S, [], X).

% Regel4 v2
check(T, L, S, [], or(_,X)) :- 
check(T, L, S, [], X).

% Regel5  AX. Alla nästa steg vi kan ta från sx innehåller x.  sx, ax(x)).
check(T, L, S, [], ax(X)) :- 
member([S,TS], T),       
fullCheck(T, L, TS,[], X).     % Skickar in en lista med states vi ska kolla

% Regel6  AG1.
check(_, _, S, U, ag(_)) :- 
member(S, U).


% Regel6  AG2.
check(T, L, S, U, ag(X)) :- 
not(member(S, U)),
check(T, L, S, [], X),
member([S,TS], T),       
fullCheck(T, L, TS,[S|U], ag(X)).


% Regel7 AF1. om s inte hör till U, om vi kan bevisa att phi gäller i stadiet S, så kan vi bevisa att vi i stadiet S kan bevisa att phi så småningom nås för alla vägar. För alla vägar, kommer X bli sann till slut. 
check(T, L, S, U, af(X)) :- 
not(member(S,U)),    % kolla så S inte är i U
check(T, L, S, [], X).  % kollar om det är sant att alla sätt vi kan gå leder till att det blir sant.

% [[s0, [p]],
% [s1, [p]],
% [s2, [p,q]]],

% Wherever we choose to go from s2, we will always arrive somewhere where P is true.

%Regel8 AF2. om den är sann för alla vägar vi kan ta.
check(T, L, S, U, af(X)) :- 
not(member(S,U)),    % kolla så S inte är i U
member([S,TS], T),       
fullCheck(T, L, TS,[S|U], af(X)).



% Regel9 EX. Ska kolla om det finns något (ETT) steg från S så att P blir sann.
check(T, L, S, [], ex(X)) :- 
member([S,TS], T),     
member(TE,TS),  
check(T, L, TE,[], X).


% Regel10 EG1 För Någon väg ska X vara sann för alla states.
check(_, _, S, U, eg(_)) :- 
member(S, U).

% Regel11 EG2 
check(T, L, S, U, eg(X)) :- 
not(member(S, U)),
check(T, L, S, [], X),
member([S,TS], T),     
member(TE,TS),  
check(T, L, TE,[S|U], eg(X)).



% Regel12 EF1 
check(T, L, S, U, ef(X)) :- 
not(member(S,U)),    % kolla så S inte är i U
check(T, L, S, [], X).


% Regel13 EF2 
check(T, L, S, U, ef(X)) :- 
not(member(S,U)),    % kolla så S inte är i U
member([S,TS], T),  
member(TE,TS),      
check(T, L, TE,[S|U], ef(X)).



/*
verify2([[s0, [s1, s0]],        T
 [s1, [s2, s0, s1]],
 [s2, [s1, s0]]],

[[s0, [p]],                     L
 [s1, [p]],
 [s2, [p,q]]],
        
 s2,    						S


  af(p)).						X     

  U - Currently recorded states   (börjar som tom, fylls på vid visits)            
*/ 