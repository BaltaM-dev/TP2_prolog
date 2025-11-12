:- set_prolog_flag(encoding, utf8).
:- set_stream(user_output, encoding(utf8)).

% Ejercicio 1
%! matriz(+F, +C, -M)
matriz(0, _, []).
matriz(F, C, [FILA| XS]) :- F > 0, length(FILA,C),  F2 is F - 1, matriz(F2,C, XS). 


% Ejercicio 2
replicar(_, 0, []).
replicar(X,N, [X | XS]) :- N > 0, N2 is N - 1, replicar(X,N2, XS).

% % Ejercicio 3

%iesimosElems(+I, +M,-R) r es res.
iesimosElems(_,[],[]).
iesimosElems(I,[M | MS],[R | RS]) :-
    nth1(I,M,R),
    iesimosElems(I,MS,RS).

transponerAux(0, _, []) :- !. %si no hay mas columnas :)
transponerAux(I, M, [R | RS]) :- %la armamos desde el fondo agregando adelante
    I > 0,
    iesimosElems(I, M, R),
    J is I-1,
    transponerAux(J, M, RS).

transponer([],[]).
transponer([M | MS],Re) :-
    length(M,Lc), %cant de columnas
    transponerAux(Lc,[M | MS],R),
    reverse(R,Re).



% % Predicado dado armarNono/3
armarNono(RF, RC, nono(M, RS)) :-
 	length(RF, F),
 	length(RC, C),
 	matriz(F, C, M),
 	transponer(M, Mt),
 	zipR(RF, M, RSFilas),
 	zipR(RC, Mt, RSColumnas),
 	append(RSFilas, RSColumnas, RS).

zipR([], [], []).
zipR([R|RT], [L|LT], [r(R,L)|T]) :- zipR(RT, LT, T).

% % Ejercicio 4

pintadasValidas(r(R, L)) :- auxiliar(R,L,0).


auxiliar([], L , _) :- length(L,N), replicar(o,N,L).

%caso en el que solo hay una restriccion, pruebo las distintas formas de pintar R celdas de negros en la fila L. 
% donde CantBl representa la cantidad de celdas pintadas de blanco al prinipio de la fila (se ubica entre Mb (minimo) y MaxMb), y luego R negras.
% los espacios sobrantes despues de eso se pintan de blanco
auxiliar([R],L,Mb) :-length(L,N), MaxMb is N - R, between(Mb,MaxMb, CantBl), 
					RestoBl is N - R - CantBl, RestoBl >= 0,
					replicar(o,CantBl,A1), replicar(x,R,A2), replicar(o, RestoBl, A3),
					append(A1,A2,A4), append(A4,A3,L).

% caso base donde hay mas de una restriccion, similar a lo anterior, pero ahora mientras mi cola de la lista no sea vacia, (para evitar soluciones repetidas)
% pinto CantBl blancas al principio, luego R negras, hago recursion sobre el Resto de la fila  que me falta pintar, obligando a que el minimo de pintadas blancas
% a poner entre una restriccion R y otra sea igual 1
auxiliar([R|Rs],L, Mb) :- Rs \= [], length(L,N), sum_list([R|Rs],S), MaxMb is N - S, 
						between(Mb,MaxMb, CantBl), RestoBl is N - R - CantBl, RestoBl >= 0,
						replicar(o,CantBl,A1), replicar(x,R,A2), 
						append(A1,A2,A3), length(L2, RestoBl), append(A3,L2,L),
						auxiliar(Rs,L2,1).


% % Ejercicio 5
resolverNaive(nono(_,NN)) :- maplist(pintadasValidas, NN).

% % Ejercicio 6

pintarObligatorias(r(Rest,L)) :-  
							pintarOblAux(Rest,L,L2), obligatorio(L2,L). 
% luego de calcular la lista de todas las posibles pintadas validas de la lista L para dicha restriccion (en OblAux),
% calculo las celdas que son iguales en todas esas posibles pintadas, lo que las obligatorias y las agrego a mi lista de retorno.

pintarOblAux(Restricciones,L,Res) :- copiarLista(L,Fila), findall(Fila, 
	pintadasValidas(r(Restricciones,Fila)),Res).

copiarLista([], []). 
copiarLista([E1|L1],[E1|L2]) :- copiarLista(L1,L2).

combinarFilas(F1,F2,R) :- maplist(combinarCelda, F1, F2, R). 

obligatorio([R],R). 	
obligatorio([H1,H2|Hs], Res) :- combinarFilas( H1, H2, Hi), obligatorio([Hi|Hs], Res).



% % Predicado dado combinarCelda/3
 combinarCelda(A, B, _) :- var(A), var(B).
 combinarCelda(A, B, _) :- nonvar(A), var(B).
 combinarCelda(A, B, _) :- var(A), nonvar(B).
 combinarCelda(A, B, A) :- nonvar(A), nonvar(B), A = B.
 combinarCelda(A, B, _) :- nonvar(A), nonvar(B), A \== B.

% % Ejercicio 7
deducir1Pasada(nono(_,Rs)) :- maplist(pintarObligatorias,Rs ).

% % Predicado dado
cantidadVariablesLibres(T, N) :- term_variables(T, LV), length(LV, N).

% % Predicado dado
deducirVariasPasadas(NN) :-
 	NN = nono(M,_),
 	cantidadVariablesLibres(M, VI), % VI = cantidad de celdas sin instanciar en M en este punto
 	deducir1Pasada(NN),
 	cantidadVariablesLibres(M, VF), % VF = cantidad de celdas sin instanciar en M en este punto
 	deducirVariasPasadasCont(NN, VI, VF).

% % Predicado dado
deducirVariasPasadasCont(_, A, A). 
deducirVariasPasadasCont(NN, A, B) :- A =\= B, deducirVariasPasadas(NN).

% % Ejercicio 8
restriccionConMenosLibres(nono(_,RS), R) :- 
	length(RS,P), 
	between(1,P,Itera), 
	nth1(Itera,RS,R), 
	cantidadVariablesLibres(R,N), 
	N>0,
	\+ ( between(1,P,Itera2), Itera =\= Itera2, nth1(Itera2,RS,R2), cantidadVariablesLibres(R2, M) , M > 0, M < N).
	
	% basicamente decimo que R es una restriccion de RS con al menos una variable libre y NO existe otra restriccion con menos variables libres que ella (por eso el uso del not)

		


% % Ejercicio 9
estaCompleto(nono(M,_)) :- cantidadVariablesLibres(M,0). % es como mi break, si me da true termine 


resolverDeduciendo(NN) :- deducirVariasPasadas(NN), resolverDeduciendoAux(NN). 

resolverDeduciendoAux(NN):- estaCompleto(NN), !.  
resolverDeduciendoAux(NN) :-
	restriccionConMenosLibres(NN, R), !,
	pintadasValidas(R), resolverDeduciendo(NN).


% % Ejercicio 10
solucionUnica(NN) :- findall(NN, resolverDeduciendo(NN),Res), length(Res,1).
/*
Ejercicio 11 


N  | Tamaño |  ¿ Tiene Solucion Unica ? | ¿Es Deducible Sin Backtraking ?
0  |   2x3 	|			Si 				|				Si 
1  |   5x5 	|			Si 				|				Si 
2  |   5x5 	|			Si 				|				Si 
3  |  10x10 |			Si 				|				Si 
4  |   5x5 	|			Si 				|				Si 
5  |   5x5 	|			Si 				|				No 
6  |   5x5 	|			Si 				|				Si 
7  |  10x10 |			Si 				|				Si 
8  |  10x10 |			Si 				|				Si 
9  |   5x5 	|			Si 				|				Si 
10 |   5x5 	|			No 				|				No 
11 |  10x10 |			Si 				|				Si 
12 |  15x15 |			Si 				|				Si 
13 |  11x5  |			Si 				|				No 
14 |   4x4 	|			Si 				|				No

Para calcular el tamaño de cada nono usamos la consulta,  ?-tamaño(N, (F,C)).  Probamos los nonos de 0<=N<=14 y usamos los siguientes predicados a continuacion:

tamaño(N, (F, C)) :- nn(N, nono(M, _)), matriz2(F, C, M).

matriz2(0,0,[]).
matriz2(F,C,[Fila|Xs]) :- length(Fila,C), length([Fila|Xs], F). --> similar al ej1 pero con la diferencia que F y C se pasan sin instanciar

Para calcular si tiene Solucion Unica usamos la consulta , ?-nn(N, NN) , solucionUnica(NN).  Probamos los nonos de 0<=N<=14

Para calcular si  es Deducible Sin Backtraking ?- nn(N, NN), deducirVariasPasadas(NN), cantidadVariablesLibres(NN, 0). Probamos los nonos de 0<=N<=14.
Si despues de aplicar varias pasadas el nonograma quedó completo, es decir no quedaron variables libres, quiere decir que se pudo resolver sin necesidad de explorar soluciones
alternativas usando el predicado resolverDeduciendo (el cual implementa backTracking)

*/

/* Ejercicio 12 
El segundo argumento no es reversible porque la segunda cláusula exige que N ya esté instanciado para poder chequear N > 0 y calcular N2 is N-1. 
Si N viene libre, esa cláusula no puede usarse y te quedás solo con el caso base.
Si N es variable, la cláusula recursiva no se puede usar y solo se obtiene la solución trivial del caso base (N=0, L=[]). Por lo tanto, la consulta 
replicar(+Elem, -N, -Lista) no genera todas las soluciones, y replicar(+Elem, -N, +Lista) falla salvo el caso Lista = [].
*/





% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% %                              %
% %    Ejemplos de nonogramas    %
% %        NO MODIFICAR          %
% %    pero se pueden agregar    %
% %                              %
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Fáciles
nn(0, NN) :- armarNono([[1],[2]],[[],[2],[1]], NN).
nn(1, NN) :- armarNono([[4],[2,1],[2,1],[1,1],[1]],[[4],[3],[1],[2],[3]], NN).
nn(2, NN) :- armarNono([[4],[3,1],[1,1],[1],[1,1]],[[4],[2],[2],[1],[3,1]], NN).
nn(3, NN) :- armarNono([[2,1],[4],[3,1],[3],[3,3],[2,1],[2,1],[4],[4,4],[4,2]], [[1,2,1],[1,1,2,2],[2,3],[1,3,3],[1,1,1,1],[2,1,1],[1,1,2],[2,1,1,2],[1,1,1],[1]], NN).
nn(4, NN) :- armarNono([[1, 1], [5], [5], [3], [1]], [[2], [4], [4], [4], [2]], NN).
nn(5, NN) :- armarNono([[], [1, 1], [], [1, 1], [3]], [[1], [1, 1], [1], [1, 1], [1]], NN).
nn(6, NN) :- armarNono([[5], [1], [1], [1], [5]], [[1, 1], [2, 2], [1, 1, 1], [1, 1], [1, 1]], NN).
nn(7, NN) :- armarNono([[1, 1], [4], [1, 3, 1], [5, 1], [3, 2], [4, 2], [5, 1], [6, 1], [2, 3, 2], [2, 6]], [[2, 1], [1, 2, 3], [9], [7, 1], [4, 5], [5], [4], [2, 1], [1, 2, 2], [4]], NN).
nn(8, NN) :- armarNono([[5], [1, 1], [1, 1, 1], [5], [7], [8, 1], [1, 8], [1, 7], [2, 5], [7]], [[4], [2, 2, 2], [1, 4, 1], [1, 5, 1], [1, 8], [1, 7], [1, 7], [2, 6], [3], [3]], NN).
nn(9, NN) :- armarNono([[4], [1, 3], [2, 2], [1, 1, 1], [3]], [[3], [1, 1, 1], [2, 2], [3, 1], [4]], NN).
nn(10, NN) :- armarNono([[1], [1], [1], [1, 1], [1, 1]], [[1, 1], [1, 1], [1], [1], [ 1]], NN).
nn(11, NN) :- armarNono([[1, 1, 1, 1], [3, 3], [1, 1], [1, 1, 1, 1], [8], [6], [10], [6], [2, 4, 2], [1, 1]], [[2, 1, 2], [4, 1, 1], [2, 4], [6], [5], [5], [6], [2, 4], [4, 1, 1], [2, 1, 2]], NN).
nn(12, NN) :- armarNono([[9], [1, 1, 1, 1], [10], [2, 1, 1], [1, 1, 1, 1], [1, 10], [1, 1, 1], [1, 1, 1], [1, 1, 1, 1, 1], [1, 9], [1, 2, 1, 1, 2], [2, 1, 1, 1, 1], [2, 1, 3, 1], [3, 1], [10]], [[], [9], [2, 2], [3, 1, 2], [1, 2, 1, 2], [3, 11], [1, 1, 1, 2, 1], [1, 1, 1, 1, 1, 1], [3, 1, 3, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 3, 1, 1], [3, 1, 1, 1, 1], [1, 1, 2, 1], [11], []], NN).
nn(13, NN) :- armarNono([[2], [1,1], [1,1], [1,1], [1], [], [2], [1,1], [1,1], [1,1], [1]], [[1], [1,3], [3,1,1], [1,1,3], [3]], NN).
nn(14, NN) :- armarNono([[1,1], [1,1], [1,1], [2]], [[2], [1,1], [1,1], [1,1]], NN).

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% %                              %
% %    Predicados auxiliares     %
% %        NO MODIFICAR          %
% %                              %
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% %! completar(+S)
% %
% % Indica que se debe completar el predicado. Siempre falla.
% completar(S) :- write("COMPLETAR: "), write(S), nl, fail.

%! mostrarNono(+NN)
%
% Muestra una estructura nono(...) en pantalla
% Las celdas x (pintadas) se muestran como ██.
% Las o (no pintasdas) se muestran como ░░.
% Las no instanciadas se muestran como ¿?.
mostrarNono(nono(M,_)) :- mostrarMatriz(M).

%! mostrarMatriz(+M)
%
% Muestra una matriz. Solo funciona si las celdas
% son valores x, o, o no instanciados.
mostrarMatriz(M) :-
	M = [F|_], length(F, Cols),
	mostrarBorde('╔',Cols,'╗'),
	maplist(mostrarFila, M),
	mostrarBorde('╚',Cols,'╝').

mostrarBorde(I,N,F) :-
	write(I),
	stringRepeat('══', N, S),
	write(S),
	write(F),
	nl.

stringRepeat(_, 0, '').
stringRepeat(Str, N, R) :- N > 0, Nm1 is N - 1, stringRepeat(Str, Nm1, Rm1), string_concat(Str, Rm1, R).

%! mostrarFila(+M)
%
% Muestra una lista (fila o columna). Solo funciona si las celdas
% son valores x, o, o no instanciados.
mostrarFila(Fila) :-
	write('║'),
	maplist(mostrarCelda, Fila),
	write('║'),
	nl.

mostrarCelda(C) :- nonvar(C), C = x, write('██').
mostrarCelda(C) :- nonvar(C), C = o, write('░░').
mostrarCelda(C) :- var(C), write('¿?').
