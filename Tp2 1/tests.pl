
:- begin_tests(nonograma).
:- ensure_loaded(nonograma).

test(matriz, [nondet]) :-
    matriz(2, 3, M),
    M =@= [[_, _, _], [_, _, _]].

test(replicar, [nondet]) :-
    replicar(_, 0, R),
    R =@= [].

test(replicar, [nondet]) :-
    replicar(x, 2, R),
    R =@= [x, x].

test(replicar, [nondet]) :-
    replicar(A, 3, R),
    R =@= [A, A, A].

test(transponer, [nondet]) :-
    transponer([[1]], 
               [[1]]).

test(transponer, [nondet]) :-
    transponer([[1, 2, 3], 
                [4, 5, 6]], 
               [[1, 4], 
                [2, 5], 
                [3, 6]]).

test(transponer, [nondet]) :-
    transponer([[1, 2, 3]], 
               [[1], 
                [2], 
                [3]]).

test(transponer, [nondet]) :-
    transponer([[1], 
                [2], 
                [3]],
               [[1, 2, 3]]).

test(pintadasValidas, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintadasValidas(r([], L)),
        [[o,o,o]]).

test(pintadasValidas, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintadasValidas(r([3], L)),
        [[x,x,x]]).

test(pintadasValidas, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintadasValidas(r([1], L)),
        [[o,o,x],[o,x,o],[x,o,o]]).

test(pintadasValidas, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintadasValidas(r([1,1], L)),
        [[x,o,x]]).

test(pintadasValidas, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintadasValidas(r([2,1], L)), 
        []).

test(pintadasValidas, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintadasValidas(r([2], L)), 
        [[x,x,o],[o,x,x]]).

test(resolverNaive, [nondet]) :-
    armarNono([[1],[1]], [[1],[1]], NN), NN=nono(M, _),
    soluciones(M, resolverNaive(NN), 
        [[[o,x], % solución A
          [x,o]],
         [[x,o], % solución B
          [o,x]]
        ]).

test(resolverNaive, [nondet]) :-
    nn(0, NN), NN=nono(M, _),
    soluciones(M, resolverNaive(NN), 
        [[[o,x,o], % única solución
          [o,x,x]]
        ]).

test(pintarObligatorias, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintarObligatorias(r([3], L)), 
        [[x,x,x]]).

test(pintarObligatorias, [nondet]) :-
    L = [_, _, _],
    soluciones(L, 
        pintarObligatorias(r([], L)), 
        [[o,o,o]]).

test(pintarObligatorias, [nondet]) :-
    L = [A, _, C],
    soluciones(L, 
        pintarObligatorias(r([2], L)), 
        [[A,x,C]]).

test(deducir1Pasada, [nondet]) :-
    armarNono([[2],[3],[2]], [[2],[3],[2]], NN), NN=nono(M, _),
    soluciones(M, deducir1Pasada(NN), 
        [[[_,x,_],
          [x,x,x],
          [_,x,_]]
        ]).

test(deducirVariasPasadas, [nondet]) :-
    % con deducir1Pasada no se resuelve del todo 
    nn(3, NN1), deducir1Pasada(NN1), cantidadVariablesLibres(NN1, NNV1), NNV1 > 0,
    % pero con deducirVariasPasadas puede resolverlo completamente
    nn(3, NN2), deducirVariasPasadas(NN2), cantidadVariablesLibres(NN2, 0).

test(restriccionConMenosLibres, fail) :-
    % si no hay restricciones con libres, falla.
    restriccionConMenosLibres(
        nono(_, [r([], [x]), 
                 r([], [o])
                ], _), _).

test(restriccionConMenosLibres, [nondet]) :-
    % NOTA: asume que ni la matriz, ni la restricción afectan el resultado.
    %       se usa la restricción como identificador.
    soluciones(R,
        restriccionConMenosLibres(
            nono(_, [r([2], [A,B]),
                     r([1], [x,x])
                    ]), R), 
        % la restricción resultante tiene que tener alguna variable libre
        % por eso r([1], [x,x]) no es el resultado correcto.
        [r([2], [A,B])]).

test(restriccionConMenosLibres, [nondet]) :-
    % NOTA: asume que ni la matriz, ni la restricción afectan el resultado.
    %       se usa la restricción como identificador.
    soluciones(R,
        restriccionConMenosLibres(
            nono(_, [r([1], [x,A]),
                     r([2], [_,_])
                    ]), R), 
        [r([1], [x,A])]).

test(restriccionConMenosLibres, [nondet]) :-
    % NOTA: asume que ni la matriz, ni la restricción afectan el resultado.
    %       se usa la restricción como identificador.
    soluciones(R,
        restriccionConMenosLibres(
            nono(_, [r([2], [_,_]),
                     r([1], [x,A])
                    ]), R), 
        [r([1], [x,A])]).

test(restriccionConMenosLibres, [nondet]) :-
    % NOTA: asume que ni la matriz, ni la restricción afectan el resultado.
    %       se usa la restricción como identificador.
    soluciones(R,
        restriccionConMenosLibres(
            nono(_, [r([1], [A,x]),
                     r([2], [x,B])
                    ]), R), 
        % Ambas restricciones tienen la misma cantidad de variables libres
        [r([1], [A,x]), 
         r([2], [x,B])
        ]).

test(resolverDeduciendo, [nondet]) :-
    nn(10, NN), NN=nono(M, _),
    findall(M, resolverDeduciendo(NN), MS),
    assertion(term_variables(MS, [])), % todas las soluciones están totalmente instanciadas
    sort(MS, SMS), length(SMS, SN),
    assertion(SN == 36), % tiene 36 soluciones distintas
    length(MS, N),
    assertion(N == 36). % no se listan soluciones repetidas

test(solucionUnica, [nondet]) :-
    nn(0, NN), solucionUnica(NN).

test(solucionUnica, fail) :-
    nn(10, NN), solucionUnica(NN).

% Similar a findall/3 pero compara con un conjunto 
% esperado independientemente del orden.
% Acepta soluciones parcialmente instanciadas, se comparan con =@=/2.
soluciones(L, G, S) :- 
    findall(L, G, LS), 
    msort(LS, LSS), 
    msort(S, SS),
    (LSS =@= SS;
     format('Esperado: ~w~nActual: ~w~n', [S, LS]),
     fail).

:- end_tests(nonograma).

