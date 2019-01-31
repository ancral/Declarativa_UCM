-- PRACTICA LOGICA PROPOSICIONAL
-- Ángel Cruz Alonso - 3A

type Var = String -- nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp

f1 = Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q"))))
f2 = Y (V "p") (Si (No (V "q")) (No (V "p")))
f3 = Y (V "p") (Y (V "q") (O (No (V "q")) (V "r")))
f4 = Si (No (O (V "p") (V "q"))) (Si (V "p") (V "r"))
f5 = Sii (No (O (V "p") (V "q"))) (Si (V "p") (V "r"))

-- Parte A -----------------------------------
--vars: vars f calcula una lista con los nombres de las variables proposicionales que hay en f, sin
--repeticiones (aunque el orden es irrelevante). Por ejemplo, vars f1 debe evaluarse a ["p","q"].

vars::FProp -> [Var]
varsAux::FProp  -> [Var]
noRepetidos::[Var] -> [Var]

--Llamamos a noRepetidos para que elimine los repetidos de la lista de variables
vars f = noRepetidos (varsAux f)

varsAux (V a)      = [a]
varsAux (No f)     = varsAux f
varsAux (Y f f')   = varsAux f ++ varsAux f'
varsAux (O f f')   = varsAux f ++ varsAux f'
varsAux (Si f f')  = varsAux f ++ varsAux f'
varsAux (Sii f f') = varsAux f ++ varsAux f'

noRepetidos [] = []
noRepetidos (x:xs)
    | elem x xs = noRepetidos xs
    | otherwise = x:noRepetidos xs

-- Parte B -----------------------------------------
--tautologia: reconoce si una fórmula es una tautologı́a o no, es decir, si es cierta para valores de
--verdad cualesquiera (True o False) de sus variables proposicionales.

tautologia::FProp -> Bool
resolver::[(Var,Bool)] -> FProp -> Bool
generarPosib::[Var] -> [[(Var,Bool)]]
buscarEnLista::Var -> [(Var,Bool)] -> (Var,Bool)
listaBools :: Int -> [[Bool]]

--Para saber si todas las conclusiones salen True, haremos un foldl, donde usaremos un &&
-- y la lista a recorrer sera la de las conclusiones que han salido

-- <resolver>, sera una funcion que resuelva la formula con una fila de la tabla de verdad.
-- <generarPosib>, sera una funcion que coja las variables de la formula y te devuelva una lista de listas de duplas
--              (x,y) donde 'x' es la variable e 'y' el valor bool que se le asigna.
--              Con esto generamos todas las combinaciones posibles para un determinado numero de variables.
--
--              Ejemplo: si tenemos las variables "a" y "b", generarPosib devolvera:
--              [[("a",True),("b",True)],[("a",True),("b",False)],[("a",False),("b",True)],[("a",False),("b",False)]]
--
---				 a   |   b
---			    -----------
---              T   |  T
---				 T	 |	F
---				 F	 |  T
---              F   |  F
---
---
tautologia f = foldl (&&) True [ resolver listaPosib f | listaPosib <- generarPosib (vars f) ]

-- <generarPosib>, entonces aqui hacemos lo que hemos dicho antes, generamos una lista donde venga cada fila de la tabla
--                 de verdad, entonces para falicitar despues el encontrar que valor le corresponde a la variable
--                 emparejamos cada variable con su correspondiente valor de la fila.
generarPosib vars = [zip vars fila | fila <- listaBools (length vars)]

-- <listaBools>, sera la funcion que genere todos las filas de la tabla de verdad con un determinado numero.
--               Este numero sera el numero de variables existentes, asi generaremos todas las combinaciones posibles.
--
--               /        \
--				/          \
--			   T            F
--		  (:) / \(:)    (:)/ \(:)
--           /   \        /   \
--          T     F      T     F
--          |(:)  |(:)   |(:)  |(:)
--			|     |      |     |
--		   [[]]  [[]]   [[]]  [[]]

--        Ese esquema simboliza un poco "como se formaria" si n = 2, todas las combinaciones para esa n
--

listaBools 0 = [[]]
listaBools n = do
    bool <- [True,False]
    map (bool :) (listaBools (n - 1))

-- <buscarEnLista>, sera la funcion necesaria a la hora de sustituir una variable por un valor bool.
--                  Buscamos por el primero valor de la dupla, cuando lo encontremos, devolvemos la dupla completa.
buscarEnLista a [] = error ("La variable " ++ a ++ " no se encuentra en la lista, revise si la formula esta correcta. \n"
                            ++ "Recuerde que si haces 'consecuncia' o 'equivalencia' las dos formulas tienen que tener las mismas variables")
buscarEnLista a (x:xs)
    | a == fst x = x
    | otherwise = buscarEnLista a xs

-- <resolver>, una aclaracion de resolver seria la parte de 'resolver lista (V a) = snd $ buscarEnLista a lista'.
--             Aqui lo que hacemos es teniendo ya la dupla completa de esa variable, conseguimos el valor correspondiente
resolver lista (V a) = snd $ buscarEnLista a lista
resolver lista (No f) = not $ resolver lista f
resolver lista (Y f f') = resolver lista f && resolver lista f'
resolver lista (O f f') = resolver lista f || resolver lista f'
resolver lista (Si f f') = if resolver lista f then resolver lista f' else True
resolver lista (Sii f f') = resolver lista f == resolver lista f'

-- Parte C -----------------------------------------
--satisfactible: reconoce si una fórmula es una satisfactible o no, es decir, si es cierta para algunos
--valores de verdad de sus variables proposicionales.
satisfactible :: FProp -> Bool

-- <satisfactible>, como esta vez solo queremos que alguna se cumpla, usaremos un ||
satisfactible f = foldl (||) False [ resolver listaPosib f | listaPosib <- generarPosib (vars f) ]

-- Parte D -----------------------------------------
--consecuencia: reconoce si una fórmula φ1 es consecuencia lógica de otra φ2 , es decir, si para valores de verdad cualesquiera de las variables proposicionales, cuando φ2 es cierta φ1 lo es también.
consecuencia :: FProp -> FProp -> Bool

-- <consecuencia>, se tiene que cumplir que φ1 --> φ2 (f --> f')
consecuencia f f' = foldl (&&) True [ resolver listaPosib (Si f f') | listaPosib <- generarPosib (vars (Si f f'))]

-- Parte E -----------------------------------------
--equivalente: reconoce si dos fórmulas φ1 y φ2 son lógicamente equivalentes, es decir, si para valores de verdad cualesquiera de las variables proposicionales, cuando φ2 es cierta φ1 lo es también.
equivalente :: FProp -> FProp -> Bool

-- <equivalente>, se tiene que cumplir que φ1 <--> φ2 (f <--> f')
equivalente f f' = foldl (&&) True [ resolver listaPosib (Sii f f') | listaPosib <- generarPosib (vars (Sii f f'))]

-- Parte F -----------------------------------------
--consecuencias: dada una lista fs de fórmulas, consecuencias fs es una lista con cada fórmula f de fs emparejada con la lista de aquellas fórmulas de fs que son consecuencia lógica de f.
consecuencias :: [FProp] -> [(FProp,FProp)]
consecuenciasAux :: [FProp] -> [FProp] -> [(FProp,FProp)]

-- <consecuencias>, en esta funcion usaremos una auxiliar, en la cual se le pasara la lista dos veces.
consecuencias fs = consecuenciasAux fs fs

-- <consecuenciasAux>, esta funcion devolvera una dupla (un emparejamiento) de (f,x), donde x es consecuencia de f.
--                     xs es fija, ya que la necesitamos para recorrer la lista de formulas desde el principio.
consecuenciasAux [] xs = []
consecuenciasAux (f:fs) xs = [(f,x) | x <- xs , consecuencia f x] ++ consecuenciasAux fs xs

-- Parte G -----------------------------------------
--equivalentes: dada una lista fs de fórmulas, equivalentes fs es el conjunto cociente de fs por
--la relación de equivalencia lógica, es decir, es una partición de fs en sublistas, cada una de las
--cuales está formada por fórmulas de fs equivalentes entre sı́.
equivalentes :: [FProp] -> [[FProp]]

-- <equivalentes>, esta funcion devolvera una lista de listas de formulas que son equivalentes entre si.
equivalentes []     = []
equivalentes (f:fs) = [f : [x | x <- fs , equivalente f x]] ++ equivalentes fs

-- Parte H -----------------------------------------

-- Para saber si son iguales, tienen que tener las mismas variables uno y otro, y que sean equivalentes.
instance Eq FProp where
    f == f' = (equivalente f f' && comparacionVariables (vars f) (vars f') && comparacionVariables (vars f') (vars f))     where
              comparacionVariables [] fs' = True
              comparacionVariables (f:fs) fs' = elem f fs' && comparacionVariables fs fs'

-- Para saber si f < f' (pongo <= porque me daba un warning con <), f' tendra que ser consecuencia de f.
instance Ord FProp where
    f <= f' = consecuencia f f'

-- Para poder mostrar cada componente, tenemos que establecer unos parentesis y hacer una concatenacion del simbolo
-- que representa ese componente y sus formulas internas, todo esto hasta llegar a las variables.
instance Show FProp where
    show (V x) = x
    show (No (V x)) = "~" ++ x
    show (No f) = "~" ++ "(" ++ show f ++ ")"
    show (Y f f') = "(" ++ show f ++ ")" ++ " ^ " ++ "(" ++ show f' ++ ")"
    show (O f f') = "(" ++ show f ++ ")" ++ " v " ++ "(" ++ show f' ++ ")"
    show (Si f f') = "(" ++ show f ++ ")" ++ " --> " ++ "(" ++ show f' ++ ")"
    show (Sii f f') = "(" ++ show f ++ ")" ++ " <--> " ++ "(" ++ show f' ++ ")"

-- PARTE OPCIONAL -------------------------------------
-- Programar una pequeña interacción con el usuario, de modo que se pida al usuario que introduzca las
-- fórmulas, se le pregunte en un sencillo menú qué quiere hacer con ellas y muestre el resultado de lo pedido.
-- El formato y procedimiento concreto para esta interacción se deja a criterio del programador.

-- <parsear>, solamente lo que hace es llamar a parsearAux, y quita el primero y ultimo parentesis.
--            Por eso es importante poner siempre los parentesis.
parsear :: String -> FProp
parsear formula = parsearAux (tail(init formula))

-- <parsearAux>, es la funcion que se encargara en saber:
--               Primero, si esa formula en su interior tiene una negacion o es directamente la variable,
--               Segundo, si no es asi, lo que hara es pasarle a parsearAux' la primera subformula y el resto del string
--                        que forma la formula en si.
parsearAux :: String -> FProp
parsearAux (x:xs)
    | (xs == []) = (V [x])
    | (x == '~') = (No (parsear xs))
    -- Aqui lo que hace es del string entero de la formula, coger por un lado la primera subformula como primer parametro
    -- y como segundo (gracia al drop) el resto de la formula.
    | otherwise = parsearAux' subformula1 (drop ((length subformula1) -1) xs) where subformula1 = equilibrioParentesis xs 1 [x]

-- <parsearAux'>, es la funcion que empezara a comprobar y establecer formulas que tienen en su interior 2 subformulas.
parsearAux' :: String -> String -> FProp
parsearAux' [] xs = error "Escriba bien la formula"
parsearAux' ys [] = error "Escriba bien la formula"
parsearAux' subformula1 (r:resto)
    | (r == '-') = (Si (parsear subformula1) (parsear (drop (2) resto)))
    | (r == '<') = (Sii (parsear subformula1) (parsear (drop (3) resto)))
    | (r == '^') = (Y (parsear subformula1) (parsear resto))
    | (r == 'v') = (O (parsear subformula1) (parsear resto))
    | otherwise = error ("Escriba bien la formula, no se reconoce el simbolo: "++[r])

-- <equilibrioParentesis>, es la funcion que se encargara en coger solamente hasta la primera subformula.
--                         Pongo un ejemplo por si no queda claro, si tenemos ((~(p))^(q)) la primera subformula seria
--                         (~(p)) y la segunda (q). Lo que hace es empezar a contar parentesis, cuando cuente un parentesis
--                         abierto '(' sumara 1 a un contador, si encuentra uno cerrado ')' restara 1.
--                         Esto hara que solamete coja (~(p)) ya que cuando llegue a 0, se devolvera esa subformula.
equilibrioParentesis :: String -> Int -> String -> String
equilibrioParentesis [] _ _ = error "Error: revise los parentesis de la formula o escriba variables de una letra \n"
equilibrioParentesis xs 0 ys = ys
equilibrioParentesis (x:xs) n ys
    | (x=='(') = equilibrioParentesis xs (n+1) (ys++[x])
    | (x==')') = equilibrioParentesis xs (n-1) (ys++[x])
    | otherwise = equilibrioParentesis xs n (ys++[x])

stringAint :: String -> Int
stringAint x = read x :: Int


-- <opciones>, es una funcion necesaria para saber que opcion eligio el usuario.
--             Dentro de acada opcion posible, se le pregunta que formula quiere (tiene que estar ese numero en la lista)
--             y despues, simplemente, se aplica lo que haya elegido a la formula X dentro de la lista de formulas
opciones :: String -> [FProp] -> IO()
opciones n formulas
    | n == "1" = do putStr ("¿Que formula quieres saber si es tautologia? (>= 0) ")
                    f <- getLine
                    let pos = stringAint f
                    putStr ("\n[[[---f"++f++" es una tautologia: " ++ (show (tautologia (formulas!!pos)))++"---]]]\n")
    | n == "2" = do putStr ("¿Que formula quieres saber si es satisfacible? (>= 0) ")
                    f <- getLine
                    let pos = stringAint f
                    let formula = formulas!!pos
                    putStr ("\n[[[---"++ show formula ++"(f"++f++") es satisfacible: " ++ (show (satisfactible formula))++"---]]]\n")
    | n == "3" = do putStr ("Elige la primera formula (>= 0) ")
                    f1 <- getLine
                    let pos1 = stringAint f1
                    putStr ("Elige la segunda formula (>= 0) ")
                    f2 <- getLine
                    let pos2 = stringAint f2
                    putStr ("\n[[[---f"++f1++" y f"++f2++" es equivalente: " ++ (show (equivalente (formulas!!pos1) (formulas!!pos2)))++"---]]]\n")
    | n == "4" = do putStr ("Elige la primera formula (>= 0) ")
                    f1 <- getLine
                    let pos1 = stringAint f1
                    putStr ("Elige la segunda formula (>= 0) ")
                    f2 <- getLine
                    let pos2 = stringAint f2
                    putStr ("\n[[[---f"++f1++" es consecuencia de f"++f2++": " ++ (show (consecuencia (formulas!!pos1) (formulas!!pos2)))++"---]]]\n")
    | n == "5" = putStr ("\n[[[---Consecuencias: " ++ show (consecuencias formulas) ++"---]]]\n")
    | n == "6" = putStr ("\n[[[---Equivalentes: " ++ show (equivalentes formulas) ++"---]]]\n")
    | n == "7" = putStr "\n[[[Saliendo...]]] \n \n"
    | otherwise = error "\n[[[Opcion incorrecta, saliendo...]]] \n \n"

opciones' :: String -> [FProp] -> IO()
opciones' n formulas
    | n == "1" = opcion1
    | n == "2" = opcion2 formulas
    | otherwise = error "[[[Opcion incorrecta, saliendo...]]] \n"

-- Las formulas se tienen que escribir como se comenta aqui abajo, pero pondre unos cuantos mas ejemplos.
-- Una negacion de 'p' seria asi: (~(p)), la variable 'q' asi: (q), un disyuncion de 'p' y 'q' asi: ((p)v(q)).
-- Cuidado con los parentesis, tambien lo pongo abajo, pero si falta un parentesis de la formula, directamente fallara .
main = do putStr "/////////// B I E N V E N I D O //////////////////////////////////////// \n"
          putStr "A la hora de introducir las formulas, introducelas sin espacios, que cada subformulas esten entre parentesis y que las varibles que tengan una longitud 1 \n"
          putStr " , si no, dara error. Ejemplos: ((~(p))^(q)), ((p)-->(r)) \n \n"
          putStr "Negacion ~  \n"
          putStr "Conjuncion ^  \n"
          putStr "Disyuncion v  \n"
          putStr "Implicacion -->  \n"
          putStr "Doble implicacion <-->  \n  \n"
          putStr "Para mas info mire los comentarios del codigo fuente \n"
          putStr "//////////////////////////////////////////////////////////////////////// \n"
          opcion1

-- <opcion1>, es necesaria para poder llamarla cuando el usuario escoja la opcion: 1. Poner formulas nuevas
opcion1 :: IO()
opcion1 = do putStr "¿Cuantas formulas vas a meter? "
             x <- getLine
             let num = stringAint x
             leerFormula 0 ([]) num

-- <leerFormula>, es una funcion que recibe un contador, una lista vacia y el numero de funciones que va a leer
leerFormula :: Int -> [FProp] -> Int -> IO()
leerFormula cont xs num
    | cont == num = opcion2 xs
    | otherwise = do putStr ("Introduzca la formula " ++ show cont ++ ": ")
                     formula <- getLine
                     leerFormula (cont+1) (xs ++ [(parsear (formula))]) num

-- <mostrarFormulas>, es una funcion que simplemente muestra la formulas que estan en la lista
mostrarFormulas :: [FProp] -> Int -> IO()
mostrarFormulas [] n = do putStr "\n"
mostrarFormulas (x:xs) n = do putStr (show x ++ " |||| Formula "++ show n)
                              putStr "\n"
                              mostrarFormulas xs (n+1)

-- <opcion2>, es necesaria para poder llamarla cuando el usuario escoja la opcion: 2. Volver al anterior menu
opcion2 :: [FProp] -> IO()
opcion2 formulas =          do putStr ("\n||||||||| F O R M U L A S |||||||||||" ++ "\n")
                               mostrarFormulas formulas 0
                               putStr ("\n|||||||||||| M E N U ||||||||||||||||" ++ "\n")
                               putStr ("1. Ver si una formula es una tautologia" ++ "\n")
                               putStr ("2. Ver si una formula es satisfacible" ++ "\n")
                               putStr ("3. Ver si dos formula son equivalentes" ++ "\n")
                               putStr ("4. Ver si una formula es consecuencia de otra" ++ "\n")
                               putStr ("5. Ver consecuencias" ++ "\n")
                               putStr ("6. Ver equivalentes" ++ "\n")
                               putStr ("7. Salir" ++ "\n")
                               putStr ("Elija una de las opciones anteriores: ")
                               opcion <- getLine
                               let a = opciones opcion formulas in a
                               if opcion /= "7"
                                   then do  putStr ("|||||||||||||||||||||||||||||||||||||" ++ "\n")
                                            putStr ("1. Poner formulas nuevas \n")
                                            putStr ("2. Volver al anterior menu \n")
                                            putStr ("Elija una de las opciones anteriores: ")
                                            opcion <- getLine
                                            let a = opciones' opcion formulas in a
                               else return ()
