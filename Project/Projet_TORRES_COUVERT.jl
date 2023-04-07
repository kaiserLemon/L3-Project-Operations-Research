#= 
ANDY TORRES 
COUVERT NICOLAS
=#

using JuMP, GLPK


######  PARTIE 1, SOLVEUR Miller-Tucker-Zemlin #####

# Fonction spécifiant les paramètres du modele m pour la méthode de résolution Miller-Tucker-Zemlin
# On a en entrée une matrice C, la matrice des distances entre chaque points
function resolutionMTZ(solverSelected::DataType, C::Matrix{Int64})
    m::Model = Model(solverSelected)
    n::Int64 = size(C, 1)   #C étant une matrice carré, on pourrait aussi prendre size(C,2), on prend son nombre de lignes/colonnes

    @variable(m, t[2:n] >= 0)
    @variable(m, x[1:n, 1:n] >= 0, binary = true)

    @objective(m, Min, sum(sum(C[i, j] * x[i, j] for j = 1:n) for i = 1:n))

    @constraint(m, somme1[j = 1:n], sum(if (i == j) 0 * x[i, j] else x[i, j] end for i = 1:n) == 1)
    @constraint(m, somme2[i = 1:n], sum(if (i == j) 0 * x[i, j] else x[i, j] end for j = 1:n) == 1)
    @constraint(m, temps1[i = 2:n, j = 2:n], t[i] - t[j] + (n * x[i, j]) <= n - 1)

    return m
end


######  PARTIE 2, SOLVEUR Dantzig-Fulkerson-Johnson #####

# Fonction spécifiant les paramètres du modele m pour la méthode de résolution Dantzig-Fulkerson-Johnson
# On a en entrée une matrice C, la matrice des distances entre chaque points
function resolutionDFJ(solverSelected::DataType, C::Matrix{Int64})
    m::Model = Model(solverSelected)
    n::Int64 = size(C, 2)

    @variable(m, x[1:n, 1:n] >= 0, binary = true)

    @objective(m, Min, sum(sum(C[i, j] * x[i, j] for j = 1:n) for i = 1:n))

    @constraint(m, somme1[j = 1:n], sum(x[i, j] for i = 1:n) - x[j, j] == 1)
    @constraint(m, somme2[i = 1:n], sum(x[i, j] for j = 1:n) - x[i, i] == 1)

    return m
end


# fonction qui prend en paramètre un fichier contenant un distancier et qui retourne le tableau bidimensionnel correspondant
function parseTSP(nomFichier::String)
    # Ouverture d'un fichier en lecture
    f::IOStream = open(nomFichier, "r")

    # Lecture de la première ligne pour connaître la taille n du problème
    s::String = readline(f) # lecture d'une ligne et stockage dans une chaîne de caractères
    tab::Vector{Int64} = parse.(Int64, split(s, " ", keepempty = false)) # Segmentation de la ligne en plusieurs entiers, à stocker dans un tableau (qui ne contient ici qu'un entier)
    n::Int64 = tab[1]

    # Allocation mémoire pour le distancier
    C = Matrix{Int64}(undef, n, n)

    # Lecture du distancier
    for i = 1:n
        s = readline(f)
        tab = parse.(Int64, split(s, " ", keepempty = false))
        for j = 1:n
            C[i, j] = tab[j]
        end
    end

    # Fermeture du fichier
    close(f)

    # Retour de la matrice de coûts
    return C
end

# Fonction renvoyant un boolean, servant à verifier la présence d'un élement dans un Vecteur à 2 dimensions
function Exist(val::Int64, tableau::Vector{Vector{Int64}})
    n::Int64 = length(tableau)
    m::Int64 = 0

    i::Int64 = 1

    while i <= n    #boucle servant au parcours du tableau sur une dimension
        m = length(tableau[i])
        j::Int64 = 1
        while j <= m    #parcours sur la deuxieme, on parcours tout le tableau
            if (tableau[i][j] == val)
                return true     #si on trouve la valeur choisie, on renvoie true et on stop la fonction
            end
            j = j + 1
        end
        i = i + 1
    end
    return false        #si on a pas stoppé, on a donc pas trovué la valeur, on retourne false
end

# Fonction prenant en entrée un vecteur de tuples d'entier, et renvoyant un vecteur de vecteur, contenant les cycles induit par le vecteur en entrée
function Cycles(X::Vector{Tuple{Int64,Int64}})
    n::Int64 = length(X)
    i::Int64 = 0
    courrant::Tuple{Int64,Int64} = (0, 0)
    tab::Vector{Int64} = Vector{Int64}(undef, n)    
    #tab sera un vecteur ayant à chaque positon i, la valeur j de l'endroit lié, exemple avec un tuple (5,4), on aura en position 5 la valeur 4


    while i < n     #boucle servant à remplir tab
        i = i + 1
        courrant = X[i]
        tab[courrant[1]] = courrant[2]
    end

    tableau::Vector{Vector{Int64}} = []     #tableau sera le vecteur de vecteur contenant les cycles
    nbCycles::Int64 = 0
    i = 1


    #on parcourt tab, on prend les indices et les valeurs contenues et on les ajoute dans un vecteur de "tableau"
    #quand on a arrive à quelque chose qu'on a déjà dans tableau, on a fini un cycle et on recommence, en ajoutant dans un nouveau vecteur

    while (i <= length(tab) - 1)    
        nbCycles = nbCycles + 1
        push!(tableau, [])

        while (Exist(tab[i], tableau) && i < length(tab))
            i = i + 1
        end

        valeur::Int64 = tab[i]
        if !(Exist(valeur, tableau))
            push!(tableau[nbCycles], valeur)
        end
        while !(Exist(tab[valeur], tableau))
            valeur = tab[valeur]
            if !(Exist(valeur, tableau))        #ce if sert à ne pas avoir de doublon, sinon on aurait deux fois la 1ere valeur qu'on trouve aussi à la fin
                push!(tableau[nbCycles], valeur)
            end
        end
    end

    pop!(tableau)       #sans cette ligne, on a aussi un vecteur vide en trop
    return tableau
end

# Cette fonction prend en entrée un vecteur de vecteur, et retourne le vecteur avec la taille la plus petite
function PlusPetit(X::Vector{Vector{Int64}})    
    n::Vector{Int64} = []
    min::Int64 = typemax(Int)

    for x in X  #parcours de X, le vecteur de vecteur
        if (length(x) <= min)
            min = length(x)
            n = x
        end
    end

    return n
end

# Cette fonction sert à choisir selon un booleen et un entier, quel fichier on va lire
# si plat_relief == true alors on choisi un fichier "plat", sinon on choisi un fichier "relief"
function choisPlatRelief(nb::Int64, plat_relief::Bool) 
    if (plat_relief)
        file::String = "plat/plat$nb.dat"
        println("Instance à résoudre : plat$nb.dat")
        C::Matrix{Int64} = parseTSP(file)
        return C
    else
        file2::String = "relief/relief$nb.dat"
        println("Instance à résoudre : relief$nb.dat")
        C2::Matrix{Int64} = parseTSP(file2)
        return C2
    end
end

# Fonction servant à résoudre le probleme sur un des fichiers en utilisant la méthode MTZ
# Elle prend deux paramètres en entrée : i le numéro du fichier qu'on va lire, et plat_relif un boolean servant à indiquer quel type de fichier on lira
function methodeMTZ(i::Int64, plat_relief::Bool)

    C::Matrix{Int64} = choisPlatRelief(i, plat_relief) #appel de choisPlatRelief pour initialiser C

    #Resolution du probleme
    m2::Model = resolutionMTZ(GLPK.Optimizer, C)
    optimize!(m2)
    status = termination_status(m2)

    if status == MOI.OPTIMAL
        println("Problème résolu à l'optimalité")

        println("z = ", objective_value(m2)) # affichage de la valeur optimale

    elseif status == MOI.INFEASIBLE
        println("Problème non-borné")

    elseif status == MOI.INFEASIBLE_OR_UNBOUNDED
        println("Problème impossible")
    end
end

#Fonction servant à résoudre le probleme sur un des fichiers en utilisant la méthode MTZ
# Elle prend deux paramètres en entrée : i le numéro du fichier qu'on va lire, et plat_relif un boolean servant à indiquer quel type de fichier on lira
function methodeDFJ(nb::Int64, plat_relief::Bool)

    C::Matrix{Int64} = choisPlatRelief(nb, plat_relief) #appel de choisPlatRelief pour initialiser C
   
    #On va résoudre le probleme une premiere fois avec peu de contraintes :

    m::Model = resolutionDFJ(GLPK.Optimizer, C)
    tailleG::Int64 = 2
    x = m[:x]

    while (tailleG > 1) #tant qu'on a plus qu'un cycle, on va continuer cette boucle ayant pour fonction d'ajouter les contraintes necessaires
        optimize!(m)
        status = termination_status(m)
        if status == MOI.OPTIMAL
            X::Array{Tuple{Int64,Int64}} = []   #on cree un tableau contenant les tuples choisis pour etre egaux à 1
            for i = 1:size(C, 2)
                for j = 1:size(C, 2)
                    if isapprox(value(m[:x][i, j]), 1) # isapprox est utilisée pour tester l'égalité (approximative) entre des nombres flottants
                        push!(X, (i, j))
                    end
                end
            end
            tab::Vector{Vector{Int64}} = Cycles(X)  #tab sera le vecteur de cycles
            tailleG = length(tab)

            if (tailleG > 1)    #si on a plus que 1 cycle on va rajouter des contraintes selon le plus petit vecteur de tab
                petitTab::Vector{Int64} = PlusPetit(tab)
                taillePT = length(petitTab)

                tmp = petitTab[1]

                #on ajoute 1 contrainte comme étant la somme des taillePT termes contenus dans PlusPetit
                aux = @expression(m, 1.0 * (x[X[tmp][1], X[tmp][2]]))
                for i = 2:taillePT  
                    tmp = petitTab[i]
                    add_to_expression!(aux, 1.0, x[X[petitTab[i]][1], X[petitTab[i]][2]])
                end
                @constraint(m, aux <= taillePT - 1) #on ajoute la contrainte definie selon aux au modele
            end

        elseif status == MOI.INFEASIBLE
            println("Problème non-borné")

        elseif status == MOI.INFEASIBLE_OR_UNBOUNDED
            println("Problème impossible")
        end
    end

    #à la fin on à résolu notre problème : 
    println("Problème résolu à l'optimalité")
    println("z = ", objective_value(m)) # affichage de la valeur optimale
    Y::Array{Tuple{Int64,Int64}} = []
    print("Liste des x[i,j] = 1 ")
    println()
    for i = 1:size(C, 2)
        for j = 1:size(C, 2)
            if isapprox(value(m[:x][i, j]), 1) # isapprox est utilisée pour tester l'égalité (approximative) entre des nombres flottants
                push!(Y, (i, j))
            end
        end
    end
    println(Y)

end

# Fonction servant à verifier la présence d'un élément entier dans un vecteur
function presence(suiteVille::Vector{Int64}, element::Int64)
    n::Int64 = length(suiteVille)
    i::Int64 = 1
    while i <= n    #on parcours le vecteur et si on trouve l'element on renvoie true, ce qui stop la boucle
        if (suiteVille[i] == element)
            return true
        end
        i = i + 1
    end
    return false    #si on a tout parcouru et on a pas stoppé/trouvé l'element, on renvoie false
end

# Fonction renvoyant la position de la colonne ayant la plus petite distance sur la ligne donné entrée de la matrice C
# On veut aussi qu'on ait pas déjà l'élément de présent dans notre suiteVille qui est un vecteur contenant tous les lieux qu'on a deja parcouru
function minDist(C::Matrix{Int64}, ligne::Int64, suiteVille::Vector{Int64})
    n::Int64 = size(C, 1)
    min::Int64 = typemax(Int)
    posMin::Int64 = 0
    for i = 1:n
        #on parcours tous les elements sur la ligne donnée en entrée de C, et on prend celui avec la distance la plus basse, qui n'est pas deja dans suiteVille
        if ((C[ligne, i] <= min) && (i != ligne) && !(presence(suiteVille, i)))
            min = C[ligne, i]
            posMin = i
        end
    end
    return posMin
end

# Fonction goulonne donnant une valeur approchée de solution au probleme du voyageur du commerce
function Glouton(nb::Int64, plat_relief::Bool)

    C::Matrix{Int64} = choisPlatRelief(nb, plat_relief)
    suiteVille::Vector{Int64} = []  #vecteur contenant la suite des lieux déja parcourus
    distance::Int64 = 0 #distance sera la distance totale parcouru (équivalent de z dans les fonctions objectifs des autres méthodes)

    courrant::Int64 = 0
    villeProche::Int64 = 0

    villeDepart::Int64 = 1

    push!(suiteVille, villeDepart)

    for i = 1:(nb-1)    #on parcours tous les points tout en créant suiteVille avec chaque fois la plus petite distance possible
        courrant = suiteVille[i]
        villeProche = minDist(C, courrant, suiteVille)
        push!(suiteVille, villeProche)
        distance = distance + C[courrant, villeProche]
    end

    courrant = suiteVille[nb]
    distance = distance + C[courrant, villeDepart]

    println("Le chemin parcouru est le suivant :")
    println(suiteVille)
    println("On parcours tant de distance :")
    println(distance)
end

# Fonction "main", on prend un entier "test" en entrée qui nous sert de paramètre pour choisir quelle méthode appliquer
function ResolutionProjet(test::Int64)

    if test == 0
        println("Methode MTZ choisie sur les plats : ")
        println()
        for i = 10:10:150
            for i = 1:2
                println()
            end
            @time methodeMTZ(i, true)
        end

    elseif test == 1
        println("Methode MTZ choisie sur les reliefs : ")
        println()
        for i = 10:10:150
            for i = 1:2
                println()
            end
            @time methodeMTZ(i, false)
        end

    elseif test == 2
        println("Methode DFJ choisie sur les plats : ")
        for i in 10:10:150
            for i = 1:2
                println()
            end
            @time methodeDFJ(i, true)
        end
    elseif test == 3
        println("Methode DFJ choisie sur les reliefs : ")
        for i = 10:10:150
            for i = 1:2
                println()
            end
            @time methodeDFJ(i, false)
        end
    elseif test == 4
        println("Methode Glouton choisie sur les plats : ")
        for i = 10:10:150
            for i = 1:2
                println()
            end
            @time Glouton(i, true)
        end
    elseif test == 5
        println("Methode Glouton choisie sur les reliefs : ")
        for i = 10:10:150
            for i = 1:2
                println()
            end
            @time Glouton(i, false)
        end
    end
end




