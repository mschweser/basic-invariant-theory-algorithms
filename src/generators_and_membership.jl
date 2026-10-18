# connect programm 1 and 2
include("generators.jl")
include("f_in_IR.jl")

using Oscar

# input is R = k[x_1, ..., x_n], f in R, G <= Gl(n,k) finite matrix group and debug boolian
# output is (belongs, h, F) 
# where F = [f_1, ..., f_m] is a vector of generators with R^G = k[f_1, ..., f_m]
# belongs is a boolian and is true when f is an invariant (f in R^G)
# and h is a polynomial in k[y_1, ..., y_m] with f = h(f_1, ..., f_m)
# h is nothing if f not in R^G
# input types: R::MPolyRing, G::MatGroup, f::RingElem, debug::Bool
# output type: Tuple{Bool, Union{RingElem, Nothing}, Vector{<:MPolyRingElem}}
function compute_invariant_representation(
    R::MPolyRing, 
    G::MatGroup, 
    f::RingElem; 
    debug::Bool=true)
    # check if f is in R
    parent(f) === R || error("The polynomial f must belong to R.")
    # programm 1 needs graded rings and f must belong to graded R
    if !(R isa MPolyDecRing)
        R, _ = grade(R)
        f = R(f)
    end
    F = compute_generators(R, G; debug=debug) # programm 1
    belongs, h = membership_representation(F, f) # programm 2
    return belongs, h, F
end
