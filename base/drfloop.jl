# Support for @drf for

module DRFLoop

export @drf, drf_index

# Error thrown from ill-formed uses of @drf
struct DRFError <: Exception
    msg::AbstractString
end

# Parse iteration space expression
#       symbol '=' range
#       symbol 'in' range
function parse_iteration_space(x)
    (isa(x, Expr) && (x.head === :(=) || x.head === :in)) || throw(NoSCError("= or in expected"))
    length(x.args) == 2 || throw(NoSCError("@drf range syntax is wrong"))
    isa(x.args[1], Symbol) || throw(NoSCError("@drf loop index must be a symbol"))
    x.args # symbol, range
end

# reject invalid control flow statements in @drf loop body
function check_body!(x::Expr)
    if x.head === :break || x.head === :continue
        throw(NoSCError("$(x.head) is not allowed inside a @drf loop body"))
    elseif x.head === :macrocall && x.args[1] === Symbol("@goto")
        throw(NoSCError("$(x.args[1]) is not allowed inside a @drf loop body"))
    end
    for arg in x.args
        check_body!(arg)
    end
    return true
end
check_body!(x::QuoteNode) = check_body!(x.value)
check_body!(x) = true

@inline drf_index(r, i) = (@inbounds ret = r[i+firstindex(r)]; ret)

# Compile Expr x in context of @drf.
function compile(x)
    (isa(x, Expr) && x.head === :for) || throw(NoSCError("for loop expected"))
    length(x.args) == 2 || throw(NoSCError("1D for loop expected"))
    check_body!(x)

    var,range = parse_iteration_space(x.args[1])
    r = gensym("r") # Range value
    n = gensym("n") # Trip count for loop
    i = gensym("i") # Trip index for loop
    quote
        # Evaluate range value once, to enhance type and data flow analysis by optimizers.
        let $r = $range
            let $n = Base.length($r)
                if zero($n) < $n
                    let $i = zero($n)
                        while $i < $n
                            local $var = Base.drf_index($r,$i)
                            $(x.args[2])        # Body of loop
                            $i += 1
                            $(Expr(:loopinfo, Symbol("julia.drfloop")))  # Mark loop as drf loop
                        end
                    end
                end
            end
        end
        nothing
    end
end

"""
    @drf

Annotate a `for` loop to allow the compiler to take extra liberties to allow loop re-ordering for no SC purposes

!!! warning
    This feature is experimental and could change or disappear in future versions of Julia.
    Incorrect use of the `@drf` macro may cause unexpected results.

The object iterated over in a `@drf for` loop should be a one-dimensional range.
By using `@simd`, you are asserting several properties of the loop:

* It is safe to execute iterations in arbitrary or overlapping order, with special consideration for reduction variables.

* The loop must be an innermost loop
* The loop body must be straight-line code. Therefore, [`@inbounds`](@ref) is
    currently needed for all array accesses. The compiler can sometimes turn
    short `&&`, `||`, and `?:` expressions into straight-line code if it is safe
    to evaluate all operands unconditionally. Consider using the [`ifelse`](@ref)
    function instead of `?:` in the loop if it is safe to do so.
* Accesses must have a stride pattern and cannot be "gathers" (random-index
    reads) or "scatters" (random-index writes).
* The stride should be unit stride.

* There exists no loop-carried memory dependencies
* No iteration ever waits on a previous iteration to make forward progress.
"""
macro drf(forloop)
    esc(compile(forloop))
end

end # module DRFLoop
