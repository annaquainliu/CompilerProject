class Pattern {

    eqType(p) {

    }
}

class Generic extends Pattern {

    eqType(p) {
        return p instanceof Generic;
    }

    toString() {
        return "GENERIC";
    }
}

class ConPattern extends Pattern {

    /**
     * @param {String} name 
     * @param {List<Pattern>} lists 
     */
    constructor(name, list) {
        super();
        this.name = name;
        this.list = list;
    }

    eqType(p) {
        if (p instanceof Generic) {
            return false;
        }
        return p.name == this.name;
    }

    toString() {
        if (this.list.length == 0) {
            return this.name;
        }
        let str = this.name + "(";
        for (let p of this.list) {
            str += p.toString() + ", "; 
        }
        str = str.substring(0, str.length - 2);
        str += ")";
        return str;
    }
}

function all (p, xs) {
    for (let x of xs) {
        if (!p(x)) {
            return false;
        }
    }
    return true;
}

let list_constructors = [new ConPattern("NIL", []), new ConPattern("CONS", [new Generic(), new Generic()])]

let datatype_env = {"list" : list_constructors};

function deepCopy(list) {
    let copy = [];
    for (let item of list) {
        copy.push(item);
    }
    return copy;
}
function validate_pattern(user_patterns) {
    let name = user_patterns[0].name;
    let values = Object.values(datatype_env);
    for (let constructors of values) {
        console.log("constructors are: ", listOfPatternsToString(constructors))
        for (let cons of constructors) {
            if (cons.name == name) {
                console.log("calling pattern exhaustive on ", listOfPatternsToString(user_patterns), " and ", listOfPatternsToString(constructors))
                return pattern_exhaustive(user_patterns, deepCopy(constructors));
            }
        }
    }
    throw new Error("Constructor does not exist!")
}

function listOfPatternsToString(list) {
    let str = "[";
    for (let p of list) {
        str += p.toString() + ", ";
    }
    str = str.substring(0, str.length - 2);
    return str + "]";
}


/**
 * 
 * Example:
 * 
 * user_patterns = [CONPATTERN("CONS", [GENERIC("X"), CONPATTERN("CONS", [GENERIC("Y"), GENERIC("YS")])]), 
 *                      CONPATTERN("CONS", [GENERIC("X"), CONPATTERN("NIL", [])]),
 *                      CONPATTERN("NIL", [])]
 * 
 * 
 * to_match = [CONPATTERN("CONS", [GENERIC, GENERIC]), CONPATTERN("NIL", [])]
 * 
 * @param {List<Pattern>} user_patterns 
 * @param {List<Pattern>} to_match 
 */
function pattern_exhaustive(user_patterns, to_match) {
    if (to_match.length == 0 && user_patterns.length > 0) {
        throw new Error("Excessive pattern matching")
    }
    if (to_match.length > 0 && user_patterns.length == 0) {
        throw new Error("Non-Exhaustive pattern matching");
    }
    if (to_match.length == 0 && user_patterns.length == 0) {
        return true;
    }
    let first_pattern = to_match[0];
    console.log("trying to match ", first_pattern.toString());
    let matched_patterns = []
    for (let pattern of user_patterns) {
        if (first_pattern.eqType(pattern)) {
            matched_patterns.push(pattern);
        }
    }
    if (matched_patterns.length == 0) {
        throw new Error("Non-Exhaustive pattern matching");
    }
    // list_to_match = [GENERIC, GENERIC]
    let list_to_match = first_pattern.list;

    if (matched_patterns.length > 1 && all(p => all(inner_p => inner_p instanceof Generic, p.list), matched_patterns)) {
        throw new Error("Excessive pattern matching")
    }
    // for every single generic in list_to_match
    // to do: can be generalized 
    // [PATTERN("CONS", [GENERIC, PATTERN("CONS", [GENERIC, GENERIC])]), PATTERN("CONS", [GEN, NIL])]
    //
    for (let i = 0; i < list_to_match.length; i++) {
        console.log("current to match pattern is ", list_to_match[i].toString());
        for (let j = 0; j < matched_patterns.length; j++) {
            let user_pattern_list = matched_patterns[j].list;
            console.log("user pattern match: ", user_pattern_list[i].toString());
            if (!(user_pattern_list[i] instanceof Generic)) {
                let new_user_patterns = [];
                // for every single pattern that is more specific than generic, split up
                for (let z = 0; z < matched_patterns.length; z++) {
                    new_user_patterns.push(matched_patterns[z].list[i]);
                }
                console.log("validating ", listOfPatternsToString(new_user_patterns))
                // validate_pattern based on the non-generic patterns
                validate_pattern(new_user_patterns);
            }
        }
    }
    // if first pattern to match is matched exhaustively in user_patterns, move on to next pattern
    to_match.shift();
    // remove all patterns that matched with the first pattern
    user_patterns = user_patterns.filter(p => !matched_patterns.includes(p));
    // see whether the rest of patterns is exhaustive
    console.log("recursing with userpatterns: ", user_patterns.toString(), "to match: ", to_match.toString());
    return pattern_exhaustive(user_patterns, to_match);
}

// let user_patterns = [new ConPattern("CONS", [new Generic(), new ConPattern("CONS", [new Generic(), new Generic()])]), 
//                        new ConPattern("CONS", [new Generic(), new ConPattern("NIL", [])]),
//                        new ConPattern("NIL", [])]

/**
 * Too little:
 * 
 * x::y::ys
 * []
 */
// let user_patterns = [new ConPattern("NIL", []), new ConPattern("CONS", [new Generic(), new ConPattern("CONS", [new Generic(), new Generic()])])]

/**
 * Too many??:
 * 
 * x::y::ys
 * x::ys
 * []
 * 
 */

// let user_patterns = [new ConPattern("NIL", []), new ConPattern("CONS", [new Generic(), new ConPattern("CONS", [new Generic(), new Generic()])]), new ConPattern("CONS", [new Generic(), new Generic()]), new ConPattern("CONS", [new Generic(), new ConPattern("NIL", [])])];

/**
 * too many:
 * 
 * []
 * []
 * x::xs
 * 
 */

//  let user_patterns = [new ConPattern("NIL", []), new ConPattern("NIL", []), new ConPattern("CONS", [new Generic(), new Generic()])]

/**
 * 
 * Just right:
 * 
 * []
 * x::xs
 */

// let user_patterns = [new ConPattern("NIL", []), new ConPattern("CONS", [new Generic(), new Generic()])]


/**
 * too many:
 * x::xs
 * y::ys
 * []
 */
// let user_patterns = [new ConPattern("CONS", [new Generic(), new Generic()]), new ConPattern("CONS", [new Generic(), new Generic()]), new ConPattern("NIL", [])]


// console.log(validate_pattern(user_patterns));