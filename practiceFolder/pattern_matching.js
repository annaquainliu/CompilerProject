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