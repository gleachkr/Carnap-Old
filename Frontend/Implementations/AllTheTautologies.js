// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

function F(f) {
    this.f = f;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Apply
   Applies the function f to the arguments args. If the application is under-
   saturated, a closure is returned, awaiting further arguments. If it is over-
   saturated, the function is fully applied, and the result (assumed to be a
   function) is then applied to the remaining arguments.
*/
function A(f, args) {
    if(f instanceof T) {
        f = E(f);
    }
    // Closure does some funny stuff with functions that occasionally
    // results in non-functions getting applied, so we have to deal with
    // it.
    if(!(f instanceof Function)) {
        f = B(f);
        if(!(f instanceof Function)) {
            return f;
        }
    }

    if(f.arity === undefined) {
        f.arity = f.length;
    }
    if(args.length === f.arity) {
        switch(f.arity) {
            case 0:  return f();
            case 1:  return f(args[0]);
            default: return f.apply(null, args);
        }
    } else if(args.length > f.arity) {
        switch(f.arity) {
            case 0:  return f();
            case 1:  return A(f(args.shift()), args);
            default: return A(f.apply(null, args.splice(0, f.arity)), args);
        }
    } else {
        var g = function() {
            return A(f, args.concat(Array.prototype.slice.call(arguments)));
        };
        g.arity = f.arity - args.length;
        return g;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            var f = t.f;
            t.f = __blackhole;
            if(t.x === __updatable) {
                t.x = f();
            } else {
                return f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw err;
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [[0, str.charCodeAt(i)], acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,[0,str.charCodeAt(i)],new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1])[1]);
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return [0];
    } else if(a == b) {
        return [1];
    }
    return [2];
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

function jsSetCB(elem, evt, cb) {
    // Count return press in single line text box as a change event.
    if(evt == 'change' && elem.type.toLowerCase() == 'text') {
        setCB(elem, 'keyup', function(k) {
            if(k == '\n'.charCodeAt(0)) {
                B(A(cb,[[0,k.keyCode],0]));
            }
        });
    }

    var fun;
    switch(evt) {
    case 'click':
    case 'dblclick':
    case 'mouseup':
    case 'mousedown':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            B(A(cb,[[0,x.button],[0,mx,my],0]));
        };
        break;
    case 'mousemove':
    case 'mouseover':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            B(A(cb,[[0,mx,my],0]));
        };
        break;
    case 'keypress':
    case 'keyup':
    case 'keydown':
        fun = function(x) {B(A(cb,[[0,x.keyCode],0]));};
        break;
    case 'wheel':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            var mdx = [0,x.deltaX];
            var mdy = [0,x.deltaY];
            var mdz = [0,x.deltaZ];
            B(A(cb,[[0,mx,my],[0,mdx,mdy,mdz],0]));
        };
        break;
    default:
        fun = function() {B(A(cb,[0]));};
        break;
    }
    return setCB(elem, evt, fun);
}

function setCB(elem, evt, cb) {
    if(elem.addEventListener) {
        elem.addEventListener(evt, cb, false);
        return true;
    } else if(elem.attachEvent) {
        elem.attachEvent('on'+evt, cb);
        return true;
    }
    return false;
}

function jsSetTimeout(msecs, cb) {
    window.setTimeout(function() {B(A(cb,[0]));}, msecs);
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    if(elem.hasAttribute(prop)) {
        return elem.getAttribute(prop).toString();
    } else {
        return "";
    }
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,[0,e]];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, [0, es[i]], els];
    }
    return els;
}

function jsQuerySelectorAll(elem, query) {
    var els = [0], nl;

    if (!elem || typeof elem.querySelectorAll !== 'function') {
        return els;
    }

    nl = elem.querySelectorAll(query);

    for (var i = nl.length-1; i >= 0; --i) {
        els = [1, [0, nl[i]], els];
    }

    return els;
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,[0,elem]];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, [0,elem.childNodes[i]], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(E(children[1])[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1])[1]);
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

var jsJSONParse = JSON.parse;

// JSON stringify a string
function jsStringify(str) {
    return JSON.stringify(str);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, [0,ks[i]], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

function arr2lst(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem], new T(function() {return arr2lst(arr,elem+1);})]
}
window['arr2lst'] = arr2lst;

function lst2arr(xs) {
    var arr = [];
    for(; xs[0]; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}
window['lst2arr'] = lst2arr;

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);

    if(method == "POST") {
        xhr.setRequestHeader("Content-type",
                             "application/x-www-form-urlencoded");
    }
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                B(A(cb,[[1,[0,xhr.responseText]],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;

function makeStableName(x) {
    if(!x.stableName) {
        x.stableName = __next_stable_name;
        __next_stable_name += 1;
    }
    return x.stableName;
}

function eqStableName(x, y) {
    return (x == y) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation; used under the BSD license.

function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s) {
    var n = s.length,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=s.length; i+=64) {
        md5cycle(state, md5blk(s.substring(i-64, i)));
    }
    s = s.substring(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<s.length; i++)
        tail[i>>2] |= s.charCodeAt(i) << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s.charCodeAt(i)
            + (s.charCodeAt(i+1) << 8)
            + (s.charCodeAt(i+2) << 16)
            + (s.charCodeAt(i+3) << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s) {
    return hex(md51(s));
}

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = [];
    for(; n >= 0; --n) {
        arr.push(x);
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

var _0=function(_1,_2,_){var _3=jsGet(_1,toJSStr(E(_2))),_4=_3;return new T(function(){return fromJSStr(_4);});},_5=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_6=new T(function(){return B(err(_5));}),_7=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_8=new T(function(){return B(err(_7));}),_9=function(_a,_b){while(1){var _c=E(_a);if(!_c[0]){return E(_8);}else{var _d=E(_b);if(!_d){return E(_c[1]);}else{_a=_c[2];_b=_d-1|0;continue;}}}},_e=0,_f=function(_g,_h,_i,_){var _j=rMV(_g),_k=_j,_l=E(_k)[1],_m=function(_){var _=wMV(_g,[0,_l+1|0]);if(_l>=0){var _n=B(A(_9,[_h,_l,_])),_o=_n,_p=jsAppendChild(E(_o)[1],E(_i)[1]);return _e;}else{return E(_6);}};if(_l<=100){return new F(function(){return _m(_);});}else{var _q=E(_i)[1],_r=jsGetFirstChild(_q),_s=_r,_t=E(_s);if(!_t[0]){return new F(function(){return _m(_);});}else{var _u=jsKillChild(E(_t[1])[1],_q);return new F(function(){return _m(_);});}}},_v=function(_w,_x,_y,_){var _z=rMV(_w),_A=_z,_B=E(_A)[1];if(_B<=100){return _e;}else{var _C=E(_y)[1],_D=jsGetLastChild(_C),_E=_D,_F=function(_){var _=wMV(_w,[0,_B-1|0]),_G=jsGetFirstChild(_C),_H=_G,_I=_B-100|0;if(_I>=0){var _J=B(A(_9,[_x,_I,_])),_K=_J,_L=E(_H);if(!_L[0]){return _e;}else{var _M=jsAddChildBefore(E(_K)[1],_C,E(_L[1])[1]);return _e;}}else{return E(_6);}},_N=E(_E);if(!_N[0]){return new F(function(){return _F(_);});}else{var _O=jsKillChild(E(_N[1])[1],_C);return new F(function(){return _F(_);});}}},_P=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_Q=new T(function(){return B(err(_P));}),_R=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V){var _W=E(_U);return _W[0]==0?E(_V):[1,_W[1],new T(function(){return B(_T(_W[2],_V));})];},_X=new T(function(){return B(unCStr("Control.Exception.Base"));}),_Y=new T(function(){return B(unCStr("base"));}),_Z=new T(function(){return B(unCStr("PatternMatchFail"));}),_10=[0],_11=new T(function(){var _12=hs_wordToWord64(18445595),_13=_12,_14=hs_wordToWord64(52003073),_15=_14;return [0,_13,_15,[0,_13,_15,_Y,_X,_Z],_10];}),_16=function(_17){return E(_11);},_18=function(_19){return E(E(_19)[1]);},_1a=function(_1b,_1c,_1d){var _1e=B(A(_1b,[_])),_1f=B(A(_1c,[_])),_1g=hs_eqWord64(_1e[1],_1f[1]),_1h=_1g;if(!E(_1h)){return [0];}else{var _1i=hs_eqWord64(_1e[2],_1f[2]),_1j=_1i;return E(_1j)==0?[0]:[1,_1d];}},_1k=function(_1l){var _1m=E(_1l);return new F(function(){return _1a(B(_18(_1m[1])),_16,_1m[2]);});},_1n=function(_1o){return E(E(_1o)[1]);},_1p=function(_1q,_1r){return new F(function(){return _T(E(_1q)[1],_1r);});},_1s=[0,44],_1t=[0,93],_1u=[0,91],_1v=function(_1w,_1x,_1y){var _1z=E(_1x);return _1z[0]==0?B(unAppCStr("[]",_1y)):[1,_1u,new T(function(){return B(A(_1w,[_1z[1],new T(function(){var _1A=function(_1B){var _1C=E(_1B);return _1C[0]==0?E([1,_1t,_1y]):[1,_1s,new T(function(){return B(A(_1w,[_1C[1],new T(function(){return B(_1A(_1C[2]));})]));})];};return B(_1A(_1z[2]));})]));})];},_1D=function(_1E,_1F){return new F(function(){return _1v(_1p,_1E,_1F);});},_1G=function(_1H,_1I,_1J){return new F(function(){return _T(E(_1I)[1],_1J);});},_1K=[0,_1G,_1n,_1D],_1L=new T(function(){return [0,_16,_1K,_1M,_1k];}),_1M=function(_1N){return [0,_1L,_1N];},_1O=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_1P=function(_1Q,_1R){return new F(function(){return die(new T(function(){return B(A(_1R,[_1Q]));}));});},_1S=function(_1T,_1U){var _1V=E(_1U);if(!_1V[0]){return [0,_10,_10];}else{var _1W=_1V[1];if(!B(A(_1T,[_1W]))){return [0,_10,_1V];}else{var _1X=new T(function(){var _1Y=B(_1S(_1T,_1V[2]));return [0,_1Y[1],_1Y[2]];});return [0,[1,_1W,new T(function(){return E(E(_1X)[1]);})],new T(function(){return E(E(_1X)[2]);})];}}},_1Z=[0,32],_20=[0,10],_21=[1,_20,_10],_22=function(_23){return E(E(_23)[1])==124?false:true;},_24=function(_25,_26){var _27=B(_1S(_22,B(unCStr(_25)))),_28=_27[1],_29=function(_2a,_2b){return new F(function(){return _T(_2a,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_T(_26,new T(function(){return B(_T(_2b,_21));},1)));})));},1));});},_2c=E(_27[2]);if(!_2c[0]){return new F(function(){return _29(_28,_10);});}else{return E(E(_2c[1])[1])==124?B(_29(_28,[1,_1Z,_2c[2]])):B(_29(_28,_10));}},_2d=function(_2e){return new F(function(){return _1P([0,new T(function(){return B(_24(_2e,_1O));})],_1M);});},_2f=new T(function(){return B(_2d("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_2g=function(_2h,_2i){while(1){var _2j=(function(_2k,_2l){var _2m=E(_2k);switch(_2m[0]){case 0:var _2n=E(_2l);if(!_2n[0]){return [0];}else{_2h=B(A(_2m[1],[_2n[1]]));_2i=_2n[2];return null;}break;case 1:var _2o=B(A(_2m[1],[_2l])),_2p=_2l;_2h=_2o;_2i=_2p;return null;case 2:return [0];case 3:return [1,[0,_2m[1],_2l],new T(function(){return B(_2g(_2m[2],_2l));})];default:return E(_2m[1]);}})(_2h,_2i);if(_2j!=null){return _2j;}}},_2q=function(_2r,_2s){var _2t=function(_2u){var _2v=E(_2s);if(_2v[0]==3){return [3,_2v[1],new T(function(){return B(_2q(_2r,_2v[2]));})];}else{var _2w=E(_2r);if(_2w[0]==2){return E(_2v);}else{var _2x=E(_2v);if(_2x[0]==2){return E(_2w);}else{var _2y=function(_2z){var _2A=E(_2x);if(_2A[0]==4){return [1,function(_2B){return [4,new T(function(){return B(_T(B(_2g(_2w,_2B)),_2A[1]));})];}];}else{var _2C=E(_2w);if(_2C[0]==1){var _2D=_2C[1],_2E=E(_2A);return _2E[0]==0?[1,function(_2F){return new F(function(){return _2q(B(A(_2D,[_2F])),_2E);});}]:[1,function(_2G){return new F(function(){return _2q(B(A(_2D,[_2G])),new T(function(){return B(A(_2E[1],[_2G]));}));});}];}else{var _2H=E(_2A);return _2H[0]==0?E(_2f):[1,function(_2I){return new F(function(){return _2q(_2C,new T(function(){return B(A(_2H[1],[_2I]));}));});}];}}},_2J=E(_2w);switch(_2J[0]){case 1:var _2K=E(_2x);if(_2K[0]==4){return [1,function(_2L){return [4,new T(function(){return B(_T(B(_2g(B(A(_2J[1],[_2L])),_2L)),_2K[1]));})];}];}else{return new F(function(){return _2y(_);});}break;case 4:var _2M=_2J[1],_2N=E(_2x);switch(_2N[0]){case 0:return [1,function(_2O){return [4,new T(function(){return B(_T(_2M,new T(function(){return B(_2g(_2N,_2O));},1)));})];}];case 1:return [1,function(_2P){return [4,new T(function(){return B(_T(_2M,new T(function(){return B(_2g(B(A(_2N[1],[_2P])),_2P));},1)));})];}];default:return [4,new T(function(){return B(_T(_2M,_2N[1]));})];}break;default:return new F(function(){return _2y(_);});}}}}},_2Q=E(_2r);switch(_2Q[0]){case 0:var _2R=E(_2s);if(!_2R[0]){return [0,function(_2S){return new F(function(){return _2q(B(A(_2Q[1],[_2S])),new T(function(){return B(A(_2R[1],[_2S]));}));});}];}else{return new F(function(){return _2t(_);});}break;case 3:return [3,_2Q[1],new T(function(){return B(_2q(_2Q[2],_2s));})];default:return new F(function(){return _2t(_);});}},_2T=[0,41],_2U=[1,_2T,_10],_2V=[0,40],_2W=[1,_2V,_10],_2X=function(_2Y,_2Z){while(1){var _30=E(_2Y);if(!_30[0]){return E(_2Z)[0]==0?true:false;}else{var _31=E(_2Z);if(!_31[0]){return false;}else{if(E(_30[1])[1]!=E(_31[1])[1]){return false;}else{_2Y=_30[2];_2Z=_31[2];continue;}}}}},_32=function(_33,_34){return E(_33)[1]!=E(_34)[1];},_35=function(_36,_37){return E(_36)[1]==E(_37)[1];},_38=[0,_35,_32],_39=function(_3a,_3b){while(1){var _3c=E(_3a);if(!_3c[0]){return E(_3b)[0]==0?true:false;}else{var _3d=E(_3b);if(!_3d[0]){return false;}else{if(E(_3c[1])[1]!=E(_3d[1])[1]){return false;}else{_3a=_3c[2];_3b=_3d[2];continue;}}}}},_3e=function(_3f,_3g){return !B(_39(_3f,_3g))?true:false;},_3h=[0,_39,_3e],_3i=function(_3j,_3k){var _3l=E(_3j);switch(_3l[0]){case 0:return [0,function(_3m){return new F(function(){return _3i(B(A(_3l[1],[_3m])),_3k);});}];case 1:return [1,function(_3n){return new F(function(){return _3i(B(A(_3l[1],[_3n])),_3k);});}];case 2:return [2];case 3:return new F(function(){return _2q(B(A(_3k,[_3l[1]])),new T(function(){return B(_3i(_3l[2],_3k));}));});break;default:var _3o=function(_3p){var _3q=E(_3p);if(!_3q[0]){return [0];}else{var _3r=E(_3q[1]);return new F(function(){return _T(B(_2g(B(A(_3k,[_3r[1]])),_3r[2])),new T(function(){return B(_3o(_3q[2]));},1));});}},_3s=B(_3o(_3l[1]));return _3s[0]==0?[2]:[4,_3s];}},_3t=[2],_3u=function(_3v){return [3,_3v,_3t];},_3w=function(_3x,_3y){var _3z=E(_3x);if(!_3z){return new F(function(){return A(_3y,[_e]);});}else{return [0,function(_3A){return E(new T(function(){return B(_3w(_3z-1|0,_3y));}));}];}},_3B=function(_3C,_3D,_3E){return function(_3F){return new F(function(){return A(function(_3G,_3H,_3I){while(1){var _3J=(function(_3K,_3L,_3M){var _3N=E(_3K);switch(_3N[0]){case 0:var _3O=E(_3L);if(!_3O[0]){return E(_3D);}else{_3G=B(A(_3N[1],[_3O[1]]));_3H=_3O[2];var _3P=_3M+1|0;_3I=_3P;return null;}break;case 1:var _3Q=B(A(_3N[1],[_3L])),_3R=_3L,_3P=_3M;_3G=_3Q;_3H=_3R;_3I=_3P;return null;case 2:return E(_3D);case 3:return function(_3S){return new F(function(){return _3w(_3M,function(_3T){return E(new T(function(){return B(_3i(_3N,_3S));}));});});};default:return function(_3U){return new F(function(){return _3i(_3N,_3U);});};}})(_3G,_3H,_3I);if(_3J!=null){return _3J;}}},[new T(function(){return B(A(_3C,[_3u]));}),_3F,0,_3E]);});};},_3V=function(_3W){return new F(function(){return A(_3W,[_10]);});},_3X=function(_3Y,_3Z){var _40=function(_41){var _42=E(_41);if(!_42[0]){return E(_3V);}else{var _43=_42[1];return !B(A(_3Y,[_43]))?E(_3V):function(_44){return [0,function(_45){return E(new T(function(){return B(A(new T(function(){return B(_40(_42[2]));}),[function(_46){return new F(function(){return A(_44,[[1,_43,_46]]);});}]));}));}];};}};return function(_47){return new F(function(){return A(_40,[_47,_3Z]);});};},_48=[6],_49=function(_4a){return E(_4a);},_4b=new T(function(){return B(unCStr("valDig: Bad base"));}),_4c=new T(function(){return B(err(_4b));}),_4d=function(_4e,_4f){var _4g=function(_4h,_4i){var _4j=E(_4h);if(!_4j[0]){return function(_4k){return new F(function(){return A(_4k,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{var _4l=E(_4j[1])[1],_4m=function(_4n){return function(_4o){return [0,function(_4p){return E(new T(function(){return B(A(new T(function(){return B(_4g(_4j[2],function(_4q){return new F(function(){return A(_4i,[[1,_4n,_4q]]);});}));}),[_4o]));}));}];};};switch(E(E(_4e)[1])){case 8:if(48>_4l){return function(_4r){return new F(function(){return A(_4r,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{if(_4l>55){return function(_4s){return new F(function(){return A(_4s,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{return new F(function(){return _4m([0,_4l-48|0]);});}}break;case 10:if(48>_4l){return function(_4t){return new F(function(){return A(_4t,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{if(_4l>57){return function(_4u){return new F(function(){return A(_4u,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{return new F(function(){return _4m([0,_4l-48|0]);});}}break;case 16:if(48>_4l){if(97>_4l){if(65>_4l){return function(_4v){return new F(function(){return A(_4v,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{if(_4l>70){return function(_4w){return new F(function(){return A(_4w,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{return new F(function(){return _4m([0,(_4l-65|0)+10|0]);});}}}else{if(_4l>102){if(65>_4l){return function(_4x){return new F(function(){return A(_4x,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{if(_4l>70){return function(_4y){return new F(function(){return A(_4y,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{return new F(function(){return _4m([0,(_4l-65|0)+10|0]);});}}}else{return new F(function(){return _4m([0,(_4l-97|0)+10|0]);});}}}else{if(_4l>57){if(97>_4l){if(65>_4l){return function(_4z){return new F(function(){return A(_4z,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{if(_4l>70){return function(_4A){return new F(function(){return A(_4A,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{return new F(function(){return _4m([0,(_4l-65|0)+10|0]);});}}}else{if(_4l>102){if(65>_4l){return function(_4B){return new F(function(){return A(_4B,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{if(_4l>70){return function(_4C){return new F(function(){return A(_4C,[new T(function(){return B(A(_4i,[_10]));})]);});};}else{return new F(function(){return _4m([0,(_4l-65|0)+10|0]);});}}}else{return new F(function(){return _4m([0,(_4l-97|0)+10|0]);});}}}else{return new F(function(){return _4m([0,_4l-48|0]);});}}break;default:return E(_4c);}}};return function(_4D){return new F(function(){return A(_4g,[_4D,_49,function(_4E){var _4F=E(_4E);return _4F[0]==0?[2]:B(A(_4f,[_4F]));}]);});};},_4G=[0,10],_4H=[0,1],_4I=[0,2147483647],_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M[0]){var _4N=_4M[1],_4O=E(_4L);if(!_4O[0]){var _4P=_4O[1],_4Q=addC(_4N,_4P);if(!E(_4Q[2])){return [0,_4Q[1]];}else{_4K=[1,I_fromInt(_4N)];_4L=[1,I_fromInt(_4P)];continue;}}else{_4K=[1,I_fromInt(_4N)];_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R[0]){_4K=_4M;_4L=[1,I_fromInt(_4R[1])];continue;}else{return [1,I_add(_4M[1],_4R[1])];}}}},_4S=new T(function(){return B(_4J(_4I,_4H));}),_4T=function(_4U){var _4V=E(_4U);if(!_4V[0]){var _4W=E(_4V[1]);return _4W==(-2147483648)?E(_4S):[0, -_4W];}else{return [1,I_negate(_4V[1])];}},_4X=[0,10],_4Y=[0,0],_4Z=function(_50){return [0,_50];},_51=function(_52,_53){while(1){var _54=E(_52);if(!_54[0]){var _55=_54[1],_56=E(_53);if(!_56[0]){var _57=_56[1];if(!(imul(_55,_57)|0)){return [0,imul(_55,_57)|0];}else{_52=[1,I_fromInt(_55)];_53=[1,I_fromInt(_57)];continue;}}else{_52=[1,I_fromInt(_55)];_53=_56;continue;}}else{var _58=E(_53);if(!_58[0]){_52=_54;_53=[1,I_fromInt(_58[1])];continue;}else{return [1,I_mul(_54[1],_58[1])];}}}},_59=function(_5a,_5b,_5c){while(1){var _5d=E(_5c);if(!_5d[0]){return E(_5b);}else{var _5e=B(_4J(B(_51(_5b,_5a)),B(_4Z(E(_5d[1])[1]))));_5c=_5d[2];_5b=_5e;continue;}}},_5f=function(_5g){var _5h=new T(function(){return B(_2q(B(_2q([0,function(_5i){return E(E(_5i)[1])==45?[1,B(_4d(_4G,function(_5j){return new F(function(){return A(_5g,[[1,new T(function(){return B(_4T(B(_59(_4X,_4Y,_5j))));})]]);});}))]:[2];}],[0,function(_5k){return E(E(_5k)[1])==43?[1,B(_4d(_4G,function(_5l){return new F(function(){return A(_5g,[[1,new T(function(){return B(_59(_4X,_4Y,_5l));})]]);});}))]:[2];}])),new T(function(){return [1,B(_4d(_4G,function(_5m){return new F(function(){return A(_5g,[[1,new T(function(){return B(_59(_4X,_4Y,_5m));})]]);});}))];})));});return new F(function(){return _2q([0,function(_5n){return E(E(_5n)[1])==101?E(_5h):[2];}],[0,function(_5o){return E(E(_5o)[1])==69?E(_5h):[2];}]);});},_5p=[0],_5q=function(_5r){return new F(function(){return A(_5r,[_5p]);});},_5s=function(_5t){return new F(function(){return A(_5t,[_5p]);});},_5u=function(_5v){return function(_5w){return E(E(_5w)[1])==46?[1,B(_4d(_4G,function(_5x){return new F(function(){return A(_5v,[[1,_5x]]);});}))]:[2];};},_5y=function(_5z){return [0,B(_5u(_5z))];},_5A=function(_5B){return new F(function(){return _4d(_4G,function(_5C){return [1,B(_3B(_5y,_5q,function(_5D){return [1,B(_3B(_5f,_5s,function(_5E){return new F(function(){return A(_5B,[[5,[1,_5C,_5D,_5E]]]);});}))];}))];});});},_5F=function(_5G){return [1,B(_5A(_5G))];},_5H=function(_5I){return E(E(_5I)[1]);},_5J=function(_5K,_5L,_5M){while(1){var _5N=E(_5M);if(!_5N[0]){return false;}else{if(!B(A(_5H,[_5K,_5L,_5N[1]]))){_5M=_5N[2];continue;}else{return true;}}}},_5O=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_5P=function(_5Q){return new F(function(){return _5J(_38,_5Q,_5O);});},_5R=[0,8],_5S=[0,16],_5T=function(_5U){var _5V=function(_5W){return new F(function(){return A(_5U,[[5,[0,_5R,_5W]]]);});},_5X=function(_5Y){return new F(function(){return A(_5U,[[5,[0,_5S,_5Y]]]);});};return function(_5Z){return E(E(_5Z)[1])==48?E([0,function(_60){switch(E(E(_60)[1])){case 79:return [1,B(_4d(_5R,_5V))];case 88:return [1,B(_4d(_5S,_5X))];case 111:return [1,B(_4d(_5R,_5V))];case 120:return [1,B(_4d(_5S,_5X))];default:return [2];}}]):[2];};},_61=function(_62){return [0,B(_5T(_62))];},_63=false,_64=true,_65=function(_66){var _67=new T(function(){return B(A(_66,[_5R]));}),_68=new T(function(){return B(A(_66,[_5S]));});return function(_69){switch(E(E(_69)[1])){case 79:return E(_67);case 88:return E(_68);case 111:return E(_67);case 120:return E(_68);default:return [2];}};},_6a=function(_6b){return [0,B(_65(_6b))];},_6c=[0,92],_6d=function(_6e){return new F(function(){return A(_6e,[_4G]);});},_6f=function(_6g,_6h){var _6i=jsShowI(_6g),_6j=_6i;return new F(function(){return _T(fromJSStr(_6j),_6h);});},_6k=[0,41],_6l=[0,40],_6m=function(_6n,_6o,_6p){if(_6o>=0){return new F(function(){return _6f(_6o,_6p);});}else{return _6n<=6?B(_6f(_6o,_6p)):[1,_6l,new T(function(){var _6q=jsShowI(_6o),_6r=_6q;return B(_T(fromJSStr(_6r),[1,_6k,_6p]));})];}},_6s=function(_6t){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_6m(9,_6t,_10));}))));});},_6u=function(_6v){var _6w=E(_6v);return _6w[0]==0?E(_6w[1]):I_toInt(_6w[1]);},_6x=function(_6y,_6z){var _6A=E(_6y);if(!_6A[0]){var _6B=_6A[1],_6C=E(_6z);return _6C[0]==0?_6B<=_6C[1]:I_compareInt(_6C[1],_6B)>=0;}else{var _6D=_6A[1],_6E=E(_6z);return _6E[0]==0?I_compareInt(_6D,_6E[1])<=0:I_compare(_6D,_6E[1])<=0;}},_6F=function(_6G){return [2];},_6H=function(_6I){var _6J=E(_6I);if(!_6J[0]){return E(_6F);}else{var _6K=_6J[1],_6L=E(_6J[2]);return _6L[0]==0?E(_6K):function(_6M){return new F(function(){return _2q(B(A(_6K,[_6M])),new T(function(){return B(A(new T(function(){return B(_6H(_6L));}),[_6M]));}));});};}},_6N=function(_6O){return [2];},_6P=function(_6Q,_6R){var _6S=function(_6T,_6U){var _6V=E(_6T);if(!_6V[0]){return function(_6W){return new F(function(){return A(_6W,[_6Q]);});};}else{var _6X=E(_6U);return _6X[0]==0?E(_6N):E(_6V[1])[1]!=E(_6X[1])[1]?E(_6N):function(_6Y){return [0,function(_6Z){return E(new T(function(){return B(A(new T(function(){return B(_6S(_6V[2],_6X[2]));}),[_6Y]));}));}];};}};return function(_70){return new F(function(){return A(_6S,[_6Q,_70,_6R]);});};},_71=new T(function(){return B(unCStr("SOH"));}),_72=[0,1],_73=function(_74){return [1,B(_6P(_71,function(_75){return E(new T(function(){return B(A(_74,[_72]));}));}))];},_76=new T(function(){return B(unCStr("SO"));}),_77=[0,14],_78=function(_79){return [1,B(_6P(_76,function(_7a){return E(new T(function(){return B(A(_79,[_77]));}));}))];},_7b=function(_7c){return [1,B(_3B(_73,_78,_7c))];},_7d=new T(function(){return B(unCStr("NUL"));}),_7e=[0,0],_7f=function(_7g){return [1,B(_6P(_7d,function(_7h){return E(new T(function(){return B(A(_7g,[_7e]));}));}))];},_7i=new T(function(){return B(unCStr("STX"));}),_7j=[0,2],_7k=function(_7l){return [1,B(_6P(_7i,function(_7m){return E(new T(function(){return B(A(_7l,[_7j]));}));}))];},_7n=new T(function(){return B(unCStr("ETX"));}),_7o=[0,3],_7p=function(_7q){return [1,B(_6P(_7n,function(_7r){return E(new T(function(){return B(A(_7q,[_7o]));}));}))];},_7s=new T(function(){return B(unCStr("EOT"));}),_7t=[0,4],_7u=function(_7v){return [1,B(_6P(_7s,function(_7w){return E(new T(function(){return B(A(_7v,[_7t]));}));}))];},_7x=new T(function(){return B(unCStr("ENQ"));}),_7y=[0,5],_7z=function(_7A){return [1,B(_6P(_7x,function(_7B){return E(new T(function(){return B(A(_7A,[_7y]));}));}))];},_7C=new T(function(){return B(unCStr("ACK"));}),_7D=[0,6],_7E=function(_7F){return [1,B(_6P(_7C,function(_7G){return E(new T(function(){return B(A(_7F,[_7D]));}));}))];},_7H=new T(function(){return B(unCStr("BEL"));}),_7I=[0,7],_7J=function(_7K){return [1,B(_6P(_7H,function(_7L){return E(new T(function(){return B(A(_7K,[_7I]));}));}))];},_7M=new T(function(){return B(unCStr("BS"));}),_7N=[0,8],_7O=function(_7P){return [1,B(_6P(_7M,function(_7Q){return E(new T(function(){return B(A(_7P,[_7N]));}));}))];},_7R=new T(function(){return B(unCStr("HT"));}),_7S=[0,9],_7T=function(_7U){return [1,B(_6P(_7R,function(_7V){return E(new T(function(){return B(A(_7U,[_7S]));}));}))];},_7W=new T(function(){return B(unCStr("LF"));}),_7X=[0,10],_7Y=function(_7Z){return [1,B(_6P(_7W,function(_80){return E(new T(function(){return B(A(_7Z,[_7X]));}));}))];},_81=new T(function(){return B(unCStr("VT"));}),_82=[0,11],_83=function(_84){return [1,B(_6P(_81,function(_85){return E(new T(function(){return B(A(_84,[_82]));}));}))];},_86=new T(function(){return B(unCStr("FF"));}),_87=[0,12],_88=function(_89){return [1,B(_6P(_86,function(_8a){return E(new T(function(){return B(A(_89,[_87]));}));}))];},_8b=new T(function(){return B(unCStr("CR"));}),_8c=[0,13],_8d=function(_8e){return [1,B(_6P(_8b,function(_8f){return E(new T(function(){return B(A(_8e,[_8c]));}));}))];},_8g=new T(function(){return B(unCStr("SI"));}),_8h=[0,15],_8i=function(_8j){return [1,B(_6P(_8g,function(_8k){return E(new T(function(){return B(A(_8j,[_8h]));}));}))];},_8l=new T(function(){return B(unCStr("DLE"));}),_8m=[0,16],_8n=function(_8o){return [1,B(_6P(_8l,function(_8p){return E(new T(function(){return B(A(_8o,[_8m]));}));}))];},_8q=new T(function(){return B(unCStr("DC1"));}),_8r=[0,17],_8s=function(_8t){return [1,B(_6P(_8q,function(_8u){return E(new T(function(){return B(A(_8t,[_8r]));}));}))];},_8v=new T(function(){return B(unCStr("DC2"));}),_8w=[0,18],_8x=function(_8y){return [1,B(_6P(_8v,function(_8z){return E(new T(function(){return B(A(_8y,[_8w]));}));}))];},_8A=new T(function(){return B(unCStr("DC3"));}),_8B=[0,19],_8C=function(_8D){return [1,B(_6P(_8A,function(_8E){return E(new T(function(){return B(A(_8D,[_8B]));}));}))];},_8F=new T(function(){return B(unCStr("DC4"));}),_8G=[0,20],_8H=function(_8I){return [1,B(_6P(_8F,function(_8J){return E(new T(function(){return B(A(_8I,[_8G]));}));}))];},_8K=new T(function(){return B(unCStr("NAK"));}),_8L=[0,21],_8M=function(_8N){return [1,B(_6P(_8K,function(_8O){return E(new T(function(){return B(A(_8N,[_8L]));}));}))];},_8P=new T(function(){return B(unCStr("SYN"));}),_8Q=[0,22],_8R=function(_8S){return [1,B(_6P(_8P,function(_8T){return E(new T(function(){return B(A(_8S,[_8Q]));}));}))];},_8U=new T(function(){return B(unCStr("ETB"));}),_8V=[0,23],_8W=function(_8X){return [1,B(_6P(_8U,function(_8Y){return E(new T(function(){return B(A(_8X,[_8V]));}));}))];},_8Z=new T(function(){return B(unCStr("CAN"));}),_90=[0,24],_91=function(_92){return [1,B(_6P(_8Z,function(_93){return E(new T(function(){return B(A(_92,[_90]));}));}))];},_94=new T(function(){return B(unCStr("EM"));}),_95=[0,25],_96=function(_97){return [1,B(_6P(_94,function(_98){return E(new T(function(){return B(A(_97,[_95]));}));}))];},_99=new T(function(){return B(unCStr("SUB"));}),_9a=[0,26],_9b=function(_9c){return [1,B(_6P(_99,function(_9d){return E(new T(function(){return B(A(_9c,[_9a]));}));}))];},_9e=new T(function(){return B(unCStr("ESC"));}),_9f=[0,27],_9g=function(_9h){return [1,B(_6P(_9e,function(_9i){return E(new T(function(){return B(A(_9h,[_9f]));}));}))];},_9j=new T(function(){return B(unCStr("FS"));}),_9k=[0,28],_9l=function(_9m){return [1,B(_6P(_9j,function(_9n){return E(new T(function(){return B(A(_9m,[_9k]));}));}))];},_9o=new T(function(){return B(unCStr("GS"));}),_9p=[0,29],_9q=function(_9r){return [1,B(_6P(_9o,function(_9s){return E(new T(function(){return B(A(_9r,[_9p]));}));}))];},_9t=new T(function(){return B(unCStr("RS"));}),_9u=[0,30],_9v=function(_9w){return [1,B(_6P(_9t,function(_9x){return E(new T(function(){return B(A(_9w,[_9u]));}));}))];},_9y=new T(function(){return B(unCStr("US"));}),_9z=[0,31],_9A=function(_9B){return [1,B(_6P(_9y,function(_9C){return E(new T(function(){return B(A(_9B,[_9z]));}));}))];},_9D=new T(function(){return B(unCStr("SP"));}),_9E=[0,32],_9F=function(_9G){return [1,B(_6P(_9D,function(_9H){return E(new T(function(){return B(A(_9G,[_9E]));}));}))];},_9I=new T(function(){return B(unCStr("DEL"));}),_9J=[0,127],_9K=function(_9L){return [1,B(_6P(_9I,function(_9M){return E(new T(function(){return B(A(_9L,[_9J]));}));}))];},_9N=[1,_9K,_10],_9O=[1,_9F,_9N],_9P=[1,_9A,_9O],_9Q=[1,_9v,_9P],_9R=[1,_9q,_9Q],_9S=[1,_9l,_9R],_9T=[1,_9g,_9S],_9U=[1,_9b,_9T],_9V=[1,_96,_9U],_9W=[1,_91,_9V],_9X=[1,_8W,_9W],_9Y=[1,_8R,_9X],_9Z=[1,_8M,_9Y],_a0=[1,_8H,_9Z],_a1=[1,_8C,_a0],_a2=[1,_8x,_a1],_a3=[1,_8s,_a2],_a4=[1,_8n,_a3],_a5=[1,_8i,_a4],_a6=[1,_8d,_a5],_a7=[1,_88,_a6],_a8=[1,_83,_a7],_a9=[1,_7Y,_a8],_aa=[1,_7T,_a9],_ab=[1,_7O,_aa],_ac=[1,_7J,_ab],_ad=[1,_7E,_ac],_ae=[1,_7z,_ad],_af=[1,_7u,_ae],_ag=[1,_7p,_af],_ah=[1,_7k,_ag],_ai=[1,_7f,_ah],_aj=[1,_7b,_ai],_ak=new T(function(){return B(_6H(_aj));}),_al=[0,1114111],_am=[0,34],_an=[0,39],_ao=function(_ap){var _aq=new T(function(){return B(A(_ap,[_7I]));}),_ar=new T(function(){return B(A(_ap,[_7N]));}),_as=new T(function(){return B(A(_ap,[_7S]));}),_at=new T(function(){return B(A(_ap,[_7X]));}),_au=new T(function(){return B(A(_ap,[_82]));}),_av=new T(function(){return B(A(_ap,[_87]));}),_aw=new T(function(){return B(A(_ap,[_8c]));});return new F(function(){return _2q([0,function(_ax){switch(E(E(_ax)[1])){case 34:return E(new T(function(){return B(A(_ap,[_am]));}));case 39:return E(new T(function(){return B(A(_ap,[_an]));}));case 92:return E(new T(function(){return B(A(_ap,[_6c]));}));case 97:return E(_aq);case 98:return E(_ar);case 102:return E(_av);case 110:return E(_at);case 114:return E(_aw);case 116:return E(_as);case 118:return E(_au);default:return [2];}}],new T(function(){return B(_2q([1,B(_3B(_6a,_6d,function(_ay){return [1,B(_4d(_ay,function(_az){var _aA=B(_59(new T(function(){return B(_4Z(E(_ay)[1]));}),_4Y,_az));return !B(_6x(_aA,_al))?[2]:B(A(_ap,[new T(function(){var _aB=B(_6u(_aA));if(_aB>>>0>1114111){var _aC=B(_6s(_aB));}else{var _aC=[0,_aB];}var _aD=_aC,_aE=_aD,_aF=_aE;return _aF;})]));}))];}))],new T(function(){return B(_2q([0,function(_aG){return E(E(_aG)[1])==94?E([0,function(_aH){switch(E(E(_aH)[1])){case 64:return E(new T(function(){return B(A(_ap,[_7e]));}));case 65:return E(new T(function(){return B(A(_ap,[_72]));}));case 66:return E(new T(function(){return B(A(_ap,[_7j]));}));case 67:return E(new T(function(){return B(A(_ap,[_7o]));}));case 68:return E(new T(function(){return B(A(_ap,[_7t]));}));case 69:return E(new T(function(){return B(A(_ap,[_7y]));}));case 70:return E(new T(function(){return B(A(_ap,[_7D]));}));case 71:return E(_aq);case 72:return E(_ar);case 73:return E(_as);case 74:return E(_at);case 75:return E(_au);case 76:return E(_av);case 77:return E(_aw);case 78:return E(new T(function(){return B(A(_ap,[_77]));}));case 79:return E(new T(function(){return B(A(_ap,[_8h]));}));case 80:return E(new T(function(){return B(A(_ap,[_8m]));}));case 81:return E(new T(function(){return B(A(_ap,[_8r]));}));case 82:return E(new T(function(){return B(A(_ap,[_8w]));}));case 83:return E(new T(function(){return B(A(_ap,[_8B]));}));case 84:return E(new T(function(){return B(A(_ap,[_8G]));}));case 85:return E(new T(function(){return B(A(_ap,[_8L]));}));case 86:return E(new T(function(){return B(A(_ap,[_8Q]));}));case 87:return E(new T(function(){return B(A(_ap,[_8V]));}));case 88:return E(new T(function(){return B(A(_ap,[_90]));}));case 89:return E(new T(function(){return B(A(_ap,[_95]));}));case 90:return E(new T(function(){return B(A(_ap,[_9a]));}));case 91:return E(new T(function(){return B(A(_ap,[_9f]));}));case 92:return E(new T(function(){return B(A(_ap,[_9k]));}));case 93:return E(new T(function(){return B(A(_ap,[_9p]));}));case 94:return E(new T(function(){return B(A(_ap,[_9u]));}));case 95:return E(new T(function(){return B(A(_ap,[_9z]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_ak,[_ap]));})));})));}));});},_aI=function(_aJ){return new F(function(){return A(_aJ,[_e]);});},_aK=function(_aL){var _aM=E(_aL);if(!_aM[0]){return E(_aI);}else{var _aN=_aM[2],_aO=E(E(_aM[1])[1]);switch(_aO){case 9:return function(_aP){return [0,function(_aQ){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_aP]));}));}];};case 10:return function(_aR){return [0,function(_aS){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_aR]));}));}];};case 11:return function(_aT){return [0,function(_aU){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_aT]));}));}];};case 12:return function(_aV){return [0,function(_aW){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_aV]));}));}];};case 13:return function(_aX){return [0,function(_aY){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_aX]));}));}];};case 32:return function(_aZ){return [0,function(_b0){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_aZ]));}));}];};case 160:return function(_b1){return [0,function(_b2){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_b1]));}));}];};default:var _b3=u_iswspace(_aO),_b4=_b3;return E(_b4)==0?E(_aI):function(_b5){return [0,function(_b6){return E(new T(function(){return B(A(new T(function(){return B(_aK(_aN));}),[_b5]));}));}];};}}},_b7=function(_b8){var _b9=new T(function(){return B(_b7(_b8));}),_ba=[1,function(_bb){return new F(function(){return A(_aK,[_bb,function(_bc){return E([0,function(_bd){return E(E(_bd)[1])==92?E(_b9):[2];}]);}]);});}];return new F(function(){return _2q([0,function(_be){return E(E(_be)[1])==92?E([0,function(_bf){var _bg=E(E(_bf)[1]);switch(_bg){case 9:return E(_ba);case 10:return E(_ba);case 11:return E(_ba);case 12:return E(_ba);case 13:return E(_ba);case 32:return E(_ba);case 38:return E(_b9);case 160:return E(_ba);default:var _bh=u_iswspace(_bg),_bi=_bh;return E(_bi)==0?[2]:E(_ba);}}]):[2];}],[0,function(_bj){var _bk=E(_bj);return E(_bk[1])==92?E(new T(function(){return B(_ao(function(_bl){return new F(function(){return A(_b8,[[0,_bl,_64]]);});}));})):B(A(_b8,[[0,_bk,_63]]));}]);});},_bm=function(_bn,_bo){return new F(function(){return _b7(function(_bp){var _bq=E(_bp),_br=E(_bq[1]);if(E(_br[1])==34){if(!E(_bq[2])){return E(new T(function(){return B(A(_bo,[[1,new T(function(){return B(A(_bn,[_10]));})]]));}));}else{return new F(function(){return _bm(function(_bs){return new F(function(){return A(_bn,[[1,_br,_bs]]);});},_bo);});}}else{return new F(function(){return _bm(function(_bt){return new F(function(){return A(_bn,[[1,_br,_bt]]);});},_bo);});}});});},_bu=new T(function(){return B(unCStr("_\'"));}),_bv=function(_bw){var _bx=u_iswalnum(_bw),_by=_bx;return E(_by)==0?B(_5J(_38,[0,_bw],_bu)):true;},_bz=function(_bA){return new F(function(){return _bv(E(_bA)[1]);});},_bB=new T(function(){return B(unCStr(",;()[]{}`"));}),_bC=new T(function(){return B(unCStr(".."));}),_bD=new T(function(){return B(unCStr("::"));}),_bE=new T(function(){return B(unCStr("->"));}),_bF=[0,64],_bG=[1,_bF,_10],_bH=[0,126],_bI=[1,_bH,_10],_bJ=new T(function(){return B(unCStr("=>"));}),_bK=[1,_bJ,_10],_bL=[1,_bI,_bK],_bM=[1,_bG,_bL],_bN=[1,_bE,_bM],_bO=new T(function(){return B(unCStr("<-"));}),_bP=[1,_bO,_bN],_bQ=[0,124],_bR=[1,_bQ,_10],_bS=[1,_bR,_bP],_bT=[1,_6c,_10],_bU=[1,_bT,_bS],_bV=[0,61],_bW=[1,_bV,_10],_bX=[1,_bW,_bU],_bY=[1,_bD,_bX],_bZ=[1,_bC,_bY],_c0=function(_c1){return new F(function(){return _2q([1,function(_c2){return E(_c2)[0]==0?E(new T(function(){return B(A(_c1,[_48]));})):[2];}],new T(function(){return B(_2q([0,function(_c3){return E(E(_c3)[1])==39?E([0,function(_c4){var _c5=E(_c4);switch(E(_c5[1])){case 39:return [2];case 92:return E(new T(function(){return B(_ao(function(_c6){return [0,function(_c7){return E(E(_c7)[1])==39?E(new T(function(){return B(A(_c1,[[0,_c6]]));})):[2];}];}));}));default:return [0,function(_c8){return E(E(_c8)[1])==39?E(new T(function(){return B(A(_c1,[[0,_c5]]));})):[2];}];}}]):[2];}],new T(function(){return B(_2q([0,function(_c9){return E(E(_c9)[1])==34?E(new T(function(){return B(_bm(_49,_c1));})):[2];}],new T(function(){return B(_2q([0,function(_ca){return !B(_5J(_38,_ca,_bB))?[2]:B(A(_c1,[[2,[1,_ca,_10]]]));}],new T(function(){return B(_2q([0,function(_cb){return !B(_5J(_38,_cb,_5O))?[2]:[1,B(_3X(_5P,function(_cc){var _cd=[1,_cb,_cc];return !B(_5J(_3h,_cd,_bZ))?B(A(_c1,[[4,_cd]])):B(A(_c1,[[2,_cd]]));}))];}],new T(function(){return B(_2q([0,function(_ce){var _cf=E(_ce),_cg=_cf[1],_ch=u_iswalpha(_cg),_ci=_ch;return E(_ci)==0?E(_cg)==95?[1,B(_3X(_bz,function(_cj){return new F(function(){return A(_c1,[[3,[1,_cf,_cj]]]);});}))]:[2]:[1,B(_3X(_bz,function(_ck){return new F(function(){return A(_c1,[[3,[1,_cf,_ck]]]);});}))];}],new T(function(){return [1,B(_3B(_61,_5F,_c1))];})));})));})));})));})));}));});},_cl=[0,0],_cm=function(_cn,_co){return function(_cp){return new F(function(){return A(_aK,[_cp,function(_cq){return E(new T(function(){return B(_c0(function(_cr){var _cs=E(_cr);return _cs[0]==2?!B(_2X(_cs[1],_2W))?[2]:E(new T(function(){return B(A(_cn,[_cl,function(_ct){return [1,function(_cu){return new F(function(){return A(_aK,[_cu,function(_cv){return E(new T(function(){return B(_c0(function(_cw){var _cx=E(_cw);return _cx[0]==2?!B(_2X(_cx[1],_2U))?[2]:E(new T(function(){return B(A(_co,[_ct]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_cy=function(_cz,_cA,_cB){var _cC=function(_cD,_cE){return new F(function(){return _2q([1,function(_cF){return new F(function(){return A(_aK,[_cF,function(_cG){return E(new T(function(){return B(_c0(function(_cH){var _cI=E(_cH);if(_cI[0]==4){var _cJ=E(_cI[1]);if(!_cJ[0]){return new F(function(){return A(_cz,[_cI,_cD,_cE]);});}else{return E(E(_cJ[1])[1])==45?E(_cJ[2])[0]==0?E([1,function(_cK){return new F(function(){return A(_aK,[_cK,function(_cL){return E(new T(function(){return B(_c0(function(_cM){return new F(function(){return A(_cz,[_cM,_cD,function(_cN){return new F(function(){return A(_cE,[new T(function(){return [0, -E(_cN)[1]];})]);});}]);});}));}));}]);});}]):B(A(_cz,[_cI,_cD,_cE])):B(A(_cz,[_cI,_cD,_cE]));}}else{return new F(function(){return A(_cz,[_cI,_cD,_cE]);});}}));}));}]);});}],new T(function(){return [1,B(_cm(_cC,_cE))];}));});};return new F(function(){return _cC(_cA,_cB);});},_cO=function(_cP,_cQ){return [2];},_cR=function(_cS){var _cT=E(_cS);return _cT[0]==0?[1,new T(function(){return B(_59(new T(function(){return B(_4Z(E(_cT[1])[1]));}),_4Y,_cT[2]));})]:E(_cT[2])[0]==0?E(_cT[3])[0]==0?[1,new T(function(){return B(_59(_4X,_4Y,_cT[1]));})]:[0]:[0];},_cU=function(_cV){var _cW=E(_cV);if(_cW[0]==5){var _cX=B(_cR(_cW[1]));return _cX[0]==0?E(_cO):function(_cY,_cZ){return new F(function(){return A(_cZ,[new T(function(){return [0,B(_6u(_cX[1]))];})]);});};}else{return E(_cO);}},_d0=function(_d1){return [1,function(_d2){return new F(function(){return A(_aK,[_d2,function(_d3){return E([3,_d1,_3t]);}]);});}];},_d4=new T(function(){return B(_cy(_cU,_cl,_d0));}),_d5=new T(function(){return B(unCStr("clientHeight"));}),_d6=new T(function(){return B(unCStr("scrollHeight"));}),_d7=new T(function(){return B(unCStr("scrollTop"));}),_d8=function(_d9){while(1){var _da=(function(_db){var _dc=E(_db);if(!_dc[0]){return [0];}else{var _dd=_dc[2],_de=E(_dc[1]);if(!E(_de[2])[0]){return [1,_de[1],new T(function(){return B(_d8(_dd));})];}else{_d9=_dd;return null;}}})(_d9);if(_da!=null){return _da;}}},_df=function(_dg,_dh,_di,_){var _dj=B(_0(_di,_d7,_)),_dk=_dj,_dl=B(_0(_di,_d6,_)),_dm=_dl,_dn=B(_0(_di,_d5,_)),_do=_dn,_dp=B(_d8(B(_2g(_d4,_dm))));if(!_dp[0]){return E(_S);}else{if(!E(_dp[2])[0]){var _dq=B(_d8(B(_2g(_d4,_dk))));if(!_dq[0]){return E(_S);}else{if(!E(_dq[2])[0]){var _dr=E(_dq[1])[1],_ds=B(_d8(B(_2g(_d4,_do))));if(!_ds[0]){return E(_S);}else{if(!E(_ds[2])[0]){if((E(_dp[1])[1]-_dr|0)!=E(_ds[1])[1]){if(!E(_dr)){return new F(function(){return _v(E(_dg)[1],_dh,[0,_di],_);});}else{return _e;}}else{return new F(function(){return _f(E(_dg)[1],_dh,[0,_di],_);});}}else{return E(_Q);}}}else{return E(_Q);}}}else{return E(_Q);}}},_dt=new T(function(){return [0,"wheel"];}),_du=[0,0],_dv=function(_dw){var _dx=E(_dw);if(!_dx[0]){return [0];}else{return new F(function(){return _T(_dx[1],new T(function(){return B(_dv(_dx[2]));},1));});}},_dy=function(_dz,_dA){if(_dz<=_dA){var _dB=function(_dC){return [1,[0,_dC],new T(function(){if(_dC!=_dA){var _dD=B(_dB(_dC+1|0));}else{var _dD=[0];}var _dE=_dD;return _dE;})];};return new F(function(){return _dB(_dz);});}else{return [0];}},_dF=[0,42],_dG=[1,_dF,_10],_dH=[0,_dG,_10],_dI=[1,_dH,_10],_dJ=new T(function(){return B(unCStr("lneg"));}),_dK=new T(function(){return B(unCStr("lor"));}),_dL=[1,_dJ,_10],_dM=new T(function(){return B(unCStr("liff"));}),_dN=[1,_dM,_dL],_dO=new T(function(){return B(unCStr("lif"));}),_dP=[1,_dO,_dN],_dQ=[1,_dK,_dP],_dR=[1,_dM,_10],_dS=[1,_dO,_dR],_dT=[1,_dK,_dS],_dU=new T(function(){return B(unCStr("land"));}),_dV=function(_dW){var _dX=E(_dW);if(!_dX){return E(_dI);}else{var _dY=_dX-1|0,_dZ=function(_e0){while(1){var _e1=(function(_e2){var _e3=E(_e2);if(!_e3[0]){return [0];}else{var _e4=_e3[2],_e5=E(_e3[1])[1],_e6=new T(function(){return B(_dV(_e5));}),_e7=new T(function(){return B(_dV(_dY-_e5|0));}),_e8=function(_e9){while(1){var _ea=(function(_eb){var _ec=E(_eb);if(!_ec[0]){return [0];}else{var _ed=_ec[1],_ee=_ec[2],_ef=function(_eg){while(1){var _eh=(function(_ei){var _ej=E(_ei);if(!_ej[0]){return [0];}else{var _ek=_ej[1],_el=_ej[2],_em=[0,_ed,[1,_ek,_10]],_en=E(_e7);if(!_en[0]){_eg=_el;return null;}else{var _eo=_en[2];return !E(new T(function(){return B(_2X(_ed,_dJ));}))?[1,[0,_ed,[1,_ek,[1,_en[1],_10]]],new T(function(){var _ep=function(_eq){var _er=E(_eq);return _er[0]==0?[0]:[1,[0,_ed,[1,_ek,[1,_er[1],_10]]],new T(function(){return B(_ep(_er[2]));})];};return B(_T(B(_ep(_eo)),new T(function(){return B(_ef(_el));},1)));})]:[1,_em,new T(function(){var _es=function(_et){var _eu=E(_et);return _eu[0]==0?[0]:[1,_em,new T(function(){return B(_es(_eu[2]));})];};return B(_T(B(_es(_eo)),new T(function(){return B(_ef(_el));},1)));})];}}})(_eg);if(_eh!=null){return _eh;}}},_ev=B(_ef(_e6));if(!_ev[0]){_e9=_ee;return null;}else{return [1,_ev[1],new T(function(){return B(_T(_ev[2],new T(function(){return B(_e8(_ee));},1)));})];}}})(_e9);if(_ea!=null){return _ea;}}},_ew=function(_ex,_ey){var _ez=function(_eA){while(1){var _eB=(function(_eC){var _eD=E(_eC);if(!_eD[0]){return [0];}else{var _eE=_eD[1],_eF=_eD[2],_eG=[0,_ex,[1,_eE,_10]],_eH=E(_e7);if(!_eH[0]){_eA=_eF;return null;}else{var _eI=_eH[2];return !E(new T(function(){return B(_2X(_ex,_dJ));}))?[1,[0,_ex,[1,_eE,[1,_eH[1],_10]]],new T(function(){var _eJ=function(_eK){var _eL=E(_eK);return _eL[0]==0?[0]:[1,[0,_ex,[1,_eE,[1,_eL[1],_10]]],new T(function(){return B(_eJ(_eL[2]));})];};return B(_T(B(_eJ(_eI)),new T(function(){return B(_ez(_eF));},1)));})]:[1,_eG,new T(function(){var _eM=function(_eN){var _eO=E(_eN);return _eO[0]==0?[0]:[1,_eG,new T(function(){return B(_eM(_eO[2]));})];};return B(_T(B(_eM(_eI)),new T(function(){return B(_ez(_eF));},1)));})];}}})(_eA);if(_eB!=null){return _eB;}}},_eP=B(_ez(_e6));return _eP[0]==0?B(_e8(_ey)):[1,_eP[1],new T(function(){return B(_T(_eP[2],new T(function(){return B(_e8(_ey));},1)));})];};if(_e5!=_dY){var _eQ=B(_ew(_dU,_dT));if(!_eQ[0]){_e0=_e4;return null;}else{return [1,_eQ[1],new T(function(){return B(_T(_eQ[2],new T(function(){return B(_dZ(_e4));},1)));})];}}else{var _eR=B(_ew(_dU,_dQ));if(!_eR[0]){_e0=_e4;return null;}else{return [1,_eR[1],new T(function(){return B(_T(_eR[2],new T(function(){return B(_dZ(_e4));},1)));})];}}}})(_e0);if(_e1!=null){return _e1;}}};return new F(function(){return _dZ(B(_dy(0,_dY)));});}},_eS=function(_eT,_eU){return !E(_eT)?!E(_eU)?true:false:E(_eU);},_eV=function(_eW,_eX){return !E(_eW)?true:E(_eX);},_eY=function(_eZ,_f0){return !E(_eZ)?false:E(_f0);},_f1=function(_f2){return !E(_f2)?true:false;},_f3=function(_f4,_f5){return !E(_f4)?E(_f5):true;},_f6=function(_f7,_f8){switch(E(_f8)[0]){case 0:return E(_f1);case 1:return E(_eY);case 2:return E(_f3);case 3:return E(_eV);default:return E(_eS);}},_f9=function(_fa,_fb){return new F(function(){return A(_fa,[E(_fb)[2]]);});},_fc=new T(function(){return B(unCStr("Prelude.undefined"));}),_fd=new T(function(){return B(err(_fc));}),_fe=function(_ff,_fg,_fh,_fi){var _fj=E(_fi);switch(_fj[0]){case 0:return E(_fd);case 1:return new F(function(){return A(_fg,[_fh,_fj[1]]);});break;case 2:return new F(function(){return A(_ff,[_fh,_fj[1],new T(function(){return B(_fe(_ff,_fg,_fh,_fj[2]));})]);});break;default:return new F(function(){return A(_ff,[_fh,_fj[1],new T(function(){return B(_fe(_ff,_fg,_fh,_fj[2]));}),new T(function(){return B(_fe(_ff,_fg,_fh,_fj[3]));})]);});}},_fk=function(_fl,_fm,_fn,_fo,_fp,_fq,_fr){var _fs=E(_fr);switch(_fs[0]){case 0:return E(_fd);case 1:return new F(function(){return A(_fp,[_fq,_fs[1]]);});break;case 2:return new F(function(){return A(_fl,[_fq,_fs[1],new T(function(){return B(_fe(_fo,_fp,_fq,_fs[2]));})]);});break;case 3:return new F(function(){return A(_fl,[_fq,_fs[1],new T(function(){return B(_fe(_fo,_fp,_fq,_fs[2]));}),new T(function(){return B(_fe(_fo,_fp,_fq,_fs[3]));})]);});break;case 4:return new F(function(){return A(_fm,[_fq,_fs[1],new T(function(){return B(_fk(_fl,_fm,_fn,_fo,_fp,_fq,_fs[2]));})]);});break;case 5:return new F(function(){return A(_fm,[_fq,_fs[1],new T(function(){return B(_fk(_fl,_fm,_fn,_fo,_fp,_fq,_fs[2]));}),new T(function(){return B(_fk(_fl,_fm,_fn,_fo,_fp,_fq,_fs[3]));})]);});break;default:return new F(function(){return A(_fn,[_fq,_fs[1],function(_ft){return new F(function(){return _fk(_fl,_fm,_fn,_fo,_fp,_fq,B(A(_fs[2],[[1,_ft]])));});}]);});}},_fu=function(_fv,_fw){return E(_fd);},_fx=[1,_63,_10],_fy=function(_fz){return false;},_fA=[1,_fy,_10],_fB=function(_fC){var _fD=E(_fC);if(!_fD){return E(_fA);}else{var _fE=new T(function(){return B(_fB(_fD-1|0));}),_fF=function(_fG){while(1){var _fH=(function(_fI){var _fJ=E(_fI);if(!_fJ[0]){return [0];}else{var _fK=_fJ[2],_fL=function(_fM){var _fN=E(_fM);return _fN[0]==0?[0]:[1,function(_fO){var _fP=E(_fO);return _fP[1]>=_fD?E(_fJ[1]):B(A(_fN[1],[_fP]));},new T(function(){return B(_fL(_fN[2]));})];},_fQ=B(_fL(_fE));if(!_fQ[0]){_fG=_fK;return null;}else{return [1,_fQ[1],new T(function(){return B(_T(_fQ[2],new T(function(){return B(_fF(_fK));},1)));})];}}})(_fG);if(_fH!=null){return _fH;}}};return new F(function(){return (function(_fR,_fS){var _fT=function(_fU){var _fV=E(_fU);return _fV[0]==0?[0]:[1,function(_fW){var _fX=E(_fW);return _fX[1]>=_fD?E(_fR):B(A(_fV[1],[_fX]));},new T(function(){return B(_fT(_fV[2]));})];},_fY=B(_fT(_fE));return _fY[0]==0?B(_fF(_fS)):[1,_fY[1],new T(function(){return B(_T(_fY[2],new T(function(){return B(_fF(_fS));},1)));})];})(_64,_fx);});}},_fZ=function(_g0,_g1){while(1){var _g2=E(_g1);if(!_g2[0]){return true;}else{if(!B(A(_g0,[_g2[1]]))){return false;}else{_g1=_g2[2];continue;}}}},_g3=function(_g4,_g5){var _g6=function(_g7){var _g8=E(_g7);return _g8[0]==0?[0]:[1,new T(function(){return B(_fk(_fu,_f6,_fu,_fu,_f9,_g8[1],_g5));}),new T(function(){return B(_g6(_g8[2]));})];};return new F(function(){return _fZ(_49,B(_g6(B(_fB(_g4)))));});},_g9=function(_ga,_gb){while(1){var _gc=(function(_gd,_ge){var _gf=E(_ge);if(!_gf[0]){return [0];}else{var _gg=_gf[1],_gh=_gf[2];if(!B(A(_gd,[_gg]))){var _gi=_gd;_gb=_gh;_ga=_gi;return null;}else{return [1,_gg,new T(function(){return B(_g9(_gd,_gh));})];}}})(_ga,_gb);if(_gc!=null){return _gc;}}},_gj=function(_gk,_gl){while(1){var _gm=E(_gk);if(!_gm[0]){return E(_gl);}else{_gk=_gm[2];var _gn=_gl+E(_gm[1])[1]|0;_gl=_gn;continue;}}},_go=function(_gp,_gq){var _gr=E(_gq);return _gr[0]==0?[0]:[1,new T(function(){return B(A(_gp,[_gr[1]]));}),new T(function(){return B(_go(_gp,_gr[2]));})];},_gs=function(_gt){return [0,B(_gu(E(_gt)[2]))];},_gu=function(_gv){var _gw=E(_gv);if(!_gw[0]){return 1;}else{return new F(function(){return _gj(B(_go(_gs,_gw)),0);});}},_gx=[1,_],_gy=[3,_],_gz=[4,_],_gA=[0,_],_gB=[2,_],_gC=new T(function(){return B(unCStr(": empty list"));}),_gD=new T(function(){return B(unCStr("Prelude."));}),_gE=function(_gF){return new F(function(){return err(B(_T(_gD,new T(function(){return B(_T(_gF,_gC));},1))));});},_gG=new T(function(){return B(unCStr("head"));}),_gH=new T(function(){return B(_gE(_gG));}),_gI=function(_gJ,_gK){var _gL=E(_gK);return new F(function(){return _gM(_gJ,_gL[1],_gL[2]);});},_gN=function(_gO,_gP){while(1){var _gQ=E(_gO);if(!_gQ){return E(_gP);}else{var _gR=E(_gP);if(!_gR[0]){return [0];}else{_gO=_gQ-1|0;_gP=_gR[2];continue;}}}},_gS=function(_gT,_gU){var _gV=E(_gT);if(!_gV){return [0];}else{var _gW=E(_gU);return _gW[0]==0?[0]:[1,_gW[1],new T(function(){return B(_gS(_gV-1|0,_gW[2]));})];}},_gM=function(_gX,_gY,_gZ){var _h0=E(_gZ);if(!_h0[0]){return [1,[0,_,new T(function(){var _h1=E(_gX);return _h1[0]==0?E(_gH):E(_h1[1]);})]];}else{var _h2=_h0[1],_h3=E(_h0[2]);if(!_h3[0]){return [4,_gA,new T(function(){return B(_gI(_gX,_h2));})];}else{if(!E(_h3[2])[0]){var _h4=new T(function(){var _h5=E(_h2),_h6=_h5[2];return B(_gM(new T(function(){var _h7=B(_gu(_h6));if(_h7>0){var _h8=_h7<0?[0]:B(_gS(_h7,_gX));}else{var _h8=[0];}var _h9=_h8,_ha=_h9;return _ha;}),_h5[1],_h6));}),_hb=new T(function(){var _hc=E(_h3[1]);return B(_gM(new T(function(){var _hd=B(_gu(E(_h2)[2]));return _hd>=0?B(_gN(_hd,_gX)):E(_gX);}),_hc[1],_hc[2]));});return !B(_2X(_gY,_dU))?!B(_2X(_gY,_dO))?!B(_2X(_gY,_dM))?!B(_2X(_gY,_dK))?[5,_gx,_h4,_hb]:[5,_gB,_h4,_hb]:[5,_gz,_h4,_hb]:[5,_gy,_h4,_hb]:[5,_gx,_h4,_hb];}else{return [4,_gA,new T(function(){return B(_gI(_gX,_h2));})];}}}},_he=function(_hf,_hg){while(1){var _hh=E(_hg);if(!_hh[0]){return E(_hf);}else{var _hi=_hh[2],_hj=E(_hh[1])[1];if(_hf>_hj){_hg=_hi;continue;}else{_hf=_hj;_hg=_hi;continue;}}}},_hk=new T(function(){return B(unCStr("maximum"));}),_hl=new T(function(){return B(_gE(_hk));}),_hm=function(_hn){while(1){var _ho=(function(_hp){var _hq=E(_hp);if(!_hq[0]){return [0];}else{var _hr=_hq[2],_hs=E(_hq[1]);if(!_hs[0]){return E(_hl);}else{var _ht=function(_hu){var _hv=E(_hu);return _hv[0]==0?[0]:[1,[1,_hv[1],_hs],new T(function(){return B(_ht(_hv[2]));})];},_hw=B(_ht(B(_dy(1,B(_he(E(_hs[1])[1],_hs[2]))+1|0))));if(!_hw[0]){_hn=_hr;return null;}else{return [1,_hw[1],new T(function(){return B(_T(_hw[2],new T(function(){return B(_hm(_hr));},1)));})];}}}})(_hn);if(_ho!=null){return _ho;}}},_hx=[0,1],_hy=[1,_hx,_10],_hz=[1,_hy,_10],_hA=function(_hB){var _hC=E(_hB);if(_hC==1){return E(_hz);}else{return new F(function(){return _hm(B(_hA(_hC-1|0)));});}},_hD=function(_hE){while(1){var _hF=(function(_hG){var _hH=E(_hG);if(!_hH[0]){return [0];}else{var _hI=_hH[2],_hJ=E(_hH[1]),_hK=_hJ[2],_hL=function(_hM){var _hN=E(_hM);return _hN[0]==0?[0]:[1,new T(function(){return B(_gM(_hN[1],_hJ[1],_hK));}),new T(function(){return B(_hL(_hN[2]));})];},_hO=B(_hL(B(_hA(B(_gu(_hK))))));if(!_hO[0]){_hE=_hI;return null;}else{return [1,_hO[1],new T(function(){return B(_T(_hO[2],new T(function(){return B(_hD(_hI));},1)));})];}}})(_hE);if(_hF!=null){return _hF;}}},_hP=function(_hQ){return new F(function(){return _g9(function(_hR){return new F(function(){return _g3(_hQ+1|0,_hR);});},B(_hD(B(_dV(_hQ)))));});},_hS=function(_hT){return [1,new T(function(){return B(_hP(_hT));}),new T(function(){var _hU=E(_hT);if(_hU==2147483647){var _hV=[0];}else{var _hV=B(_hS(_hU+1|0));}return _hV;})];},_hW=new T(function(){return B(_hS(1));}),_hX=new T(function(){return B(_dv(_hW));}),_hY=function(_hZ,_i0){return E(_fd);},_i1=new T(function(){return B(unCStr(" \u2194 "));}),_i2=new T(function(){return B(unCStr(" \u2192 "));}),_i3=new T(function(){return B(unCStr(" \u2228 "));}),_i4=[0,41],_i5=[1,_i4,_10],_i6=new T(function(){return B(unCStr(" \u2227 "));}),_i7=[0,40],_i8=[0,172],_i9=function(_ia,_ib){switch(E(_ia)[0]){case 0:var _ic=E(_ib);return _ic[0]==0?E(_fd):E(_ic[2])[0]==0?[0,_i8,_ic[1]]:E(_fd);case 1:var _id=E(_ib);if(!_id[0]){return E(_fd);}else{var _ie=E(_id[2]);return _ie[0]==0?E(_fd):E(_ie[2])[0]==0?[0,_i7,new T(function(){return B(_T(_id[1],new T(function(){return B(_T(_i6,new T(function(){return B(_T(_ie[1],_i5));},1)));},1)));})]:E(_fd);}break;case 2:var _if=E(_ib);if(!_if[0]){return E(_fd);}else{var _ig=E(_if[2]);return _ig[0]==0?E(_fd):E(_ig[2])[0]==0?[0,_i7,new T(function(){return B(_T(_if[1],new T(function(){return B(_T(_i3,new T(function(){return B(_T(_ig[1],_i5));},1)));},1)));})]:E(_fd);}break;case 3:var _ih=E(_ib);if(!_ih[0]){return E(_fd);}else{var _ii=E(_ih[2]);return _ii[0]==0?E(_fd):E(_ii[2])[0]==0?[0,_i7,new T(function(){return B(_T(_ih[1],new T(function(){return B(_T(_i2,new T(function(){return B(_T(_ii[1],_i5));},1)));},1)));})]:E(_fd);}break;default:var _ij=E(_ib);if(!_ij[0]){return E(_fd);}else{var _ik=E(_ij[2]);return _ik[0]==0?E(_fd):E(_ik[2])[0]==0?[0,_i7,new T(function(){return B(_T(_ij[1],new T(function(){return B(_T(_i1,new T(function(){return B(_T(_ik[1],_i5));},1)));},1)));})]:E(_fd);}}},_il=function(_im,_in){var _io=B(_i9(_im,_in));return [1,_io[1],_io[2]];},_ip=function(_iq){return new F(function(){return unAppCStr("P_",new T(function(){return B(_6m(0,E(E(_iq)[2])[1],_10));}));});},_ir=function(_is,_it){return new F(function(){return _ip(_is);});},_iu=function(_iv,_iw,_ix,_iy){var _iz=E(_ix);switch(_iz[0]){case 0:var _iA=E(_iy);return _iA[0]==0?E(_fd):E(_iA[1]);case 1:return new F(function(){return A(_iv,[_iz[1],_10]);});break;case 2:return new F(function(){return A(_iw,[_iz[1],[1,new T(function(){return B(_iu(_iv,_iw,_iz[2],_iy));}),_10]]);});break;default:return new F(function(){return A(_iw,[_iz[1],[1,new T(function(){return B(_iu(_iv,_iw,_iz[2],_iy));}),[1,new T(function(){return B(_iu(_iv,_iw,_iz[3],_iy));}),_10]]]);});}},_iB=[0],_iC=function(_iD,_iE,_iF,_iG,_iH,_iI,_iJ,_iK){var _iL=E(_iJ);switch(_iL[0]){case 0:return [0];case 1:return new F(function(){return A(_iG,[_iL[1],_10]);});break;case 2:return new F(function(){return A(_iD,[_iL[1],[1,new T(function(){return B(_iu(_iG,_iH,_iL[2],_iK));}),_10]]);});break;case 3:return new F(function(){return A(_iD,[_iL[1],[1,new T(function(){return B(_iu(_iG,_iH,_iL[2],_iK));}),[1,new T(function(){return B(_iu(_iG,_iH,_iL[3],_iK));}),_10]]]);});break;case 4:return new F(function(){return A(_iE,[_iL[1],[1,new T(function(){return B(_iC(_iD,_iE,_iF,_iG,_iH,_iI,_iL[2],_iK));}),_10]]);});break;case 5:return new F(function(){return A(_iE,[_iL[1],[1,new T(function(){return B(_iC(_iD,_iE,_iF,_iG,_iH,_iI,_iL[2],_iK));}),[1,new T(function(){return B(_iC(_iD,_iE,_iF,_iG,_iH,_iI,_iL[3],_iK));}),_10]]]);});break;default:var _iM=_iL[1],_iN=_iL[2];return new F(function(){return A(_iF,[_iM,[1,new T(function(){return B(A(_iI,[new T(function(){return B(A(_iN,[_iB]));}),_iM]));}),[1,new T(function(){return B(_iC(_iD,_iE,_iF,_iG,_iH,_iI,B(A(_iN,[_iB])),[1,new T(function(){return B(A(_iI,[new T(function(){return B(A(_iN,[_iB]));}),_iM]));}),_10]));}),_10]]]);});}},_iO=function(_iP){return E(_fd);},_iQ=[0,95],_iR=[1,_iQ,_10],_iS=[1,_iR,_10],_iT=new T(function(){return B(unCStr("innerHTML"));}),_iU=function(_iV,_){var _iW=jsCreateElem("div"),_iX=_iW,_iY=jsSet(_iX,toJSStr(E(_iT)),toJSStr(B(_iC(_iO,_il,_iO,_ir,_iO,_hY,_iV,_iS))));return [0,_iX];},_iZ=new T(function(){return B(_go(_iU,_hX));}),_j0=function(_){var _j1=jsElemsByClassName("scrollbox"),_j2=_j1,_j3=nMV(_du),_j4=_j3,_j5=[0,_j4],_j6=E(_j2);if(!_j6[0]){return _e;}else{var _j7=_j6[1],_j8=E(_dt)[1],_j9=jsSetCB(E(_j7)[1],_j8,function(_ja,_jb,_){return new F(function(){return _df(_j5,_iZ,E(_j7)[1],_);});}),_jc=_j9;return new F(function(){return (function(_jd,_){while(1){var _je=(function(_jf,_){var _jg=E(_jf);if(!_jg[0]){return _e;}else{var _jh=_jg[1],_ji=jsSetCB(E(_jh)[1],_j8,function(_jj,_jk,_){return new F(function(){return _df(_j5,_iZ,E(_jh)[1],_);});}),_jl=_ji;_jd=_jg[2];return null;}})(_jd,_);if(_je!=null){return _je;}}})(_j6[2],_);});}},_jm=function(_){return new F(function(){return _j0(_);});};
var hasteMain = function() {B(A(_jm, [0]));};window.onload = hasteMain;