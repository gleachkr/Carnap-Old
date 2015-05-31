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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_1p=new T(function(){return B(err(_1o));}),_1q=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_1r=new T(function(){return B(err(_1q));}),_1s=function(_1t,_1u){while(1){var _1v=E(_1t);if(!_1v[0]){return E(_1r);}else{var _1w=E(_1u);if(!_1w){return E(_1v[1]);}else{_1t=_1v[2];_1u=_1w-1|0;continue;}}}},_1x=0,_1y=function(_1z,_1A,_1B,_){var _1C=rMV(_1z),_1D=_1C,_1E=E(_1D)[1],_1F=function(_){var _=wMV(_1z,[0,_1E+1|0]);if(_1E>=0){var _1G=B(A(_1s,[_1A,_1E,_])),_1H=_1G,_1I=jsAppendChild(E(_1H)[1],E(_1B)[1]);return _1x;}else{return E(_1p);}};if(_1E<=100){return new F(function(){return _1F(_);});}else{var _1J=E(_1B)[1],_1K=jsGetFirstChild(_1J),_1L=_1K,_1M=E(_1L);if(!_1M[0]){return new F(function(){return _1F(_);});}else{var _1N=jsKillChild(E(_1M[1])[1],_1J);return new F(function(){return _1F(_);});}}},_1O=function(_1P,_1Q,_1R,_){var _1S=rMV(_1P),_1T=_1S,_1U=E(_1T)[1];if(_1U<=100){return _1x;}else{var _1V=E(_1R)[1],_1W=jsGetLastChild(_1V),_1X=_1W,_1Y=function(_){var _=wMV(_1P,[0,_1U-1|0]),_1Z=jsGetFirstChild(_1V),_20=_1Z,_21=_1U-100|0;if(_21>=0){var _22=B(A(_1s,[_1Q,_21,_])),_23=_22,_24=E(_20);if(!_24[0]){return _1x;}else{var _25=jsAddChildBefore(E(_23)[1],_1V,E(_24[1])[1]);return _1x;}}else{return E(_1p);}},_26=E(_1X);if(!_26[0]){return new F(function(){return _1Y(_);});}else{var _27=jsKillChild(E(_26[1])[1],_1V);return new F(function(){return _1Y(_);});}}},_28=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_29=new T(function(){return B(err(_28));}),_2a=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_2b=new T(function(){return B(err(_2a));}),_2c=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2d=new T(function(){return B(unCStr("base"));}),_2e=new T(function(){return B(unCStr("PatternMatchFail"));}),_2f=new T(function(){var _2g=hs_wordToWord64(18445595),_2h=_2g,_2i=hs_wordToWord64(52003073),_2j=_2i;return [0,_2h,_2j,[0,_2h,_2j,_2d,_2c,_2e],_9];}),_2k=function(_2l){return E(_2f);},_2m=function(_2n){return E(E(_2n)[1]);},_2o=function(_2p,_2q,_2r){var _2s=B(A(_2p,[_])),_2t=B(A(_2q,[_])),_2u=hs_eqWord64(_2s[1],_2t[1]),_2v=_2u;if(!E(_2v)){return [0];}else{var _2w=hs_eqWord64(_2s[2],_2t[2]),_2x=_2w;return E(_2x)==0?[0]:[1,_2r];}},_2y=function(_2z){var _2A=E(_2z);return new F(function(){return _2o(B(_2m(_2A[1])),_2k,_2A[2]);});},_2B=function(_2C){return E(E(_2C)[1]);},_2D=function(_2E,_2F){return new F(function(){return _e(E(_2E)[1],_2F);});},_2G=[0,44],_2H=[0,93],_2I=[0,91],_2J=function(_2K,_2L,_2M){var _2N=E(_2L);return _2N[0]==0?B(unAppCStr("[]",_2M)):[1,_2I,new T(function(){return B(A(_2K,[_2N[1],new T(function(){var _2O=function(_2P){var _2Q=E(_2P);return _2Q[0]==0?E([1,_2H,_2M]):[1,_2G,new T(function(){return B(A(_2K,[_2Q[1],new T(function(){return B(_2O(_2Q[2]));})]));})];};return B(_2O(_2N[2]));})]));})];},_2R=function(_2S,_2T){return new F(function(){return _2J(_2D,_2S,_2T);});},_2U=function(_2V,_2W,_2X){return new F(function(){return _e(E(_2W)[1],_2X);});},_2Y=[0,_2U,_2B,_2R],_2Z=new T(function(){return [0,_2k,_2Y,_30,_2y];}),_30=function(_31){return [0,_2Z,_31];},_32=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_33=function(_34,_35){return new F(function(){return die(new T(function(){return B(A(_35,[_34]));}));});},_36=function(_37,_38){var _39=E(_38);if(!_39[0]){return [0,_9,_9];}else{var _3a=_39[1];if(!B(A(_37,[_3a]))){return [0,_9,_39];}else{var _3b=new T(function(){var _3c=B(_36(_37,_39[2]));return [0,_3c[1],_3c[2]];});return [0,[1,_3a,new T(function(){return E(E(_3b)[1]);})],new T(function(){return E(E(_3b)[2]);})];}}},_3d=[0,32],_3e=[0,10],_3f=[1,_3e,_9],_3g=function(_3h){return E(E(_3h)[1])==124?false:true;},_3i=function(_3j,_3k){var _3l=B(_36(_3g,B(unCStr(_3j)))),_3m=_3l[1],_3n=function(_3o,_3p){return new F(function(){return _e(_3o,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_3k,new T(function(){return B(_e(_3p,_3f));},1)));})));},1));});},_3q=E(_3l[2]);if(!_3q[0]){return new F(function(){return _3n(_3m,_9);});}else{return E(E(_3q[1])[1])==124?B(_3n(_3m,[1,_3d,_3q[2]])):B(_3n(_3m,_9));}},_3r=function(_3s){return new F(function(){return _33([0,new T(function(){return B(_3i(_3s,_32));})],_30);});},_3t=new T(function(){return B(_3r("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_3u=function(_3v,_3w){while(1){var _3x=(function(_3y,_3z){var _3A=E(_3y);switch(_3A[0]){case 0:var _3B=E(_3z);if(!_3B[0]){return [0];}else{_3v=B(A(_3A[1],[_3B[1]]));_3w=_3B[2];return null;}break;case 1:var _3C=B(A(_3A[1],[_3z])),_3D=_3z;_3v=_3C;_3w=_3D;return null;case 2:return [0];case 3:return [1,[0,_3A[1],_3z],new T(function(){return B(_3u(_3A[2],_3z));})];default:return E(_3A[1]);}})(_3v,_3w);if(_3x!=null){return _3x;}}},_3E=function(_3F,_3G){var _3H=function(_3I){var _3J=E(_3G);if(_3J[0]==3){return [3,_3J[1],new T(function(){return B(_3E(_3F,_3J[2]));})];}else{var _3K=E(_3F);if(_3K[0]==2){return E(_3J);}else{var _3L=E(_3J);if(_3L[0]==2){return E(_3K);}else{var _3M=function(_3N){var _3O=E(_3L);if(_3O[0]==4){return [1,function(_3P){return [4,new T(function(){return B(_e(B(_3u(_3K,_3P)),_3O[1]));})];}];}else{var _3Q=E(_3K);if(_3Q[0]==1){var _3R=_3Q[1],_3S=E(_3O);return _3S[0]==0?[1,function(_3T){return new F(function(){return _3E(B(A(_3R,[_3T])),_3S);});}]:[1,function(_3U){return new F(function(){return _3E(B(A(_3R,[_3U])),new T(function(){return B(A(_3S[1],[_3U]));}));});}];}else{var _3V=E(_3O);return _3V[0]==0?E(_3t):[1,function(_3W){return new F(function(){return _3E(_3Q,new T(function(){return B(A(_3V[1],[_3W]));}));});}];}}},_3X=E(_3K);switch(_3X[0]){case 1:var _3Y=E(_3L);if(_3Y[0]==4){return [1,function(_3Z){return [4,new T(function(){return B(_e(B(_3u(B(A(_3X[1],[_3Z])),_3Z)),_3Y[1]));})];}];}else{return new F(function(){return _3M(_);});}break;case 4:var _40=_3X[1],_41=E(_3L);switch(_41[0]){case 0:return [1,function(_42){return [4,new T(function(){return B(_e(_40,new T(function(){return B(_3u(_41,_42));},1)));})];}];case 1:return [1,function(_43){return [4,new T(function(){return B(_e(_40,new T(function(){return B(_3u(B(A(_41[1],[_43])),_43));},1)));})];}];default:return [4,new T(function(){return B(_e(_40,_41[1]));})];}break;default:return new F(function(){return _3M(_);});}}}}},_44=E(_3F);switch(_44[0]){case 0:var _45=E(_3G);if(!_45[0]){return [0,function(_46){return new F(function(){return _3E(B(A(_44[1],[_46])),new T(function(){return B(A(_45[1],[_46]));}));});}];}else{return new F(function(){return _3H(_);});}break;case 3:return [3,_44[1],new T(function(){return B(_3E(_44[2],_3G));})];default:return new F(function(){return _3H(_);});}},_47=[0,41],_48=[1,_47,_9],_49=[0,40],_4a=[1,_49,_9],_4b=function(_4c,_4d){while(1){var _4e=E(_4c);if(!_4e[0]){return E(_4d)[0]==0?true:false;}else{var _4f=E(_4d);if(!_4f[0]){return false;}else{if(E(_4e[1])[1]!=E(_4f[1])[1]){return false;}else{_4c=_4e[2];_4d=_4f[2];continue;}}}}},_4g=function(_4h,_4i){return E(_4h)[1]!=E(_4i)[1];},_4j=function(_4k,_4l){return E(_4k)[1]==E(_4l)[1];},_4m=[0,_4j,_4g],_4n=function(_4o,_4p){while(1){var _4q=E(_4o);if(!_4q[0]){return E(_4p)[0]==0?true:false;}else{var _4r=E(_4p);if(!_4r[0]){return false;}else{if(E(_4q[1])[1]!=E(_4r[1])[1]){return false;}else{_4o=_4q[2];_4p=_4r[2];continue;}}}}},_4s=function(_4t,_4u){return !B(_4n(_4t,_4u))?true:false;},_4v=[0,_4n,_4s],_4w=function(_4x,_4y){var _4z=E(_4x);switch(_4z[0]){case 0:return [0,function(_4A){return new F(function(){return _4w(B(A(_4z[1],[_4A])),_4y);});}];case 1:return [1,function(_4B){return new F(function(){return _4w(B(A(_4z[1],[_4B])),_4y);});}];case 2:return [2];case 3:return new F(function(){return _3E(B(A(_4y,[_4z[1]])),new T(function(){return B(_4w(_4z[2],_4y));}));});break;default:var _4C=function(_4D){var _4E=E(_4D);if(!_4E[0]){return [0];}else{var _4F=E(_4E[1]);return new F(function(){return _e(B(_3u(B(A(_4y,[_4F[1]])),_4F[2])),new T(function(){return B(_4C(_4E[2]));},1));});}},_4G=B(_4C(_4z[1]));return _4G[0]==0?[2]:[4,_4G];}},_4H=[2],_4I=function(_4J){return [3,_4J,_4H];},_4K=function(_4L,_4M){var _4N=E(_4L);if(!_4N){return new F(function(){return A(_4M,[_1x]);});}else{return [0,function(_4O){return E(new T(function(){return B(_4K(_4N-1|0,_4M));}));}];}},_4P=function(_4Q,_4R,_4S){return function(_4T){return new F(function(){return A(function(_4U,_4V,_4W){while(1){var _4X=(function(_4Y,_4Z,_50){var _51=E(_4Y);switch(_51[0]){case 0:var _52=E(_4Z);if(!_52[0]){return E(_4R);}else{_4U=B(A(_51[1],[_52[1]]));_4V=_52[2];var _53=_50+1|0;_4W=_53;return null;}break;case 1:var _54=B(A(_51[1],[_4Z])),_55=_4Z,_53=_50;_4U=_54;_4V=_55;_4W=_53;return null;case 2:return E(_4R);case 3:return function(_56){return new F(function(){return _4K(_50,function(_57){return E(new T(function(){return B(_4w(_51,_56));}));});});};default:return function(_58){return new F(function(){return _4w(_51,_58);});};}})(_4U,_4V,_4W);if(_4X!=null){return _4X;}}},[new T(function(){return B(A(_4Q,[_4I]));}),_4T,0,_4S]);});};},_59=function(_5a){return new F(function(){return A(_5a,[_9]);});},_5b=function(_5c,_5d){var _5e=function(_5f){var _5g=E(_5f);if(!_5g[0]){return E(_59);}else{var _5h=_5g[1];return !B(A(_5c,[_5h]))?E(_59):function(_5i){return [0,function(_5j){return E(new T(function(){return B(A(new T(function(){return B(_5e(_5g[2]));}),[function(_5k){return new F(function(){return A(_5i,[[1,_5h,_5k]]);});}]));}));}];};}};return function(_5l){return new F(function(){return A(_5e,[_5l,_5d]);});};},_5m=[6],_5n=function(_5o){return E(_5o);},_5p=new T(function(){return B(unCStr("valDig: Bad base"));}),_5q=new T(function(){return B(err(_5p));}),_5r=function(_5s,_5t){var _5u=function(_5v,_5w){var _5x=E(_5v);if(!_5x[0]){return function(_5y){return new F(function(){return A(_5y,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{var _5z=E(_5x[1])[1],_5A=function(_5B){return function(_5C){return [0,function(_5D){return E(new T(function(){return B(A(new T(function(){return B(_5u(_5x[2],function(_5E){return new F(function(){return A(_5w,[[1,_5B,_5E]]);});}));}),[_5C]));}));}];};};switch(E(E(_5s)[1])){case 8:if(48>_5z){return function(_5F){return new F(function(){return A(_5F,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{if(_5z>55){return function(_5G){return new F(function(){return A(_5G,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{return new F(function(){return _5A([0,_5z-48|0]);});}}break;case 10:if(48>_5z){return function(_5H){return new F(function(){return A(_5H,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{if(_5z>57){return function(_5I){return new F(function(){return A(_5I,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{return new F(function(){return _5A([0,_5z-48|0]);});}}break;case 16:if(48>_5z){if(97>_5z){if(65>_5z){return function(_5J){return new F(function(){return A(_5J,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{if(_5z>70){return function(_5K){return new F(function(){return A(_5K,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{return new F(function(){return _5A([0,(_5z-65|0)+10|0]);});}}}else{if(_5z>102){if(65>_5z){return function(_5L){return new F(function(){return A(_5L,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{if(_5z>70){return function(_5M){return new F(function(){return A(_5M,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{return new F(function(){return _5A([0,(_5z-65|0)+10|0]);});}}}else{return new F(function(){return _5A([0,(_5z-97|0)+10|0]);});}}}else{if(_5z>57){if(97>_5z){if(65>_5z){return function(_5N){return new F(function(){return A(_5N,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{if(_5z>70){return function(_5O){return new F(function(){return A(_5O,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{return new F(function(){return _5A([0,(_5z-65|0)+10|0]);});}}}else{if(_5z>102){if(65>_5z){return function(_5P){return new F(function(){return A(_5P,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{if(_5z>70){return function(_5Q){return new F(function(){return A(_5Q,[new T(function(){return B(A(_5w,[_9]));})]);});};}else{return new F(function(){return _5A([0,(_5z-65|0)+10|0]);});}}}else{return new F(function(){return _5A([0,(_5z-97|0)+10|0]);});}}}else{return new F(function(){return _5A([0,_5z-48|0]);});}}break;default:return E(_5q);}}};return function(_5R){return new F(function(){return A(_5u,[_5R,_5n,function(_5S){var _5T=E(_5S);return _5T[0]==0?[2]:B(A(_5t,[_5T]));}]);});};},_5U=[0,10],_5V=[0,1],_5W=[0,2147483647],_5X=function(_5Y,_5Z){while(1){var _60=E(_5Y);if(!_60[0]){var _61=_60[1],_62=E(_5Z);if(!_62[0]){var _63=_62[1],_64=addC(_61,_63);if(!E(_64[2])){return [0,_64[1]];}else{_5Y=[1,I_fromInt(_61)];_5Z=[1,I_fromInt(_63)];continue;}}else{_5Y=[1,I_fromInt(_61)];_5Z=_62;continue;}}else{var _65=E(_5Z);if(!_65[0]){_5Y=_60;_5Z=[1,I_fromInt(_65[1])];continue;}else{return [1,I_add(_60[1],_65[1])];}}}},_66=new T(function(){return B(_5X(_5W,_5V));}),_67=function(_68){var _69=E(_68);if(!_69[0]){var _6a=E(_69[1]);return _6a==(-2147483648)?E(_66):[0, -_6a];}else{return [1,I_negate(_69[1])];}},_6b=[0,10],_6c=[0,0],_6d=function(_6e){return [0,_6e];},_6f=function(_6g,_6h){while(1){var _6i=E(_6g);if(!_6i[0]){var _6j=_6i[1],_6k=E(_6h);if(!_6k[0]){var _6l=_6k[1];if(!(imul(_6j,_6l)|0)){return [0,imul(_6j,_6l)|0];}else{_6g=[1,I_fromInt(_6j)];_6h=[1,I_fromInt(_6l)];continue;}}else{_6g=[1,I_fromInt(_6j)];_6h=_6k;continue;}}else{var _6m=E(_6h);if(!_6m[0]){_6g=_6i;_6h=[1,I_fromInt(_6m[1])];continue;}else{return [1,I_mul(_6i[1],_6m[1])];}}}},_6n=function(_6o,_6p,_6q){while(1){var _6r=E(_6q);if(!_6r[0]){return E(_6p);}else{var _6s=B(_5X(B(_6f(_6p,_6o)),B(_6d(E(_6r[1])[1]))));_6q=_6r[2];_6p=_6s;continue;}}},_6t=function(_6u){var _6v=new T(function(){return B(_3E(B(_3E([0,function(_6w){return E(E(_6w)[1])==45?[1,B(_5r(_5U,function(_6x){return new F(function(){return A(_6u,[[1,new T(function(){return B(_67(B(_6n(_6b,_6c,_6x))));})]]);});}))]:[2];}],[0,function(_6y){return E(E(_6y)[1])==43?[1,B(_5r(_5U,function(_6z){return new F(function(){return A(_6u,[[1,new T(function(){return B(_6n(_6b,_6c,_6z));})]]);});}))]:[2];}])),new T(function(){return [1,B(_5r(_5U,function(_6A){return new F(function(){return A(_6u,[[1,new T(function(){return B(_6n(_6b,_6c,_6A));})]]);});}))];})));});return new F(function(){return _3E([0,function(_6B){return E(E(_6B)[1])==101?E(_6v):[2];}],[0,function(_6C){return E(E(_6C)[1])==69?E(_6v):[2];}]);});},_6D=[0],_6E=function(_6F){return new F(function(){return A(_6F,[_6D]);});},_6G=function(_6H){return new F(function(){return A(_6H,[_6D]);});},_6I=function(_6J){return function(_6K){return E(E(_6K)[1])==46?[1,B(_5r(_5U,function(_6L){return new F(function(){return A(_6J,[[1,_6L]]);});}))]:[2];};},_6M=function(_6N){return [0,B(_6I(_6N))];},_6O=function(_6P){return new F(function(){return _5r(_5U,function(_6Q){return [1,B(_4P(_6M,_6E,function(_6R){return [1,B(_4P(_6t,_6G,function(_6S){return new F(function(){return A(_6P,[[5,[1,_6Q,_6R,_6S]]]);});}))];}))];});});},_6T=function(_6U){return [1,B(_6O(_6U))];},_6V=function(_6W){return E(E(_6W)[1]);},_6X=function(_6Y,_6Z,_70){while(1){var _71=E(_70);if(!_71[0]){return false;}else{if(!B(A(_6V,[_6Y,_6Z,_71[1]]))){_70=_71[2];continue;}else{return true;}}}},_72=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_73=function(_74){return new F(function(){return _6X(_4m,_74,_72);});},_75=[0,8],_76=[0,16],_77=function(_78){var _79=function(_7a){return new F(function(){return A(_78,[[5,[0,_75,_7a]]]);});},_7b=function(_7c){return new F(function(){return A(_78,[[5,[0,_76,_7c]]]);});};return function(_7d){return E(E(_7d)[1])==48?E([0,function(_7e){switch(E(E(_7e)[1])){case 79:return [1,B(_5r(_75,_79))];case 88:return [1,B(_5r(_76,_7b))];case 111:return [1,B(_5r(_75,_79))];case 120:return [1,B(_5r(_76,_7b))];default:return [2];}}]):[2];};},_7f=function(_7g){return [0,B(_77(_7g))];},_7h=false,_7i=true,_7j=function(_7k){var _7l=new T(function(){return B(A(_7k,[_75]));}),_7m=new T(function(){return B(A(_7k,[_76]));});return function(_7n){switch(E(E(_7n)[1])){case 79:return E(_7l);case 88:return E(_7m);case 111:return E(_7l);case 120:return E(_7m);default:return [2];}};},_7o=function(_7p){return [0,B(_7j(_7p))];},_7q=[0,92],_7r=function(_7s){return new F(function(){return A(_7s,[_5U]);});},_7t=function(_7u){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_7u,_9));}))));});},_7v=function(_7w){var _7x=E(_7w);return _7x[0]==0?E(_7x[1]):I_toInt(_7x[1]);},_7y=function(_7z,_7A){var _7B=E(_7z);if(!_7B[0]){var _7C=_7B[1],_7D=E(_7A);return _7D[0]==0?_7C<=_7D[1]:I_compareInt(_7D[1],_7C)>=0;}else{var _7E=_7B[1],_7F=E(_7A);return _7F[0]==0?I_compareInt(_7E,_7F[1])<=0:I_compare(_7E,_7F[1])<=0;}},_7G=function(_7H){return [2];},_7I=function(_7J){var _7K=E(_7J);if(!_7K[0]){return E(_7G);}else{var _7L=_7K[1],_7M=E(_7K[2]);return _7M[0]==0?E(_7L):function(_7N){return new F(function(){return _3E(B(A(_7L,[_7N])),new T(function(){return B(A(new T(function(){return B(_7I(_7M));}),[_7N]));}));});};}},_7O=function(_7P){return [2];},_7Q=function(_7R,_7S){var _7T=function(_7U,_7V){var _7W=E(_7U);if(!_7W[0]){return function(_7X){return new F(function(){return A(_7X,[_7R]);});};}else{var _7Y=E(_7V);return _7Y[0]==0?E(_7O):E(_7W[1])[1]!=E(_7Y[1])[1]?E(_7O):function(_7Z){return [0,function(_80){return E(new T(function(){return B(A(new T(function(){return B(_7T(_7W[2],_7Y[2]));}),[_7Z]));}));}];};}};return function(_81){return new F(function(){return A(_7T,[_7R,_81,_7S]);});};},_82=new T(function(){return B(unCStr("SOH"));}),_83=[0,1],_84=function(_85){return [1,B(_7Q(_82,function(_86){return E(new T(function(){return B(A(_85,[_83]));}));}))];},_87=new T(function(){return B(unCStr("SO"));}),_88=[0,14],_89=function(_8a){return [1,B(_7Q(_87,function(_8b){return E(new T(function(){return B(A(_8a,[_88]));}));}))];},_8c=function(_8d){return [1,B(_4P(_84,_89,_8d))];},_8e=new T(function(){return B(unCStr("NUL"));}),_8f=[0,0],_8g=function(_8h){return [1,B(_7Q(_8e,function(_8i){return E(new T(function(){return B(A(_8h,[_8f]));}));}))];},_8j=new T(function(){return B(unCStr("STX"));}),_8k=[0,2],_8l=function(_8m){return [1,B(_7Q(_8j,function(_8n){return E(new T(function(){return B(A(_8m,[_8k]));}));}))];},_8o=new T(function(){return B(unCStr("ETX"));}),_8p=[0,3],_8q=function(_8r){return [1,B(_7Q(_8o,function(_8s){return E(new T(function(){return B(A(_8r,[_8p]));}));}))];},_8t=new T(function(){return B(unCStr("EOT"));}),_8u=[0,4],_8v=function(_8w){return [1,B(_7Q(_8t,function(_8x){return E(new T(function(){return B(A(_8w,[_8u]));}));}))];},_8y=new T(function(){return B(unCStr("ENQ"));}),_8z=[0,5],_8A=function(_8B){return [1,B(_7Q(_8y,function(_8C){return E(new T(function(){return B(A(_8B,[_8z]));}));}))];},_8D=new T(function(){return B(unCStr("ACK"));}),_8E=[0,6],_8F=function(_8G){return [1,B(_7Q(_8D,function(_8H){return E(new T(function(){return B(A(_8G,[_8E]));}));}))];},_8I=new T(function(){return B(unCStr("BEL"));}),_8J=[0,7],_8K=function(_8L){return [1,B(_7Q(_8I,function(_8M){return E(new T(function(){return B(A(_8L,[_8J]));}));}))];},_8N=new T(function(){return B(unCStr("BS"));}),_8O=[0,8],_8P=function(_8Q){return [1,B(_7Q(_8N,function(_8R){return E(new T(function(){return B(A(_8Q,[_8O]));}));}))];},_8S=new T(function(){return B(unCStr("HT"));}),_8T=[0,9],_8U=function(_8V){return [1,B(_7Q(_8S,function(_8W){return E(new T(function(){return B(A(_8V,[_8T]));}));}))];},_8X=new T(function(){return B(unCStr("LF"));}),_8Y=[0,10],_8Z=function(_90){return [1,B(_7Q(_8X,function(_91){return E(new T(function(){return B(A(_90,[_8Y]));}));}))];},_92=new T(function(){return B(unCStr("VT"));}),_93=[0,11],_94=function(_95){return [1,B(_7Q(_92,function(_96){return E(new T(function(){return B(A(_95,[_93]));}));}))];},_97=new T(function(){return B(unCStr("FF"));}),_98=[0,12],_99=function(_9a){return [1,B(_7Q(_97,function(_9b){return E(new T(function(){return B(A(_9a,[_98]));}));}))];},_9c=new T(function(){return B(unCStr("CR"));}),_9d=[0,13],_9e=function(_9f){return [1,B(_7Q(_9c,function(_9g){return E(new T(function(){return B(A(_9f,[_9d]));}));}))];},_9h=new T(function(){return B(unCStr("SI"));}),_9i=[0,15],_9j=function(_9k){return [1,B(_7Q(_9h,function(_9l){return E(new T(function(){return B(A(_9k,[_9i]));}));}))];},_9m=new T(function(){return B(unCStr("DLE"));}),_9n=[0,16],_9o=function(_9p){return [1,B(_7Q(_9m,function(_9q){return E(new T(function(){return B(A(_9p,[_9n]));}));}))];},_9r=new T(function(){return B(unCStr("DC1"));}),_9s=[0,17],_9t=function(_9u){return [1,B(_7Q(_9r,function(_9v){return E(new T(function(){return B(A(_9u,[_9s]));}));}))];},_9w=new T(function(){return B(unCStr("DC2"));}),_9x=[0,18],_9y=function(_9z){return [1,B(_7Q(_9w,function(_9A){return E(new T(function(){return B(A(_9z,[_9x]));}));}))];},_9B=new T(function(){return B(unCStr("DC3"));}),_9C=[0,19],_9D=function(_9E){return [1,B(_7Q(_9B,function(_9F){return E(new T(function(){return B(A(_9E,[_9C]));}));}))];},_9G=new T(function(){return B(unCStr("DC4"));}),_9H=[0,20],_9I=function(_9J){return [1,B(_7Q(_9G,function(_9K){return E(new T(function(){return B(A(_9J,[_9H]));}));}))];},_9L=new T(function(){return B(unCStr("NAK"));}),_9M=[0,21],_9N=function(_9O){return [1,B(_7Q(_9L,function(_9P){return E(new T(function(){return B(A(_9O,[_9M]));}));}))];},_9Q=new T(function(){return B(unCStr("SYN"));}),_9R=[0,22],_9S=function(_9T){return [1,B(_7Q(_9Q,function(_9U){return E(new T(function(){return B(A(_9T,[_9R]));}));}))];},_9V=new T(function(){return B(unCStr("ETB"));}),_9W=[0,23],_9X=function(_9Y){return [1,B(_7Q(_9V,function(_9Z){return E(new T(function(){return B(A(_9Y,[_9W]));}));}))];},_a0=new T(function(){return B(unCStr("CAN"));}),_a1=[0,24],_a2=function(_a3){return [1,B(_7Q(_a0,function(_a4){return E(new T(function(){return B(A(_a3,[_a1]));}));}))];},_a5=new T(function(){return B(unCStr("EM"));}),_a6=[0,25],_a7=function(_a8){return [1,B(_7Q(_a5,function(_a9){return E(new T(function(){return B(A(_a8,[_a6]));}));}))];},_aa=new T(function(){return B(unCStr("SUB"));}),_ab=[0,26],_ac=function(_ad){return [1,B(_7Q(_aa,function(_ae){return E(new T(function(){return B(A(_ad,[_ab]));}));}))];},_af=new T(function(){return B(unCStr("ESC"));}),_ag=[0,27],_ah=function(_ai){return [1,B(_7Q(_af,function(_aj){return E(new T(function(){return B(A(_ai,[_ag]));}));}))];},_ak=new T(function(){return B(unCStr("FS"));}),_al=[0,28],_am=function(_an){return [1,B(_7Q(_ak,function(_ao){return E(new T(function(){return B(A(_an,[_al]));}));}))];},_ap=new T(function(){return B(unCStr("GS"));}),_aq=[0,29],_ar=function(_as){return [1,B(_7Q(_ap,function(_at){return E(new T(function(){return B(A(_as,[_aq]));}));}))];},_au=new T(function(){return B(unCStr("RS"));}),_av=[0,30],_aw=function(_ax){return [1,B(_7Q(_au,function(_ay){return E(new T(function(){return B(A(_ax,[_av]));}));}))];},_az=new T(function(){return B(unCStr("US"));}),_aA=[0,31],_aB=function(_aC){return [1,B(_7Q(_az,function(_aD){return E(new T(function(){return B(A(_aC,[_aA]));}));}))];},_aE=new T(function(){return B(unCStr("SP"));}),_aF=[0,32],_aG=function(_aH){return [1,B(_7Q(_aE,function(_aI){return E(new T(function(){return B(A(_aH,[_aF]));}));}))];},_aJ=new T(function(){return B(unCStr("DEL"));}),_aK=[0,127],_aL=function(_aM){return [1,B(_7Q(_aJ,function(_aN){return E(new T(function(){return B(A(_aM,[_aK]));}));}))];},_aO=[1,_aL,_9],_aP=[1,_aG,_aO],_aQ=[1,_aB,_aP],_aR=[1,_aw,_aQ],_aS=[1,_ar,_aR],_aT=[1,_am,_aS],_aU=[1,_ah,_aT],_aV=[1,_ac,_aU],_aW=[1,_a7,_aV],_aX=[1,_a2,_aW],_aY=[1,_9X,_aX],_aZ=[1,_9S,_aY],_b0=[1,_9N,_aZ],_b1=[1,_9I,_b0],_b2=[1,_9D,_b1],_b3=[1,_9y,_b2],_b4=[1,_9t,_b3],_b5=[1,_9o,_b4],_b6=[1,_9j,_b5],_b7=[1,_9e,_b6],_b8=[1,_99,_b7],_b9=[1,_94,_b8],_ba=[1,_8Z,_b9],_bb=[1,_8U,_ba],_bc=[1,_8P,_bb],_bd=[1,_8K,_bc],_be=[1,_8F,_bd],_bf=[1,_8A,_be],_bg=[1,_8v,_bf],_bh=[1,_8q,_bg],_bi=[1,_8l,_bh],_bj=[1,_8g,_bi],_bk=[1,_8c,_bj],_bl=new T(function(){return B(_7I(_bk));}),_bm=[0,1114111],_bn=[0,34],_bo=[0,39],_bp=function(_bq){var _br=new T(function(){return B(A(_bq,[_8J]));}),_bs=new T(function(){return B(A(_bq,[_8O]));}),_bt=new T(function(){return B(A(_bq,[_8T]));}),_bu=new T(function(){return B(A(_bq,[_8Y]));}),_bv=new T(function(){return B(A(_bq,[_93]));}),_bw=new T(function(){return B(A(_bq,[_98]));}),_bx=new T(function(){return B(A(_bq,[_9d]));});return new F(function(){return _3E([0,function(_by){switch(E(E(_by)[1])){case 34:return E(new T(function(){return B(A(_bq,[_bn]));}));case 39:return E(new T(function(){return B(A(_bq,[_bo]));}));case 92:return E(new T(function(){return B(A(_bq,[_7q]));}));case 97:return E(_br);case 98:return E(_bs);case 102:return E(_bw);case 110:return E(_bu);case 114:return E(_bx);case 116:return E(_bt);case 118:return E(_bv);default:return [2];}}],new T(function(){return B(_3E([1,B(_4P(_7o,_7r,function(_bz){return [1,B(_5r(_bz,function(_bA){var _bB=B(_6n(new T(function(){return B(_6d(E(_bz)[1]));}),_6c,_bA));return !B(_7y(_bB,_bm))?[2]:B(A(_bq,[new T(function(){var _bC=B(_7v(_bB));if(_bC>>>0>1114111){var _bD=B(_7t(_bC));}else{var _bD=[0,_bC];}var _bE=_bD,_bF=_bE,_bG=_bF;return _bG;})]));}))];}))],new T(function(){return B(_3E([0,function(_bH){return E(E(_bH)[1])==94?E([0,function(_bI){switch(E(E(_bI)[1])){case 64:return E(new T(function(){return B(A(_bq,[_8f]));}));case 65:return E(new T(function(){return B(A(_bq,[_83]));}));case 66:return E(new T(function(){return B(A(_bq,[_8k]));}));case 67:return E(new T(function(){return B(A(_bq,[_8p]));}));case 68:return E(new T(function(){return B(A(_bq,[_8u]));}));case 69:return E(new T(function(){return B(A(_bq,[_8z]));}));case 70:return E(new T(function(){return B(A(_bq,[_8E]));}));case 71:return E(_br);case 72:return E(_bs);case 73:return E(_bt);case 74:return E(_bu);case 75:return E(_bv);case 76:return E(_bw);case 77:return E(_bx);case 78:return E(new T(function(){return B(A(_bq,[_88]));}));case 79:return E(new T(function(){return B(A(_bq,[_9i]));}));case 80:return E(new T(function(){return B(A(_bq,[_9n]));}));case 81:return E(new T(function(){return B(A(_bq,[_9s]));}));case 82:return E(new T(function(){return B(A(_bq,[_9x]));}));case 83:return E(new T(function(){return B(A(_bq,[_9C]));}));case 84:return E(new T(function(){return B(A(_bq,[_9H]));}));case 85:return E(new T(function(){return B(A(_bq,[_9M]));}));case 86:return E(new T(function(){return B(A(_bq,[_9R]));}));case 87:return E(new T(function(){return B(A(_bq,[_9W]));}));case 88:return E(new T(function(){return B(A(_bq,[_a1]));}));case 89:return E(new T(function(){return B(A(_bq,[_a6]));}));case 90:return E(new T(function(){return B(A(_bq,[_ab]));}));case 91:return E(new T(function(){return B(A(_bq,[_ag]));}));case 92:return E(new T(function(){return B(A(_bq,[_al]));}));case 93:return E(new T(function(){return B(A(_bq,[_aq]));}));case 94:return E(new T(function(){return B(A(_bq,[_av]));}));case 95:return E(new T(function(){return B(A(_bq,[_aA]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_bl,[_bq]));})));})));}));});},_bJ=function(_bK){return new F(function(){return A(_bK,[_1x]);});},_bL=function(_bM){var _bN=E(_bM);if(!_bN[0]){return E(_bJ);}else{var _bO=_bN[2],_bP=E(E(_bN[1])[1]);switch(_bP){case 9:return function(_bQ){return [0,function(_bR){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_bQ]));}));}];};case 10:return function(_bS){return [0,function(_bT){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_bS]));}));}];};case 11:return function(_bU){return [0,function(_bV){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_bU]));}));}];};case 12:return function(_bW){return [0,function(_bX){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_bW]));}));}];};case 13:return function(_bY){return [0,function(_bZ){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_bY]));}));}];};case 32:return function(_c0){return [0,function(_c1){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_c0]));}));}];};case 160:return function(_c2){return [0,function(_c3){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_c2]));}));}];};default:var _c4=u_iswspace(_bP),_c5=_c4;return E(_c5)==0?E(_bJ):function(_c6){return [0,function(_c7){return E(new T(function(){return B(A(new T(function(){return B(_bL(_bO));}),[_c6]));}));}];};}}},_c8=function(_c9){var _ca=new T(function(){return B(_c8(_c9));}),_cb=[1,function(_cc){return new F(function(){return A(_bL,[_cc,function(_cd){return E([0,function(_ce){return E(E(_ce)[1])==92?E(_ca):[2];}]);}]);});}];return new F(function(){return _3E([0,function(_cf){return E(E(_cf)[1])==92?E([0,function(_cg){var _ch=E(E(_cg)[1]);switch(_ch){case 9:return E(_cb);case 10:return E(_cb);case 11:return E(_cb);case 12:return E(_cb);case 13:return E(_cb);case 32:return E(_cb);case 38:return E(_ca);case 160:return E(_cb);default:var _ci=u_iswspace(_ch),_cj=_ci;return E(_cj)==0?[2]:E(_cb);}}]):[2];}],[0,function(_ck){var _cl=E(_ck);return E(_cl[1])==92?E(new T(function(){return B(_bp(function(_cm){return new F(function(){return A(_c9,[[0,_cm,_7i]]);});}));})):B(A(_c9,[[0,_cl,_7h]]));}]);});},_cn=function(_co,_cp){return new F(function(){return _c8(function(_cq){var _cr=E(_cq),_cs=E(_cr[1]);if(E(_cs[1])==34){if(!E(_cr[2])){return E(new T(function(){return B(A(_cp,[[1,new T(function(){return B(A(_co,[_9]));})]]));}));}else{return new F(function(){return _cn(function(_ct){return new F(function(){return A(_co,[[1,_cs,_ct]]);});},_cp);});}}else{return new F(function(){return _cn(function(_cu){return new F(function(){return A(_co,[[1,_cs,_cu]]);});},_cp);});}});});},_cv=new T(function(){return B(unCStr("_\'"));}),_cw=function(_cx){var _cy=u_iswalnum(_cx),_cz=_cy;return E(_cz)==0?B(_6X(_4m,[0,_cx],_cv)):true;},_cA=function(_cB){return new F(function(){return _cw(E(_cB)[1]);});},_cC=new T(function(){return B(unCStr(",;()[]{}`"));}),_cD=new T(function(){return B(unCStr(".."));}),_cE=new T(function(){return B(unCStr("::"));}),_cF=new T(function(){return B(unCStr("->"));}),_cG=[0,64],_cH=[1,_cG,_9],_cI=[0,126],_cJ=[1,_cI,_9],_cK=new T(function(){return B(unCStr("=>"));}),_cL=[1,_cK,_9],_cM=[1,_cJ,_cL],_cN=[1,_cH,_cM],_cO=[1,_cF,_cN],_cP=new T(function(){return B(unCStr("<-"));}),_cQ=[1,_cP,_cO],_cR=[0,124],_cS=[1,_cR,_9],_cT=[1,_cS,_cQ],_cU=[1,_7q,_9],_cV=[1,_cU,_cT],_cW=[0,61],_cX=[1,_cW,_9],_cY=[1,_cX,_cV],_cZ=[1,_cE,_cY],_d0=[1,_cD,_cZ],_d1=function(_d2){return new F(function(){return _3E([1,function(_d3){return E(_d3)[0]==0?E(new T(function(){return B(A(_d2,[_5m]));})):[2];}],new T(function(){return B(_3E([0,function(_d4){return E(E(_d4)[1])==39?E([0,function(_d5){var _d6=E(_d5);switch(E(_d6[1])){case 39:return [2];case 92:return E(new T(function(){return B(_bp(function(_d7){return [0,function(_d8){return E(E(_d8)[1])==39?E(new T(function(){return B(A(_d2,[[0,_d7]]));})):[2];}];}));}));default:return [0,function(_d9){return E(E(_d9)[1])==39?E(new T(function(){return B(A(_d2,[[0,_d6]]));})):[2];}];}}]):[2];}],new T(function(){return B(_3E([0,function(_da){return E(E(_da)[1])==34?E(new T(function(){return B(_cn(_5n,_d2));})):[2];}],new T(function(){return B(_3E([0,function(_db){return !B(_6X(_4m,_db,_cC))?[2]:B(A(_d2,[[2,[1,_db,_9]]]));}],new T(function(){return B(_3E([0,function(_dc){return !B(_6X(_4m,_dc,_72))?[2]:[1,B(_5b(_73,function(_dd){var _de=[1,_dc,_dd];return !B(_6X(_4v,_de,_d0))?B(A(_d2,[[4,_de]])):B(A(_d2,[[2,_de]]));}))];}],new T(function(){return B(_3E([0,function(_df){var _dg=E(_df),_dh=_dg[1],_di=u_iswalpha(_dh),_dj=_di;return E(_dj)==0?E(_dh)==95?[1,B(_5b(_cA,function(_dk){return new F(function(){return A(_d2,[[3,[1,_dg,_dk]]]);});}))]:[2]:[1,B(_5b(_cA,function(_dl){return new F(function(){return A(_d2,[[3,[1,_dg,_dl]]]);});}))];}],new T(function(){return [1,B(_4P(_7f,_6T,_d2))];})));})));})));})));})));}));});},_dm=[0,0],_dn=function(_do,_dp){return function(_dq){return new F(function(){return A(_bL,[_dq,function(_dr){return E(new T(function(){return B(_d1(function(_ds){var _dt=E(_ds);return _dt[0]==2?!B(_4b(_dt[1],_4a))?[2]:E(new T(function(){return B(A(_do,[_dm,function(_du){return [1,function(_dv){return new F(function(){return A(_bL,[_dv,function(_dw){return E(new T(function(){return B(_d1(function(_dx){var _dy=E(_dx);return _dy[0]==2?!B(_4b(_dy[1],_48))?[2]:E(new T(function(){return B(A(_dp,[_du]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_dz=function(_dA,_dB,_dC){var _dD=function(_dE,_dF){return new F(function(){return _3E([1,function(_dG){return new F(function(){return A(_bL,[_dG,function(_dH){return E(new T(function(){return B(_d1(function(_dI){var _dJ=E(_dI);if(_dJ[0]==4){var _dK=E(_dJ[1]);if(!_dK[0]){return new F(function(){return A(_dA,[_dJ,_dE,_dF]);});}else{return E(E(_dK[1])[1])==45?E(_dK[2])[0]==0?E([1,function(_dL){return new F(function(){return A(_bL,[_dL,function(_dM){return E(new T(function(){return B(_d1(function(_dN){return new F(function(){return A(_dA,[_dN,_dE,function(_dO){return new F(function(){return A(_dF,[new T(function(){return [0, -E(_dO)[1]];})]);});}]);});}));}));}]);});}]):B(A(_dA,[_dJ,_dE,_dF])):B(A(_dA,[_dJ,_dE,_dF]));}}else{return new F(function(){return A(_dA,[_dJ,_dE,_dF]);});}}));}));}]);});}],new T(function(){return [1,B(_dn(_dD,_dF))];}));});};return new F(function(){return _dD(_dB,_dC);});},_dP=function(_dQ,_dR){return [2];},_dS=function(_dT){var _dU=E(_dT);return _dU[0]==0?[1,new T(function(){return B(_6n(new T(function(){return B(_6d(E(_dU[1])[1]));}),_6c,_dU[2]));})]:E(_dU[2])[0]==0?E(_dU[3])[0]==0?[1,new T(function(){return B(_6n(_6b,_6c,_dU[1]));})]:[0]:[0];},_dV=function(_dW){var _dX=E(_dW);if(_dX[0]==5){var _dY=B(_dS(_dX[1]));return _dY[0]==0?E(_dP):function(_dZ,_e0){return new F(function(){return A(_e0,[new T(function(){return [0,B(_7v(_dY[1]))];})]);});};}else{return E(_dP);}},_e1=function(_e2){return [1,function(_e3){return new F(function(){return A(_bL,[_e3,function(_e4){return E([3,_e2,_4H]);}]);});}];},_e5=new T(function(){return B(_dz(_dV,_dm,_e1));}),_e6=new T(function(){return B(unCStr("clientHeight"));}),_e7=new T(function(){return B(unCStr("scrollHeight"));}),_e8=new T(function(){return B(unCStr("scrollTop"));}),_e9=function(_ea){while(1){var _eb=(function(_ec){var _ed=E(_ec);if(!_ed[0]){return [0];}else{var _ee=_ed[2],_ef=E(_ed[1]);if(!E(_ef[2])[0]){return [1,_ef[1],new T(function(){return B(_e9(_ee));})];}else{_ea=_ee;return null;}}})(_ea);if(_eb!=null){return _eb;}}},_eg=function(_eh,_ei,_ej,_){var _ek=B(_1j(_ej,_e8,_)),_el=_ek,_em=B(_1j(_ej,_e7,_)),_en=_em,_eo=B(_1j(_ej,_e6,_)),_ep=_eo,_eq=B(_e9(B(_3u(_e5,_en))));if(!_eq[0]){return E(_2b);}else{if(!E(_eq[2])[0]){var _er=B(_e9(B(_3u(_e5,_el))));if(!_er[0]){return E(_2b);}else{if(!E(_er[2])[0]){var _es=E(_er[1])[1],_et=B(_e9(B(_3u(_e5,_ep))));if(!_et[0]){return E(_2b);}else{if(!E(_et[2])[0]){if((E(_eq[1])[1]-_es|0)!=E(_et[1])[1]){if(!E(_es)){return new F(function(){return _1O(E(_eh)[1],_ei,[0,_ej],_);});}else{return _1x;}}else{return new F(function(){return _1y(E(_eh)[1],_ei,[0,_ej],_);});}}else{return E(_29);}}}else{return E(_29);}}}else{return E(_29);}}},_eu=[3,_],_ev=[13,_],_ew=new T(function(){return B(unCStr(" . "));}),_ex=function(_ey){var _ez=E(_ey);switch(_ez[0]){case 0:return E(_ez[3]);case 1:return E(_ez[3]);case 2:return E(_ez[3]);case 3:return E(_ez[3]);case 4:return E(_ez[3]);case 5:return E(_ez[3]);case 6:return E(_ez[3]);case 7:return E(_ez[3]);case 8:return E(_ez[3]);default:return E(_ez[3]);}},_eA=[0,41],_eB=[1,_eA,_9],_eC=new T(function(){return B(_3r("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_eD=[0,44],_eE=[0,40],_eF=function(_eG,_eH,_eI){var _eJ=E(_eI);switch(_eJ[0]){case 0:return E(_eC);case 1:return new F(function(){return A(_eG,[_eJ[2],_9]);});break;case 2:return new F(function(){return _ex(_eJ[2]);});break;case 3:return new F(function(){return A(_eH,[_eJ[2],[1,new T(function(){return B(_eF(_eG,_eH,_eJ[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_ex(_eJ[2])),[1,_eE,new T(function(){return B(_e(B(_eF(_eG,_eH,_eJ[3])),_eB));})]);});break;case 5:return new F(function(){return A(_eH,[_eJ[2],[1,new T(function(){return B(_eF(_eG,_eH,_eJ[3]));}),[1,new T(function(){return B(_eF(_eG,_eH,_eJ[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_ex(_eJ[2])),[1,_eE,new T(function(){return B(_e(B(_eF(_eG,_eH,_eJ[3])),[1,_eD,new T(function(){return B(_e(B(_eF(_eG,_eH,_eJ[4])),_eB));})]));})]);});}},_eK=[0],_eL=function(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eT){var _eU=E(_eT);switch(_eU[0]){case 0:return [0];case 1:return new F(function(){return A(_eP,[_eU[2],_9]);});break;case 2:return new F(function(){return _ex(_eU[2]);});break;case 3:return new F(function(){return A(_eM,[_eU[2],[1,new T(function(){return B(_eF(_eP,_eQ,_eU[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_ex(_eU[2])),[1,_eE,new T(function(){return B(_e(B(_eF(_eP,_eQ,_eU[3])),_eB));})]);});break;case 5:return new F(function(){return A(_eM,[_eU[2],[1,new T(function(){return B(_eF(_eP,_eQ,_eU[3]));}),[1,new T(function(){return B(_eF(_eP,_eQ,_eU[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_ex(_eU[2])),[1,_eE,new T(function(){return B(_e(B(_eF(_eP,_eQ,_eU[3])),[1,_eD,new T(function(){return B(_e(B(_eF(_eP,_eQ,_eU[4])),_eB));})]));})]);});break;case 7:return new F(function(){return A(_eN,[_eU[2],[1,new T(function(){return B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eU[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_ex(_eU[2])),new T(function(){return B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eU[3]));},1));});break;case 9:return new F(function(){return A(_eN,[_eU[2],[1,new T(function(){return B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eU[3]));}),[1,new T(function(){return B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eU[4]));}),_9]]]);});break;case 10:return [1,_eE,new T(function(){return B(_e(B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eU[3])),new T(function(){return B(_e(B(_ex(_eU[2])),new T(function(){return B(_e(B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,_eU[4])),_eB));},1)));},1)));})];case 11:var _eV=_eU[2],_eW=_eU[3];return new F(function(){return A(_eO,[_eV,[1,new T(function(){return B(A(_eR,[new T(function(){return B(A(_eW,[_eK]));}),_eV]));}),[1,new T(function(){return B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,B(A(_eW,[_eK]))));}),_9]]]);});break;default:var _eX=_eU[2],_eY=_eU[3];return new F(function(){return _e(B(_ex(_eX)),new T(function(){return B(_e(B(A(_eS,[new T(function(){return B(A(_eY,[_eK]));}),_eX])),[1,_eE,new T(function(){return B(_e(B(_eL(_eM,_eN,_eO,_eP,_eQ,_eR,_eS,B(A(_eY,[_eK])))),_eB));})]));},1));});}},_eZ=function(_f0){var _f1=E(_f0);if(!_f1[0]){return [0];}else{return new F(function(){return _e(_f1[1],new T(function(){return B(_eZ(_f1[2]));},1));});}},_f2=function(_f3,_f4){var _f5=E(_f4);return _f5[0]==0?[0]:[1,new T(function(){return B(A(_f3,[_f5[1]]));}),new T(function(){return B(_f2(_f3,_f5[2]));})];},_f6=function(_f7,_f8){var _f9=E(_f8);return _f9[0]==0?[0]:[1,_f7,[1,_f9[1],new T(function(){return B(_f6(_f7,_f9[2]));})]];},_fa=function(_fb,_fc,_fd,_fe,_ff,_fg,_fh,_fi){var _fj=E(_fi);if(!_fj[0]){return new F(function(){return _ex(_fj[1]);});}else{var _fk=B(_f2(function(_fl){return new F(function(){return _eL(_fb,_fc,_fd,_ff,_fe,_fg,_fh,_fl);});},_fj[1]));return _fk[0]==0?[0]:B(_eZ([1,_fk[1],new T(function(){return B(_f6(_ew,_fk[2]));})]));}},_fm=function(_fn,_fo,_fp,_fq,_fr,_fs,_ft,_fu,_fv){return new F(function(){return _4b(B(_fa(_fn,_fo,_fp,_fq,_fr,_fs,_ft,_fu)),B(_fa(_fn,_fo,_fp,_fq,_fr,_fs,_ft,_fv)));});},_fw=function(_fx,_fy,_fz,_fA,_fB,_fC,_fD,_fE,_fF){return !B(_fm(_fx,_fy,_fz,_fA,_fB,_fC,_fD,_fE,_fF))?true:false;},_fG=function(_fH,_fI,_fJ,_fK,_fL,_fM,_fN){return [0,function(_fO,_fP){return new F(function(){return _fm(_fH,_fI,_fJ,_fK,_fL,_fM,_fN,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _fw(_fH,_fI,_fJ,_fK,_fL,_fM,_fN,_fO,_fP);});}];},_fQ=new T(function(){return B(unCStr("wheel"));}),_fR=new T(function(){return B(unCStr("mouseout"));}),_fS=new T(function(){return B(unCStr("mouseover"));}),_fT=new T(function(){return B(unCStr("mousemove"));}),_fU=new T(function(){return B(unCStr("blur"));}),_fV=new T(function(){return B(unCStr("focus"));}),_fW=new T(function(){return B(unCStr("change"));}),_fX=new T(function(){return B(unCStr("unload"));}),_fY=new T(function(){return B(unCStr("load"));}),_fZ=new T(function(){return B(unCStr("submit"));}),_g0=new T(function(){return B(unCStr("keydown"));}),_g1=new T(function(){return B(unCStr("keyup"));}),_g2=new T(function(){return B(unCStr("keypress"));}),_g3=new T(function(){return B(unCStr("mouseup"));}),_g4=new T(function(){return B(unCStr("mousedown"));}),_g5=new T(function(){return B(unCStr("dblclick"));}),_g6=new T(function(){return B(unCStr("click"));}),_g7=function(_g8){switch(E(_g8)[0]){case 0:return E(_fY);case 1:return E(_fX);case 2:return E(_fW);case 3:return E(_fV);case 4:return E(_fU);case 5:return E(_fT);case 6:return E(_fS);case 7:return E(_fR);case 8:return E(_g6);case 9:return E(_g5);case 10:return E(_g4);case 11:return E(_g3);case 12:return E(_g2);case 13:return E(_g1);case 14:return E(_g0);case 15:return E(_fZ);default:return E(_fQ);}},_g9=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_ga=new T(function(){return B(unCStr("main"));}),_gb=new T(function(){return B(unCStr("EventData"));}),_gc=new T(function(){var _gd=hs_wordToWord64(3703396926),_ge=_gd,_gf=hs_wordToWord64(1660403598),_gg=_gf;return [0,_ge,_gg,[0,_ge,_gg,_ga,_g9,_gb],_9];}),_gh=[0,0],_gi=2,_gj=[1],_gk=new T(function(){return B(unCStr("Dynamic"));}),_gl=new T(function(){return B(unCStr("Data.Dynamic"));}),_gm=new T(function(){return B(unCStr("base"));}),_gn=new T(function(){var _go=hs_wordToWord64(628307645),_gp=_go,_gq=hs_wordToWord64(949574464),_gr=_gq;return [0,_gp,_gr,[0,_gp,_gr,_gm,_gl,_gk],_9];}),_gs=[0],_gt=new T(function(){return B(unCStr("OnLoad"));}),_gu=[0,_gt,_gs],_gv=[0,_gc,_gu],_gw=[0,_gn,_gv],_gx=function(_){return _6D;},_gy=function(_gz,_){return _6D;},_gA=[0,_gx,_gy],_gB=[0,_9,_gh,_gi,_gA,_7h,_gw,_gj],_gC=function(_){var _=0,_gD=newMVar(),_gE=_gD,_=putMVar(_gE,_gB);return [0,_gE];},_gF=function(_gG){var _gH=B(A(_gG,[_])),_gI=_gH;return E(_gI);},_gJ=new T(function(){return B(_gF(_gC));}),_gK=new T(function(){return B(_3r("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_gL=[0,_fY,_gs],_gM=[0,_gc,_gL],_gN=[0,_fX,_gs],_gO=[0,_gc,_gN],_gP=[0,_fW,_gs],_gQ=[0,_gc,_gP],_gR=[0,_fV,_gs],_gS=[0,_gc,_gR],_gT=[0,_fU,_gs],_gU=[0,_gc,_gT],_gV=[3],_gW=[0,_fR,_gV],_gX=[0,_gc,_gW],_gY=function(_gZ,_h0){switch(E(_gZ)[0]){case 0:return function(_){var _h1=E(_gJ)[1],_h2=takeMVar(_h1),_h3=_h2,_=putMVar(_h1,new T(function(){var _h4=E(_h3);return [0,_h4[1],_h4[2],_h4[3],_h4[4],_h4[5],_gM,_h4[7]];}));return new F(function(){return A(_h0,[_]);});};case 1:return function(_){var _h5=E(_gJ)[1],_h6=takeMVar(_h5),_h7=_h6,_=putMVar(_h5,new T(function(){var _h8=E(_h7);return [0,_h8[1],_h8[2],_h8[3],_h8[4],_h8[5],_gO,_h8[7]];}));return new F(function(){return A(_h0,[_]);});};case 2:return function(_){var _h9=E(_gJ)[1],_ha=takeMVar(_h9),_hb=_ha,_=putMVar(_h9,new T(function(){var _hc=E(_hb);return [0,_hc[1],_hc[2],_hc[3],_hc[4],_hc[5],_gQ,_hc[7]];}));return new F(function(){return A(_h0,[_]);});};case 3:return function(_){var _hd=E(_gJ)[1],_he=takeMVar(_hd),_hf=_he,_=putMVar(_hd,new T(function(){var _hg=E(_hf);return [0,_hg[1],_hg[2],_hg[3],_hg[4],_hg[5],_gS,_hg[7]];}));return new F(function(){return A(_h0,[_]);});};case 4:return function(_){var _hh=E(_gJ)[1],_hi=takeMVar(_hh),_hj=_hi,_=putMVar(_hh,new T(function(){var _hk=E(_hj);return [0,_hk[1],_hk[2],_hk[3],_hk[4],_hk[5],_gU,_hk[7]];}));return new F(function(){return A(_h0,[_]);});};case 5:return function(_hl){return function(_){var _hm=E(_gJ)[1],_hn=takeMVar(_hm),_ho=_hn,_=putMVar(_hm,new T(function(){var _hp=E(_ho);return [0,_hp[1],_hp[2],_hp[3],_hp[4],_hp[5],[0,_gc,[0,_fT,[2,E(_hl)]]],_hp[7]];}));return new F(function(){return A(_h0,[_]);});};};case 6:return function(_hq){return function(_){var _hr=E(_gJ)[1],_hs=takeMVar(_hr),_ht=_hs,_=putMVar(_hr,new T(function(){var _hu=E(_ht);return [0,_hu[1],_hu[2],_hu[3],_hu[4],_hu[5],[0,_gc,[0,_fS,[2,E(_hq)]]],_hu[7]];}));return new F(function(){return A(_h0,[_]);});};};case 7:return function(_){var _hv=E(_gJ)[1],_hw=takeMVar(_hv),_hx=_hw,_=putMVar(_hv,new T(function(){var _hy=E(_hx);return [0,_hy[1],_hy[2],_hy[3],_hy[4],_hy[5],_gX,_hy[7]];}));return new F(function(){return A(_h0,[_]);});};case 8:return function(_hz,_hA){return function(_){var _hB=E(_gJ)[1],_hC=takeMVar(_hB),_hD=_hC,_=putMVar(_hB,new T(function(){var _hE=E(_hD);return [0,_hE[1],_hE[2],_hE[3],_hE[4],_hE[5],[0,_gc,[0,_g6,[1,_hz,E(_hA)]]],_hE[7]];}));return new F(function(){return A(_h0,[_]);});};};case 9:return function(_hF,_hG){return function(_){var _hH=E(_gJ)[1],_hI=takeMVar(_hH),_hJ=_hI,_=putMVar(_hH,new T(function(){var _hK=E(_hJ);return [0,_hK[1],_hK[2],_hK[3],_hK[4],_hK[5],[0,_gc,[0,_g5,[1,_hF,E(_hG)]]],_hK[7]];}));return new F(function(){return A(_h0,[_]);});};};case 10:return function(_hL,_hM){return function(_){var _hN=E(_gJ)[1],_hO=takeMVar(_hN),_hP=_hO,_=putMVar(_hN,new T(function(){var _hQ=E(_hP);return [0,_hQ[1],_hQ[2],_hQ[3],_hQ[4],_hQ[5],[0,_gc,[0,_g4,[1,_hL,E(_hM)]]],_hQ[7]];}));return new F(function(){return A(_h0,[_]);});};};case 11:return function(_hR,_hS){return function(_){var _hT=E(_gJ)[1],_hU=takeMVar(_hT),_hV=_hU,_=putMVar(_hT,new T(function(){var _hW=E(_hV);return [0,_hW[1],_hW[2],_hW[3],_hW[4],_hW[5],[0,_gc,[0,_g3,[1,_hR,E(_hS)]]],_hW[7]];}));return new F(function(){return A(_h0,[_]);});};};case 12:return function(_hX,_){var _hY=E(_gJ)[1],_hZ=takeMVar(_hY),_i0=_hZ,_=putMVar(_hY,new T(function(){var _i1=E(_i0);return [0,_i1[1],_i1[2],_i1[3],_i1[4],_i1[5],[0,_gc,[0,_g2,[4,_hX]]],_i1[7]];}));return new F(function(){return A(_h0,[_]);});};case 13:return function(_i2,_){var _i3=E(_gJ)[1],_i4=takeMVar(_i3),_i5=_i4,_=putMVar(_i3,new T(function(){var _i6=E(_i5);return [0,_i6[1],_i6[2],_i6[3],_i6[4],_i6[5],[0,_gc,[0,_g1,[4,_i2]]],_i6[7]];}));return new F(function(){return A(_h0,[_]);});};case 14:return function(_i7,_){var _i8=E(_gJ)[1],_i9=takeMVar(_i8),_ia=_i9,_=putMVar(_i8,new T(function(){var _ib=E(_ia);return [0,_ib[1],_ib[2],_ib[3],_ib[4],_ib[5],[0,_gc,[0,_g0,[4,_i7]]],_ib[7]];}));return new F(function(){return A(_h0,[_]);});};default:return E(_gK);}},_ic=[0,_g7,_gY],_id=function(_ie,_if,_){var _ig=jsCreateTextNode(toJSStr(E(_ie))),_ih=_ig,_ii=jsAppendChild(_ih,E(_if)[1]);return [0,_ih];},_ij=function(_ik,_il,_im,_in){return new F(function(){return A(_ik,[function(_){var _io=jsSetAttr(E(_il)[1],toJSStr(E(_im)),toJSStr(E(_in)));return _1x;}]);});},_ip=[0,112],_iq=function(_ir){var _is=new T(function(){return E(E(_ir)[2]);});return function(_it,_){return [0,[1,_ip,new T(function(){return B(_e(B(_F(0,E(_is)[1],_9)),new T(function(){return E(E(_ir)[1]);},1)));})],new T(function(){var _iu=E(_ir);return [0,_iu[1],new T(function(){return [0,E(_is)[1]+1|0];}),_iu[3],_iu[4],_iu[5],_iu[6],_iu[7]];})];};},_iv=new T(function(){return B(unCStr("id"));}),_iw=new T(function(){return B(unCStr("noid"));}),_ix=function(_iy,_){return _iy;},_iz=function(_iA,_iB,_){var _iC=jsFind(toJSStr(E(_iB))),_iD=_iC,_iE=E(_iD);if(!_iE[0]){var _iF=E(_gJ)[1],_iG=takeMVar(_iF),_iH=_iG,_iI=B(A(_iA,[_iH,_])),_iJ=_iI,_iK=E(_iJ),_=putMVar(_iF,_iK[2]);return E(_iK[1])[2];}else{var _iL=E(_iE[1]),_iM=jsClearChildren(_iL[1]),_iN=E(_gJ)[1],_iO=takeMVar(_iN),_iP=_iO,_iQ=B(A(_iA,[_iP,_])),_iR=_iQ,_iS=E(_iR),_iT=E(_iS[1]),_=putMVar(_iN,_iS[2]),_iU=B(A(_iT[1],[_iL,_])),_iV=_iU;return _iT[2];}},_iW=new T(function(){return B(unCStr("span"));}),_iX=function(_iY,_iZ,_j0,_){var _j1=jsCreateElem(toJSStr(E(_iW))),_j2=_j1,_j3=jsAppendChild(_j2,E(_j0)[1]),_j4=[0,_j2],_j5=B(A(_iY,[_iZ,_j4,_])),_j6=_j5;return _j4;},_j7=function(_j8){return E(_j8);},_j9=function(_ja,_jb,_jc,_){var _jd=B(A(_iq,[_jc,_jc,_])),_je=_jd,_jf=E(_je),_jg=_jf[1],_jh=E(_jf[2]),_ji=_jh[2],_jj=E(_jh[4]),_jk=B(A(_ja,[[0,_jh[1],_ji,_jh[3],[0,function(_){return new F(function(){return _iz(function(_jl,_){var _jm=B(A(_ja,[new T(function(){var _jn=E(_jl);return [0,_jn[1],_ji,_jn[3],_jn[4],_jn[5],_jn[6],_jn[7]];}),_])),_jo=_jm;return [0,[0,_ix,E(E(_jo)[1])[2]],_jl];},_iw,_);});},function(_jp,_){var _jq=B(_iz(new T(function(){return B(A(_jb,[_jp]));},1),_jg,_)),_jr=_jq,_js=E(_jr);return _js[0]==0?_6D:B(A(_jj[2],[_js[1],_]));}],_jh[5],_jh[6],_jh[7]],_])),_jt=_jk,_ju=E(_jt),_jv=_ju[2],_jw=E(_ju[1]),_jx=_jw[1],_jy=E(_jw[2]);if(!_jy[0]){return [0,[0,function(_jz,_){var _jA=B(A(_jx,[_jz,_])),_jB=_jA;if(!E(E(_jc)[5])){var _jC=B(_iX(_j7,_ix,_jz,_)),_jD=_jC,_jE=B(A(_ij,[_5n,_jD,_iv,_jg,_])),_jF=_jE;return _jz;}else{return _jz;}},_6D],new T(function(){var _jG=E(_jv);return [0,_jG[1],_jG[2],_jG[3],_jj,_jG[5],_jG[6],_jG[7]];})];}else{var _jH=B(A(_jb,[_jy[1],new T(function(){var _jI=E(_jv);return [0,_jI[1],_jI[2],_jI[3],_jj,_jI[5],_jI[6],_jI[7]];}),_])),_jJ=_jH,_jK=E(_jJ),_jL=E(_jK[1]),_jM=_jL[1];return [0,[0,function(_jN,_){var _jO=B(A(_jx,[_jN,_])),_jP=_jO;if(!E(E(_jc)[5])){var _jQ=B(_iX(_j7,_jM,_jN,_)),_jR=_jQ,_jS=B(A(_ij,[_5n,_jR,_iv,_jg,_])),_jT=_jS;return _jN;}else{var _jU=B(A(_jM,[_jN,_])),_jV=_jU;return _jN;}},_jL[2]],_jK[2]];}},_jW=function(_jX,_jY){switch(E(_jX)[0]){case 0:switch(E(_jY)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_jY)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_jY)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_jY)[0]==3?1:2;}},_jZ=new T(function(){return B(unCStr("end of input"));}),_k0=new T(function(){return B(unCStr("unexpected"));}),_k1=new T(function(){return B(unCStr("expecting"));}),_k2=new T(function(){return B(unCStr("unknown parse error"));}),_k3=new T(function(){return B(unCStr("or"));}),_k4=[0,58],_k5=[0,34],_k6=[0,41],_k7=[1,_k6,_9],_k8=function(_k9,_ka,_kb){var _kc=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_ka,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_kb,_9)),_k7));})));},1)));})));}),_kd=E(_k9);return _kd[0]==0?E(_kc):[1,_k5,new T(function(){return B(_e(_kd,new T(function(){return B(unAppCStr("\" ",_kc));},1)));})];},_ke=function(_kf,_kg,_kh){var _ki=E(_kh);if(!_ki[0]){return E(_kg);}else{return new F(function(){return _e(_kg,new T(function(){return B(_e(_kf,new T(function(){return B(_ke(_kf,_ki[1],_ki[2]));},1)));},1));});}},_kj=function(_kk){return E(_kk)[0]==0?false:true;},_kl=new T(function(){return B(unCStr(", "));}),_km=function(_kn){var _ko=E(_kn);if(!_ko[0]){return [0];}else{return new F(function(){return _e(_ko[1],new T(function(){return B(_km(_ko[2]));},1));});}},_kp=function(_kq,_kr){while(1){var _ks=(function(_kt,_ku){var _kv=E(_ku);if(!_kv[0]){return [0];}else{var _kw=_kv[1],_kx=_kv[2];if(!B(A(_kt,[_kw]))){var _ky=_kt;_kr=_kx;_kq=_ky;return null;}else{return [1,_kw,new T(function(){return B(_kp(_kt,_kx));})];}}})(_kq,_kr);if(_ks!=null){return _ks;}}},_kz=function(_kA,_kB){var _kC=E(_kB);return _kC[0]==0?[0]:[1,_kA,new T(function(){return B(_kz(_kC[1],_kC[2]));})];},_kD=function(_kE,_kF){while(1){var _kG=E(_kF);if(!_kG[0]){return E(_kE);}else{_kE=_kG[1];_kF=_kG[2];continue;}}},_kH=function(_kI){switch(E(_kI)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_kJ=function(_kK){return E(_kK)[0]==1?true:false;},_kL=function(_kM){return E(_kM)[0]==2?true:false;},_kN=[0,10],_kO=[1,_kN,_9],_kP=function(_kQ){return new F(function(){return _e(_kO,_kQ);});},_kR=[0,32],_kS=function(_kT){var _kU=E(_kT);switch(_kU[0]){case 0:return E(_kU[1]);case 1:return E(_kU[1]);case 2:return E(_kU[1]);default:return E(_kU[1]);}},_kV=function(_kW,_kX){var _kY=function(_kZ,_l0){while(1){var _l1=(function(_l2,_l3){var _l4=E(_l2);if(!_l4[0]){return [0];}else{var _l5=_l4[1],_l6=_l4[2];if(!B(_6X(_kW,_l5,_l3))){return [1,_l5,new T(function(){return B(_kY(_l6,[1,_l5,_l3]));})];}else{_kZ=_l6;var _l7=_l3;_l0=_l7;return null;}}})(_kZ,_l0);if(_l1!=null){return _l1;}}};return new F(function(){return _kY(_kX,_9);});},_l8=function(_l9,_la,_lb,_lc,_ld,_le){var _lf=E(_le);if(!_lf[0]){return E(_la);}else{var _lg=new T(function(){var _lh=B(_36(_kH,_lf));return [0,_lh[1],_lh[2]];}),_li=new T(function(){var _lj=B(_36(_kJ,E(_lg)[2]));return [0,_lj[1],_lj[2]];}),_lk=new T(function(){return E(E(_li)[1]);}),_ll=function(_lm,_ln){var _lo=E(_ln);if(!_lo[0]){return E(_lm);}else{var _lp=new T(function(){return B(_e(_l9,[1,_kR,new T(function(){return B(_kD(_lm,_lo));})]));}),_lq=B(_kV(_4v,B(_kp(_kj,B(_kz(_lm,_lo))))));if(!_lq[0]){return new F(function(){return _e(_9,[1,_kR,_lp]);});}else{var _lr=_lq[1],_ls=E(_lq[2]);if(!_ls[0]){return new F(function(){return _e(_lr,[1,_kR,_lp]);});}else{return new F(function(){return _e(B(_e(_lr,new T(function(){return B(_e(_kl,new T(function(){return B(_ke(_kl,_ls[1],_ls[2]));},1)));},1))),[1,_kR,_lp]);});}}}},_lt=function(_lu,_lv){var _lw=B(_kV(_4v,B(_kp(_kj,B(_f2(_kS,_lv))))));if(!_lw[0]){return [0];}else{var _lx=_lw[1],_ly=_lw[2],_lz=E(_lu);return _lz[0]==0?B(_ll(_lx,_ly)):B(_e(_lz,[1,_kR,new T(function(){return B(_ll(_lx,_ly));})]));}},_lA=new T(function(){var _lB=B(_36(_kL,E(_li)[2]));return [0,_lB[1],_lB[2]];});return new F(function(){return _km(B(_f2(_kP,B(_kV(_4v,B(_kp(_kj,[1,new T(function(){if(!E(_lk)[0]){var _lC=E(E(_lg)[1]);if(!_lC[0]){var _lD=[0];}else{var _lE=E(_lC[1]);switch(_lE[0]){case 0:var _lF=E(_lE[1]),_lG=_lF[0]==0?B(_e(_lc,[1,_kR,_ld])):B(_e(_lc,[1,_kR,_lF]));break;case 1:var _lH=E(_lE[1]),_lG=_lH[0]==0?B(_e(_lc,[1,_kR,_ld])):B(_e(_lc,[1,_kR,_lH]));break;case 2:var _lI=E(_lE[1]),_lG=_lI[0]==0?B(_e(_lc,[1,_kR,_ld])):B(_e(_lc,[1,_kR,_lI]));break;default:var _lJ=E(_lE[1]),_lG=_lJ[0]==0?B(_e(_lc,[1,_kR,_ld])):B(_e(_lc,[1,_kR,_lJ]));}var _lD=_lG;}var _lK=_lD,_lL=_lK;}else{var _lL=[0];}return _lL;}),[1,new T(function(){return B(_lt(_lc,_lk));}),[1,new T(function(){return B(_lt(_lb,E(_lA)[1]));}),[1,new T(function(){return B((function(_lM){var _lN=B(_kV(_4v,B(_kp(_kj,B(_f2(_kS,_lM))))));return _lN[0]==0?[0]:B(_ll(_lN[1],_lN[2]));})(E(_lA)[2]));}),_9]]]])))))));});}},_lO=[1,_9,_9],_lP=function(_lQ,_lR){var _lS=function(_lT,_lU){var _lV=E(_lT);if(!_lV[0]){return E(_lU);}else{var _lW=_lV[1],_lX=E(_lU);if(!_lX[0]){return E(_lV);}else{var _lY=_lX[1];return B(A(_lQ,[_lW,_lY]))==2?[1,_lY,new T(function(){return B(_lS(_lV,_lX[2]));})]:[1,_lW,new T(function(){return B(_lS(_lV[2],_lX));})];}}},_lZ=function(_m0){var _m1=E(_m0);if(!_m1[0]){return [0];}else{var _m2=E(_m1[2]);return _m2[0]==0?E(_m1):[1,new T(function(){return B(_lS(_m1[1],_m2[1]));}),new T(function(){return B(_lZ(_m2[2]));})];}},_m3=function(_m4){while(1){var _m5=E(_m4);if(!_m5[0]){return E(new T(function(){return B(_m3(B(_lZ(_9))));}));}else{if(!E(_m5[2])[0]){return E(_m5[1]);}else{_m4=B(_lZ(_m5));continue;}}}},_m6=new T(function(){return B(_m7(_9));}),_m7=function(_m8){var _m9=E(_m8);if(!_m9[0]){return E(_lO);}else{var _ma=_m9[1],_mb=E(_m9[2]);if(!_mb[0]){return [1,_m9,_9];}else{var _mc=_mb[1],_md=_mb[2];if(B(A(_lQ,[_ma,_mc]))==2){return new F(function(){return (function(_me,_mf,_mg){while(1){var _mh=(function(_mi,_mj,_mk){var _ml=E(_mk);if(!_ml[0]){return [1,[1,_mi,_mj],_m6];}else{var _mm=_ml[1];if(B(A(_lQ,[_mi,_mm]))==2){_me=_mm;var _mn=[1,_mi,_mj];_mg=_ml[2];_mf=_mn;return null;}else{return [1,[1,_mi,_mj],new T(function(){return B(_m7(_ml));})];}}})(_me,_mf,_mg);if(_mh!=null){return _mh;}}})(_mc,[1,_ma,_9],_md);});}else{return new F(function(){return (function(_mo,_mp,_mq){while(1){var _mr=(function(_ms,_mt,_mu){var _mv=E(_mu);if(!_mv[0]){return [1,new T(function(){return B(A(_mt,[[1,_ms,_9]]));}),_m6];}else{var _mw=_mv[1],_mx=_mv[2];switch(B(A(_lQ,[_ms,_mw]))){case 0:_mo=_mw;_mp=function(_my){return new F(function(){return A(_mt,[[1,_ms,_my]]);});};_mq=_mx;return null;case 1:_mo=_mw;_mp=function(_mz){return new F(function(){return A(_mt,[[1,_ms,_mz]]);});};_mq=_mx;return null;default:return [1,new T(function(){return B(A(_mt,[[1,_ms,_9]]));}),new T(function(){return B(_m7(_mv));})];}}})(_mo,_mp,_mq);if(_mr!=null){return _mr;}}})(_mc,function(_mA){return [1,_ma,_mA];},_md);});}}}};return new F(function(){return _m3(B(_m7(_lR)));});},_mB=function(_mC,_mD,_mE,_mF){return new F(function(){return _e(B(_k8(_mC,_mD,_mE)),[1,_k4,new T(function(){return B(_l8(_k3,_k2,_k1,_k0,_jZ,B(_lP(_jW,_mF))));})]);});},_mG=function(_mH){var _mI=E(_mH),_mJ=E(_mI[1]);return new F(function(){return _mB(_mJ[1],_mJ[2],_mJ[3],_mI[2]);});},_mK=function(_mL,_mM,_mN,_mO,_mP,_mQ,_mR,_mS,_mT){return new F(function(){return _2J(function(_mU,_mV){return new F(function(){return _e(B(_fa(_mL,_mM,_mN,_mO,_mP,_mQ,_mR,_mU)),_mV);});},_mS,_mT);});},_mW=function(_mX,_mY,_mZ,_n0,_n1,_n2,_n3,_n4,_n5,_n6){return new F(function(){return _e(B(_fa(_mX,_mY,_mZ,_n0,_n1,_n2,_n3,_n5)),_n6);});},_n7=function(_n8,_n9,_na,_nb,_nc,_nd,_ne){return [0,function(_nf,_fO,_fP){return new F(function(){return _mW(_n8,_n9,_na,_nb,_nc,_nd,_ne,_nf,_fO,_fP);});},function(_fP){return new F(function(){return _fa(_n8,_n9,_na,_nb,_nc,_nd,_ne,_fP);});},function(_fO,_fP){return new F(function(){return _mK(_n8,_n9,_na,_nb,_nc,_nd,_ne,_fO,_fP);});}];},_ng=new T(function(){return B(unCStr(" \u2234 "));}),_nh=new T(function(){return B(unCStr(" . "));}),_ni=function(_nj){return E(E(_nj)[2]);},_nk=function(_nl,_nm,_nn,_no){var _np=B(_f2(new T(function(){return B(_ni(_nl));}),B(_kV(_nm,_nn))));if(!_np[0]){return new F(function(){return _e(_ng,new T(function(){return B(A(_ni,[_nl,_no]));},1));});}else{return new F(function(){return _e(B(_eZ([1,_np[1],new T(function(){return B(_f6(_nh,_np[2]));})])),new T(function(){return B(_e(_ng,new T(function(){return B(A(_ni,[_nl,_no]));},1)));},1));});}},_nq=function(_nr,_ns,_nt){while(1){var _nu=E(_ns);if(!_nu[0]){return E(_nt)[0]==0?true:false;}else{var _nv=E(_nt);if(!_nv[0]){return false;}else{if(!B(A(_6V,[_nr,_nu[1],_nv[1]]))){return false;}else{_ns=_nu[2];_nt=_nv[2];continue;}}}}},_nw=function(_nx,_ny,_nz){var _nA=E(_ny),_nB=E(_nz);return !B(_nq(_nx,_nA[1],_nB[1]))?true:!B(A(_6V,[_nx,_nA[2],_nB[2]]))?true:false;},_nC=function(_nD,_nE,_nF,_nG,_nH){return !B(_nq(_nD,_nE,_nG))?false:B(A(_6V,[_nD,_nF,_nH]));},_nI=function(_nJ,_nK,_nL){var _nM=E(_nK),_nN=E(_nL);return new F(function(){return _nC(_nJ,_nM[1],_nM[2],_nN[1],_nN[2]);});},_nO=function(_nP){return [0,function(_nQ,_nR){return new F(function(){return _nI(_nP,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _nw(_nP,_nQ,_nR);});}];},_nS=function(_nT,_nU,_nV){var _nW=E(_nU),_nX=E(_nV);return !B(_nq(_nT,_nW[1],_nX[1]))?true:!B(A(_6V,[_nT,_nW[2],_nX[2]]))?true:false;},_nY=function(_nZ,_o0,_o1){var _o2=E(_o0),_o3=E(_o1);return new F(function(){return _nC(_nZ,_o2[1],_o2[2],_o3[1],_o3[2]);});},_o4=function(_o5){return [0,function(_nQ,_nR){return new F(function(){return _nY(_o5,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _nS(_o5,_nQ,_nR);});}];},_o6=function(_o7,_o8,_o9){var _oa=E(_o7);switch(_oa[0]){case 0:var _ob=E(_o8);return _ob[0]==0?!B(_4b(_oa[3],_ob[3]))?[0]:[1,_o9]:[0];case 1:var _oc=E(_o8);return _oc[0]==1?!B(_4b(_oa[3],_oc[3]))?[0]:[1,_o9]:[0];case 2:var _od=E(_o8);return _od[0]==2?!B(_4b(_oa[3],_od[3]))?[0]:[1,_o9]:[0];case 3:var _oe=E(_o8);return _oe[0]==3?!B(_4b(_oa[3],_oe[3]))?[0]:[1,_o9]:[0];case 4:var _of=E(_o8);return _of[0]==4?!B(_4b(_oa[3],_of[3]))?[0]:[1,_o9]:[0];case 5:var _og=E(_o8);return _og[0]==5?!B(_4b(_oa[3],_og[3]))?[0]:[1,_o9]:[0];case 6:var _oh=E(_o8);return _oh[0]==6?!B(_4b(_oa[3],_oh[3]))?[0]:[1,_o9]:[0];case 7:var _oi=E(_o8);return _oi[0]==7?!B(_4b(_oa[3],_oi[3]))?[0]:[1,_o9]:[0];case 8:var _oj=E(_o8);return _oj[0]==8?!B(_4b(_oa[3],_oj[3]))?[0]:[1,_o9]:[0];default:var _ok=E(_o8);return _ok[0]==9?!B(_4b(_oa[3],_ok[3]))?[0]:[1,_o9]:[0];}},_ol=new T(function(){return B(_3r("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_om=function(_on,_oo){return [3,_,_on,_oo];},_op=function(_oq,_or,_os){while(1){var _ot=E(_os);if(!_ot[0]){return [0];}else{var _ou=E(_ot[1]),_ov=B(A(_oq,[_or,_ou[2],_ou[3]]));if(!_ov[0]){_os=_ot[2];continue;}else{return E(_ov);}}}},_ow=function(_ox,_oy){while(1){var _oz=(function(_oA,_oB){var _oC=E(_oB);switch(_oC[0]){case 2:var _oD=B(_op(_o6,_oC[2],_oA));if(!_oD[0]){return E(_oC);}else{var _oE=_oA;_oy=_oD[1];_ox=_oE;return null;}break;case 4:var _oF=_oC[3],_oG=B(_op(_o6,_oC[2],_oA));if(!_oG[0]){return E(_oC);}else{var _oH=E(_oG[1]);switch(_oH[0]){case 3:return E(_oH[3])[0]==0?B(_om(_oH[2],_oF)):E(_oC);case 4:if(!E(_oH[3])[0]){var _oE=_oA;_oy=[4,_,_oH[2],_oF];_ox=_oE;return null;}else{return E(_oC);}break;default:return E(_oC);}}break;case 6:var _oI=_oC[3],_oJ=_oC[4],_oK=B(_op(_o6,_oC[2],_oA));if(!_oK[0]){return E(_oC);}else{var _oL=E(_oK[1]);switch(_oL[0]){case 5:if(!E(_oL[3])[0]){if(!E(_oL[4])[0]){var _oE=_oA;_oy=[5,_,_oL[2],_oI,_oJ];_ox=_oE;return null;}else{return E(_oC);}}else{return E(_oC);}break;case 6:if(!E(_oL[3])[0]){if(!E(_oL[4])[0]){var _oE=_oA;_oy=[6,_,_oL[2],_oI,_oJ];_ox=_oE;return null;}else{return E(_oC);}}else{return E(_oC);}break;default:return E(_oC);}}break;case 7:return [7,_,_oC[2],new T(function(){return B(_ow(_oA,_oC[3]));})];case 8:var _oM=_oC[2],_oN=_oC[3],_oO=B(_op(_o6,_oM,_oA));if(!_oO[0]){return [8,_,_oM,new T(function(){return B(_ow(_oA,_oN));})];}else{var _oP=E(_oO[1]);switch(_oP[0]){case 7:return E(_oP[3])[0]==0?[7,_,_oP[2],new T(function(){return B(_ow(_oA,_oN));})]:[8,_,_oM,new T(function(){return B(_ow(_oA,_oN));})];case 8:if(!E(_oP[3])[0]){var _oE=_oA;_oy=[8,_,_oP[2],_oN];_ox=_oE;return null;}else{return [8,_,_oM,new T(function(){return B(_ow(_oA,_oN));})];}break;default:return [8,_,_oM,new T(function(){return B(_ow(_oA,_oN));})];}}break;case 9:return [9,_,_oC[2],new T(function(){return B(_ow(_oA,_oC[3]));}),new T(function(){return B(_ow(_oA,_oC[4]));})];case 10:var _oQ=_oC[2],_oR=_oC[3],_oS=_oC[4],_oT=B(_op(_o6,_oQ,_oA));if(!_oT[0]){return [10,_,_oQ,new T(function(){return B(_ow(_oA,_oR));}),new T(function(){return B(_ow(_oA,_oS));})];}else{var _oU=E(_oT[1]);switch(_oU[0]){case 9:return E(_oU[3])[0]==0?E(_oU[4])[0]==0?[9,_,_oU[2],new T(function(){return B(_ow(_oA,B(_ow(_oA,_oR))));}),new T(function(){return B(_ow(_oA,B(_ow(_oA,_oS))));})]:[10,_,_oQ,new T(function(){return B(_ow(_oA,_oR));}),new T(function(){return B(_ow(_oA,_oS));})]:[10,_,_oQ,new T(function(){return B(_ow(_oA,_oR));}),new T(function(){return B(_ow(_oA,_oS));})];case 10:if(!E(_oU[3])[0]){if(!E(_oU[4])[0]){var _oE=_oA;_oy=[10,_,_oU[2],_oR,_oS];_ox=_oE;return null;}else{return [10,_,_oQ,new T(function(){return B(_ow(_oA,_oR));}),new T(function(){return B(_ow(_oA,_oS));})];}}else{return [10,_,_oQ,new T(function(){return B(_ow(_oA,_oR));}),new T(function(){return B(_ow(_oA,_oS));})];}break;default:return [10,_,_oQ,new T(function(){return B(_ow(_oA,_oR));}),new T(function(){return B(_ow(_oA,_oS));})];}}break;case 11:return [11,_,_oC[2],function(_oV){return new F(function(){return _ow(_oA,B(A(_oC[3],[_oV])));});}];case 12:var _oW=_oC[2],_oX=_oC[3],_oY=B(_op(_o6,_oW,_oA));if(!_oY[0]){return [12,_,_oW,function(_oZ){return new F(function(){return _ow(_oA,B(A(_oX,[_oZ])));});}];}else{var _p0=E(_oY[1]);switch(_p0[0]){case 11:return [11,_,_p0[2],function(_p1){return new F(function(){return _ow(_oA,B(A(_oX,[_p1])));});}];case 12:var _oE=_oA;_oy=[12,_,_p0[2],_oX];_ox=_oE;return null;default:return [12,_,_oW,function(_p2){return new F(function(){return _ow(_oA,B(A(_oX,[_p2])));});}];}}break;default:return E(_oC);}})(_ox,_oy);if(_oz!=null){return _oz;}}},_p3=function(_p4,_p5){var _p6=E(_p5);if(!_p6[0]){var _p7=B(_op(_o6,_p6[1],_p4));if(!_p7[0]){return E(_p6);}else{var _p8=E(_p7[1]);return _p8[0]==0?E(_ol):[1,new T(function(){return B(_f2(function(_p9){return new F(function(){return _ow(_p4,_p9);});},_p8[1]));})];}}else{return [1,new T(function(){return B(_f2(function(_pa){return new F(function(){return _ow(_p4,_pa);});},_p6[1]));})];}},_pb=function(_pc,_pd,_pe,_pf,_pg,_ph,_pi,_pj,_pk){var _pl=E(_pk);return [0,new T(function(){return B(_f2(function(_pm){return new F(function(){return _p3(_pj,_pm);});},_pl[1]));}),new T(function(){return B(_p3(_pj,_pl[2]));})];},_pn=function(_po,_pp,_pq,_pr,_ps,_pt,_pu,_pv,_pw){var _px=E(_pw);return [0,new T(function(){return B(_f2(function(_py){return new F(function(){return _pb(_po,_pp,_pq,_pr,_ps,_pt,_pu,_pv,_py);});},_px[1]));}),new T(function(){return B(_pb(_po,_pp,_pq,_pr,_ps,_pt,_pu,_pv,_px[2]));})];},_pz=function(_pA){return E(E(_pA)[1]);},_pB=function(_pC,_pD){var _pE=E(_pD);return new F(function(){return A(_pz,[_pE[1],E(_pC)[2],_pE[2]]);});},_pF=function(_pG,_pH,_pI){var _pJ=E(_pI);if(!_pJ[0]){return [0];}else{var _pK=_pJ[1],_pL=_pJ[2];return !B(A(_pG,[_pH,_pK]))?[1,_pK,new T(function(){return B(_pF(_pG,_pH,_pL));})]:E(_pL);}},_pM=function(_pN,_pO,_pP){while(1){var _pQ=E(_pP);if(!_pQ[0]){return false;}else{if(!B(A(_pN,[_pO,_pQ[1]]))){_pP=_pQ[2];continue;}else{return true;}}}},_pR=function(_pS,_pT){var _pU=function(_pV,_pW){while(1){var _pX=(function(_pY,_pZ){var _q0=E(_pY);if(!_q0[0]){return [0];}else{var _q1=_q0[1],_q2=_q0[2];if(!B(_pM(_pS,_q1,_pZ))){return [1,_q1,new T(function(){return B(_pU(_q2,[1,_q1,_pZ]));})];}else{_pV=_q2;var _q3=_pZ;_pW=_q3;return null;}}})(_pV,_pW);if(_pX!=null){return _pX;}}};return new F(function(){return _pU(_pT,_9);});},_q4=function(_q5,_q6,_q7){return new F(function(){return _e(_q6,new T(function(){return B((function(_q8,_q9){while(1){var _qa=E(_q9);if(!_qa[0]){return E(_q8);}else{var _qb=B(_pF(_q5,_qa[1],_q8));_q9=_qa[2];_q8=_qb;continue;}}})(B(_pR(_q5,_q7)),_q6));},1));});},_qc=function(_qd,_qe){while(1){var _qf=(function(_qg,_qh){var _qi=E(_qh);switch(_qi[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_qg,_qi[2]],_9];case 3:var _qj=_qg;_qe=_qi[3];_qd=_qj;return null;case 4:return new F(function(){return _q4(_pB,[1,[0,_qg,_qi[2]],_9],new T(function(){return B(_qc(_qg,_qi[3]));},1));});break;case 5:return new F(function(){return _q4(_pB,B(_qc(_qg,_qi[3])),new T(function(){return B(_qc(_qg,_qi[4]));},1));});break;default:return new F(function(){return _q4(_pB,B(_q4(_pB,[1,[0,_qg,_qi[2]],_9],new T(function(){return B(_qc(_qg,_qi[3]));},1))),new T(function(){return B(_qc(_qg,_qi[4]));},1));});}})(_qd,_qe);if(_qf!=null){return _qf;}}},_qk=function(_ql,_qm,_qn,_qo){while(1){var _qp=(function(_qq,_qr,_qs,_qt){var _qu=E(_qt);switch(_qu[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_qq,_qu[2]],_9];case 3:return new F(function(){return _qc(_qq,_qu[3]);});break;case 4:return new F(function(){return _q4(_pB,[1,[0,_qq,_qu[2]],_9],new T(function(){return B(_qc(_qq,_qu[3]));},1));});break;case 5:return new F(function(){return _q4(_pB,B(_qc(_qq,_qu[3])),new T(function(){return B(_qc(_qq,_qu[4]));},1));});break;case 6:return new F(function(){return _q4(_pB,B(_q4(_pB,[1,[0,_qq,_qu[2]],_9],new T(function(){return B(_qc(_qq,_qu[3]));},1))),new T(function(){return B(_qc(_qq,_qu[4]));},1));});break;case 7:var _qv=_qq,_qw=_qr,_qx=_qs;_qo=_qu[3];_ql=_qv;_qm=_qw;_qn=_qx;return null;case 8:return new F(function(){return _q4(_pB,[1,[0,_qq,_qu[2]],_9],new T(function(){return B(_qk(_qq,_qr,_qs,_qu[3]));},1));});break;case 9:return new F(function(){return _q4(_pB,B(_qk(_qq,_qr,_qs,_qu[3])),new T(function(){return B(_qk(_qq,_qr,_qs,_qu[4]));},1));});break;case 10:return new F(function(){return _q4(_pB,B(_q4(_pB,[1,[0,_qq,_qu[2]],_9],new T(function(){return B(_qk(_qq,_qr,_qs,_qu[3]));},1))),new T(function(){return B(_qk(_qq,_qr,_qs,_qu[4]));},1));});break;case 11:var _qv=_qq,_qw=_qr,_qx=_qs;_qo=B(A(_qu[3],[_eK]));_ql=_qv;_qm=_qw;_qn=_qx;return null;default:return new F(function(){return _q4(_pB,[1,[0,_qq,_qu[2]],_9],new T(function(){return B(_qk(_qq,_qr,_qs,B(A(_qu[3],[_eK]))));},1));});}})(_ql,_qm,_qn,_qo);if(_qp!=null){return _qp;}}},_qy=function(_qz,_qA,_qB,_qC,_qD){var _qE=function(_qF){return new F(function(){return _qk(_qz,_qA,_qB,_qF);});};return new F(function(){return _e(B(_km(B(_f2(function(_qG){var _qH=E(_qG);if(!_qH[0]){return [1,[0,_qz,_qH[1]],_9];}else{return new F(function(){return _km(B(_f2(_qE,_qH[1])));});}},_qC)))),new T(function(){var _qI=E(_qD);if(!_qI[0]){var _qJ=[1,[0,_qz,_qI[1]],_9];}else{var _qJ=B(_km(B(_f2(_qE,_qI[1]))));}return _qJ;},1));});},_qK=function(_qL,_qM,_qN,_qO,_qP,_qQ,_qR,_qS,_qT){var _qU=E(_qT);return new F(function(){return _e(B(_km(B(_f2(function(_qV){var _qW=E(_qV);return new F(function(){return _qy(_qL,_qP,_qQ,_qW[1],_qW[2]);});},_qU[1])))),new T(function(){var _qX=E(_qU[2]);return B(_qy(_qL,_qP,_qQ,_qX[1],_qX[2]));},1));});},_qY=function(_qZ,_r0,_r1,_r2,_r3,_r4,_r5,_r6,_r7,_r8,_r9){return [0,_qZ,_r0,_r1,_r2,function(_py){return new F(function(){return _qK(_qZ,_r3,_r4,_r5,_r6,_r7,_r8,_r9,_py);});},function(_ra,_py){return new F(function(){return _pn(_r3,_r4,_r5,_r6,_r7,_r8,_r9,_ra,_py);});}];},_rb=function(_rc){return E(E(_rc)[2]);},_rd=function(_re){return E(E(_re)[1]);},_rf=[0,_rd,_rb],_rg=new T(function(){return B(unCStr(" \u2234 "));}),_rh=function(_ri,_rj,_rk,_rl){return new F(function(){return _e(B(A(_rj,[_rk,_9])),new T(function(){return B(_e(_rg,new T(function(){return B(A(_ri,[_rl]));},1)));},1));});},_rm=function(_rn,_ro){var _rp=E(_rn),_rq=E(_ro);return new F(function(){return _rh(_rp[2],_rp[3],_rq[1],_rq[2]);});},_rr=function(_rs,_rt,_ru,_rv,_rw){return new F(function(){return _e(B(A(_rt,[_ru,_9])),new T(function(){return B(_e(_rg,new T(function(){return B(_e(B(A(_rs,[_rv])),_rw));},1)));},1));});},_rx=function(_ry,_rz,_rA){return new F(function(){return _2J(function(_rB,_rC){var _rD=E(_ry),_rE=E(_rB);return new F(function(){return _rr(_rD[2],_rD[3],_rE[1],_rE[2],_rC);});},_rz,_rA);});},_rF=function(_rG,_rH,_rI,_rJ){var _rK=E(_rG),_rL=E(_rI);return new F(function(){return _rr(_rK[2],_rK[3],_rL[1],_rL[2],_rJ);});},_rM=function(_rN){return [0,function(_rO,_nQ,_nR){return new F(function(){return _rF(_rN,_rO,_nQ,_nR);});},function(_nR){return new F(function(){return _rm(_rN,_nR);});},function(_nQ,_nR){return new F(function(){return _rx(_rN,_nQ,_nR);});}];},_rP=new T(function(){return B(unCStr(", "));}),_rQ=new T(function(){return B(unCStr(" \u22a2 "));}),_rR=new T(function(){return B(_km(_9));}),_rS=function(_rT,_rU,_rV){var _rW=B(_f2(new T(function(){return B(_ni(_rT));}),_rU));if(!_rW[0]){return new F(function(){return _e(_rR,new T(function(){return B(_e(_rQ,new T(function(){return B(A(_ni,[_rT,_rV]));},1)));},1));});}else{return new F(function(){return _e(B(_km([1,_rW[1],new T(function(){return B(_f6(_rP,_rW[2]));})])),new T(function(){return B(_e(_rQ,new T(function(){return B(A(_ni,[_rT,_rV]));},1)));},1));});}},_rX=function(_rY,_rZ){var _s0=E(_rZ);return new F(function(){return _rS(_rY,_s0[1],_s0[2]);});},_s1=function(_s2,_s3,_s4){return new F(function(){return _2J(function(_s5,_s6){var _s7=E(_s5);return new F(function(){return _e(B(_rS(_s2,_s7[1],_s7[2])),_s6);});},_s3,_s4);});},_s8=function(_s9,_sa,_sb,_sc){var _sd=E(_sb);return new F(function(){return _e(B(_rS(_s9,_sd[1],_sd[2])),_sc);});},_se=function(_sf){return [0,function(_rO,_nQ,_nR){return new F(function(){return _s8(_sf,_rO,_nQ,_nR);});},function(_nR){return new F(function(){return _rX(_sf,_nR);});},function(_nQ,_nR){return new F(function(){return _s1(_sf,_nQ,_nR);});}];},_sg=function(_sh,_si){return new F(function(){return _e(B(_ex(_sh)),_si);});},_sj=function(_sk,_sl){return new F(function(){return _2J(_sg,_sk,_sl);});},_sm=function(_sn,_so,_sp){return new F(function(){return _e(B(_ex(_so)),_sp);});},_sq=[0,_sm,_ex,_sj],_sr=function(_ss,_st,_su,_sv,_sw,_sx,_sy,_sz,_sA,_sB,_sC,_sD){var _sE=E(_sD);return new F(function(){return _qy(_ss,_sz,_sA,_sE[1],_sE[2]);});},_sF=function(_sG,_sH,_sI,_sJ,_sK,_sL,_sM,_sN,_sO,_sP,_sQ){return [0,_sG,_sH,_sI,_sJ,function(_py){return new F(function(){return _sr(_sG,_sH,_sI,_sJ,_sK,_sL,_sM,_sN,_sO,_sP,_sQ,_py);});},function(_ra,_py){return new F(function(){return _pb(_sK,_sL,_sM,_sN,_sO,_sP,_sQ,_ra,_py);});}];},_sR=function(_sS,_sT){return [0];},_sU=function(_sV,_sW,_sX,_sY,_sZ,_t0,_t1,_t2,_t3,_t4,_t5,_t6,_t7,_t8){return [0,_sV,_sW,_sR,_1];},_t9=function(_ta,_tb,_tc,_td,_te,_tf,_tg,_th,_ti,_tj,_tk,_tl){var _tm=E(_tl);if(!_tm[0]){return [1,[0,_ta,_tm[1]],_9];}else{return new F(function(){return _km(B(_f2(function(_tn){return new F(function(){return _qk(_ta,_th,_ti,_tn);});},_tm[1])));});}},_to=function(_tp,_tq,_tr,_ts,_tt,_tu,_tv,_tw,_tx,_ty,_tz){return [0,_tp,_tq,_tr,_ts,function(_py){return new F(function(){return _t9(_tp,_tq,_tr,_ts,_tt,_tu,_tv,_tw,_tx,_ty,_tz,_py);});},_p3];},_tA=function(_tB){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_tB));}))));});},_tC=new T(function(){return B(_tA("w_sCfQ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r141}\n                  sv{tv aBU5} [tv] quant{tv aBU3} [tv]"));}),_tD=new T(function(){return B(_tA("w_sCfP{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  quant{tv aBU3} [tv]"));}),_tE=new T(function(){return B(_tA("w_sCfO{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  con{tv aBU2} [tv]"));}),_tF=new T(function(){return B(_tA("w_sCfN{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  sv{tv aBU5} [tv]"));}),_tG=new T(function(){return B(_tA("w_sCfM{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  pred{tv aBU1} [tv]"));}),_tH=new T(function(){return B(_tA("w_sCfL{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  f{tv aBU4} [tv]"));}),_tI=new T(function(){return B(_tA("w_sCfR{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13b}\n                  sv{tv aBU5} [tv]"));}),_tJ=new T(function(){return B(_tA("w_sCfK{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  quant{tv aBU3} [tv]"));}),_tK=new T(function(){return B(_tA("w_sCfJ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  con{tv aBU2} [tv]"));}),_tL=new T(function(){return B(_tA("w_sCfI{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  sv{tv aBU5} [tv]"));}),_tM=new T(function(){return B(_tA("w_sCfH{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  pred{tv aBU1} [tv]"));}),_tN=new T(function(){return B(_tA("w_sCfG{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  f{tv aBU4} [tv]"));}),_tO=function(_tP,_tQ){return function(_tR,_tS){var _tT=E(_tR);return _tT[0]==0?[1,[0,new T(function(){return B(_tU(_tP,_tQ,_tN,_tM,_tL,_tK,_tJ,_tH,_tG,_tF,_tE,_tD,_tC,_tI));}),_tT[1],_tS]]:[0];};},_tV=function(_tW){return [0,E(_tW)];},_tU=function(_tX,_tY,_tZ,_u0,_u1,_u2,_u3,_u4,_u5,_u6,_u7,_u8,_u9,_ua){return [0,_tX,_tY,new T(function(){return B(_tO(_tX,_tY));}),_tV];},_ub=[1,_9],_uc=function(_ud,_ue){while(1){var _uf=E(_ud);if(!_uf[0]){return E(_ue);}else{_ud=_uf[2];var _ug=_ue+1|0;_ue=_ug;continue;}}},_uh=[0,95],_ui=[1,_uh,_9],_uj=[1,_ui,_9],_uk=function(_ul,_um,_un){return !B(_4b(B(A(_ul,[_um,_uj])),B(A(_ul,[_un,_uj]))))?true:false;},_uo=function(_up){return [0,function(_uq,_ur){return new F(function(){return _4b(B(A(_up,[_uq,_uj])),B(A(_up,[_ur,_uj])));});},function(_fO,_fP){return new F(function(){return _uk(_up,_fO,_fP);});}];},_us=function(_ut,_uu){return new F(function(){return _ow(_ut,_uu);});},_uv=function(_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG){return [0,_uw,_ux,_uy,_uz,function(_uH){return new F(function(){return _qk(_uw,_uD,_uE,_uH);});},_us];},_uI=new T(function(){return B(_tA("w_szpk{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r141}\n                  sv{tv awoX} [tv] quant{tv awoV} [tv]"));}),_uJ=new T(function(){return B(_tA("w_szpj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  quant{tv awoV} [tv]"));}),_uK=new T(function(){return B(_tA("w_szpi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  con{tv awoU} [tv]"));}),_uL=new T(function(){return B(_tA("w_szph{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  sv{tv awoX} [tv]"));}),_uM=new T(function(){return B(_tA("w_szpg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  pred{tv awoT} [tv]"));}),_uN=new T(function(){return B(_tA("w_szpf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc r4i}\n                  f{tv awoW} [tv]"));}),_uO=new T(function(){return B(_tA("w_szpl{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13b}\n                  sv{tv awoX} [tv]"));}),_uP=new T(function(){return B(_tA("w_szpe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  quant{tv awoV} [tv]"));}),_uQ=new T(function(){return B(_tA("w_szpd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  con{tv awoU} [tv]"));}),_uR=new T(function(){return B(_tA("w_szpc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  sv{tv awoX} [tv]"));}),_uS=new T(function(){return B(_tA("w_szpb{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  pred{tv awoT} [tv]"));}),_uT=new T(function(){return B(_tA("w_szpa{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  f{tv awoW} [tv]"));}),_uU=function(_uV,_uW,_uX,_uY){var _uZ=E(_uX);switch(_uZ[0]){case 2:return [1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_uZ[2],_uY]];case 4:var _v1=_uZ[2];if(!E(_uZ[3])[0]){var _v2=E(_uY);switch(_v2[0]){case 3:return E(_v2[3])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v1,_v2]]:[0];case 4:return E(_v2[3])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v1,_v2]]:[0];default:return [0];}}else{return [0];}break;case 6:var _v3=_uZ[2];if(!E(_uZ[3])[0]){if(!E(_uZ[4])[0]){var _v4=E(_uY);switch(_v4[0]){case 5:return E(_v4[3])[0]==0?E(_v4[4])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v3,_v4]]:[0]:[0];case 6:return E(_v4[3])[0]==0?E(_v4[4])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v3,_v4]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _v5=_uZ[2];if(!E(_uZ[3])[0]){var _v6=E(_uY);switch(_v6[0]){case 7:return E(_v6[3])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v5,_v6]]:[0];case 8:return E(_v6[3])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v5,_v6]]:[0];default:return [0];}}else{return [0];}break;case 10:var _v7=_uZ[2];if(!E(_uZ[3])[0]){if(!E(_uZ[4])[0]){var _v8=E(_uY);switch(_v8[0]){case 9:return E(_v8[3])[0]==0?E(_v8[4])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v7,_v8]]:[0]:[0];case 10:return E(_v8[3])[0]==0?E(_v8[4])[0]==0?[1,[0,new T(function(){return B(_v0(_uV,_uW,_uT,_uS,_uR,_uQ,_uP,_uN,_uM,_uL,_uK,_uJ,_uI,_uO));}),_v7,_v8]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_v9=new T(function(){return B(_3r("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_va=function(_vb){var _vc=E(_vb);switch(_vc[0]){case 3:return [2,_,_vc];case 4:return [4,_,_vc,_V];case 5:return [6,_,_vc,_V,_V];case 6:return [8,_,_vc,_S];case 7:return [10,_,_vc,_S,_S];default:return E(_v9);}},_v0=function(_vd,_ve,_vf,_vg,_vh,_vi,_vj,_vk,_vl,_vm,_vn,_vo,_vp,_vq){return [0,_vd,_ve,function(_vr,_vs){return new F(function(){return _uU(_vd,_ve,_vr,_vs);});},_va];},_vt=function(_vu,_vv,_vw){return new F(function(){return _2J(function(_vx,_vy){return new F(function(){return _e(B(A(_vu,[_vx,_uj])),_vy);});},_vv,_vw);});},_vz=function(_vA){return [0,function(_vB,_vC,_vD){return new F(function(){return _e(B(A(_vA,[_vC,_uj])),_vD);});},function(_vE){return new F(function(){return A(_vA,[_vE,_uj]);});},function(_fO,_fP){return new F(function(){return _vt(_vA,_fO,_fP);});}];},_vF=[1,_9],_vG=function(_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_vR,_vS){var _vT=E(_vR);if(_vT[0]==2){return E(_vF);}else{var _vU=E(_vS);if(_vU[0]==2){return E(_vF);}else{var _vV=function(_vW){var _vX=function(_vY){var _vZ=function(_w0){var _w1=function(_w2){var _w3=function(_w4){var _w5=function(_w6){var _w7=function(_w8){var _w9=function(_wa){var _wb=function(_wc){var _wd=function(_we){var _wf=function(_wg){var _wh=function(_wi){var _wj=E(_vT);switch(_wj[0]){case 1:var _wk=E(_vU);return _wk[0]==1?!B(A(_vI,[_wj[2],_wk[2]]))?[0]:E(_vF):[0];case 3:var _wl=E(_vU);return _wl[0]==3?!B(A(_vH,[_wj[2],_wl[2]]))?[0]:E(_vF):[0];case 4:var _wm=_wj[2],_wn=E(_vU);switch(_wn[0]){case 3:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[4,_,_wm,_V],[3,_,_wn[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[4,_,_wm,_V],[4,_,_wn[2],_V]]));}),_9]];default:return [0];}break;case 5:var _wp=E(_vU);return _wp[0]==5?!B(A(_vH,[_wj[2],_wp[2]]))?[0]:E(_vF):[0];case 6:var _wq=_wj[2],_wr=E(_vU);switch(_wr[0]){case 5:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[6,_,_wq,_V,_V],[5,_,_wr[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[6,_,_wq,_V,_V],[6,_,_wr[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _ws=E(_vU);return _ws[0]==7?!B(A(_vJ,[_wj[2],_ws[2]]))?[0]:[1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wj[3],_ws[3]]));}),_9]]:[0];case 8:var _wt=_wj[2],_wu=_wj[3],_wv=E(_vU);switch(_wv[0]){case 7:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[8,_,_wt,_S],[7,_,_wv[2],_S]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wu,_wv[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[8,_,_wt,_S],[8,_,_wv[2],_S]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wu,_wv[3]]));}),_9]]];default:return [0];}break;case 9:var _ww=E(_vU);return _ww[0]==9?!B(A(_vJ,[_wj[2],_ww[2]]))?[0]:[1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wj[3],_ww[3]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wj[4],_ww[4]]));}),_9]]]:[0];case 10:var _wx=_wj[2],_wy=_wj[3],_wz=_wj[4],_wA=function(_wB){var _wC=E(_vU);switch(_wC[0]){case 9:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[10,_,_wx,_S,_S],[9,_,_wC[2],_S,_S]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wy,_wC[3]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wz,_wC[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,[10,_,_wx,_S,_S],[10,_,_wC[2],_S,_S]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wy,_wC[3]]));}),[1,new T(function(){return B(A(_wo,[_vH,_vI,_vJ,_vK,_vL,_vM,_vN,_vO,_vP,_vQ,_wz,_wC[4]]));}),_9]]]];default:return [0];}};return E(_wy)[0]==0?E(_wz)[0]==0?E(_vF):B(_wA(_)):B(_wA(_));default:return [0];}},_wD=E(_vU);return _wD[0]==10?E(_wD[3])[0]==0?E(_wD[4])[0]==0?E(_vF):B(_wh(_)):B(_wh(_)):B(_wh(_));},_wE=E(_vT);return _wE[0]==8?E(_wE[3])[0]==0?E(_vF):B(_wf(_)):B(_wf(_));},_wF=E(_vU);switch(_wF[0]){case 6:return E(_wF[3])[0]==0?E(_wF[4])[0]==0?E(_vF):B(_wd(_)):B(_wd(_));case 8:return E(_wF[3])[0]==0?E(_vF):B(_wd(_));default:return new F(function(){return _wd(_);});}},_wG=E(_vT);return _wG[0]==6?E(_wG[3])[0]==0?E(_wG[4])[0]==0?E(_vF):B(_wb(_)):B(_wb(_)):B(_wb(_));},_wH=E(_vU);return _wH[0]==4?E(_wH[3])[0]==0?E(_vF):B(_w9(_)):B(_w9(_));},_wI=E(_vT);switch(_wI[0]){case 4:return E(_wI[3])[0]==0?E(_vF):B(_w7(_));case 9:return E(_wI[3])[0]==0?E(_wI[4])[0]==0?E(_vF):B(_w7(_)):B(_w7(_));default:return new F(function(){return _w7(_);});}},_wJ=E(_vU);return _wJ[0]==9?E(_wJ[3])[0]==0?E(_wJ[4])[0]==0?E(_vF):B(_w5(_)):B(_w5(_)):B(_w5(_));},_wK=E(_vT);return _wK[0]==7?E(_wK[3])[0]==0?E(_vF):B(_w3(_)):B(_w3(_));},_wL=E(_vU);switch(_wL[0]){case 5:return E(_wL[3])[0]==0?E(_wL[4])[0]==0?E(_vF):B(_w1(_)):B(_w1(_));case 7:return E(_wL[3])[0]==0?E(_vF):B(_w1(_));default:return new F(function(){return _w1(_);});}},_wM=E(_vT);return _wM[0]==5?E(_wM[3])[0]==0?E(_wM[4])[0]==0?E(_vF):B(_vZ(_)):B(_vZ(_)):B(_vZ(_));},_wN=E(_vU);return _wN[0]==3?E(_wN[3])[0]==0?E(_vF):B(_vX(_)):B(_vX(_));},_wO=E(_vT);return _wO[0]==3?E(_wO[3])[0]==0?E(_vF):B(_vV(_)):B(_vV(_));}}},_wP=function(_wQ,_wR,_wS){return [0,_wQ,_wR,_wS];},_wT=new T(function(){return B(_tA("w_szpt{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  quant{tv awoi} [tv]"));}),_wU=new T(function(){return B(_tA("w_szpp{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  f{tv awoj} [tv]"));}),_wV=function(_wW){return [0,function(_wX,_wY){return B(A(_wW,[_wX,_wY,_1]))[0]==0?false:true;},function(_wZ,_x0){return B(A(_wW,[_wZ,_x0,_1]))[0]==0?true:false;}];},_x1=new T(function(){return B(_wV(_o6));}),_wo=function(_x2,_x3,_x4,_x5,_x6,_x7,_x8,_x9,_xa,_xb){var _xc=function(_xd,_xe){return new F(function(){return _eL(_x6,_x8,_x9,_x7,_x5,_xa,_xb,_xd);});};return function(_58,_xf){return new F(function(){return _wP(new T(function(){return B(_v0(function(_xg,_xh){return new F(function(){return _vG(_x2,_x3,_x4,_x5,_x6,_x7,_x8,_x9,_xa,_xb,_xg,_xh);});},new T(function(){return B(_uv(_x1,_sq,new T(function(){return B(_uo(_xc));}),new T(function(){return B(_vz(_xc));}),_x6,_x8,_x9,_x5,_x7,_xa,_xb));}),_wU,_x2,_x3,_x4,_wT,_x5,_x6,_x7,_x8,_x9,_xa,_xb));}),_58,_xf);});};},_xi=function(_xj,_xk,_xl){var _xm=E(_xk);if(!_xm[0]){return [0];}else{var _xn=E(_xl);return _xn[0]==0?[0]:[1,new T(function(){return B(A(_xj,[_xm[1],_xn[1]]));}),new T(function(){return B(_xi(_xj,_xm[2],_xn[2]));})];}},_xo=function(_xp,_xq,_xr,_xs,_xt,_xu,_xv,_xw,_xx,_xy,_xz,_xA){var _xB=E(_xz);if(!_xB[0]){return E(_ub);}else{var _xC=_xB[1],_xD=E(_xA);if(!_xD[0]){return E(_ub);}else{var _xE=_xD[1];return B(_uc(_xC,0))!=B(_uc(_xE,0))?[0]:[1,new T(function(){return B(_xi(new T(function(){return B(_wo(_xp,_xq,_xr,_xs,_xt,_xu,_xv,_xw,_xx,_xy));}),_xC,_xE));})];}}},_xF=new T(function(){return B(_tA("w_sCgB{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  f{tv aBTL} [tv]"));}),_xG=new T(function(){return B(_tA("w_sCgF{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  quant{tv aBTK} [tv]"));}),_xH=new T(function(){return B(_wV(_o6));}),_xI=function(_xJ,_xK,_xL,_xM,_xN,_xO,_xP,_xQ,_xR,_xS){var _xT=new T(function(){return B(_tU(function(_xU,_xV){return new F(function(){return _xo(_xJ,_xK,_xL,_xM,_xN,_xO,_xP,_xQ,_xR,_xS,_xU,_xV);});},new T(function(){return B(_to(_xH,_sq,new T(function(){return B(_fG(_xN,_xP,_xQ,_xM,_xO,_xR,_xS));}),new T(function(){return B(_n7(_xN,_xP,_xQ,_xM,_xO,_xR,_xS));}),_xN,_xP,_xQ,_xM,_xO,_xR,_xS));}),_xF,_xJ,_xK,_xL,_xG,_xM,_xN,_xO,_xP,_xQ,_xR,_xS));});return function(_xW,_xX){var _xY=E(_xW),_xZ=_xY[1],_y0=E(_xX),_y1=_y0[1];return B(_uc(_xZ,0))!=B(_uc(_y1,0))?[0]:[1,[1,[0,_xT,_xY[2],_y0[2]],new T(function(){return B(_xi(function(_ra,_py){return [0,_xT,_ra,_py];},_xZ,_y1));})]];};},_y2=new T(function(){return B(_tA("w_sCjd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  f{tv aBTi} [tv]"));}),_y3=new T(function(){return B(_tA("w_sCjh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc r43}\n                  quant{tv aBTh} [tv]"));}),_y4=function(_y5,_y6,_y7,_y8,_y9,_ya,_yb,_yc,_yd,_ye){var _yf=new T(function(){return B(_sU(new T(function(){return B(_xI(_y5,_y6,_y7,_y8,_y9,_ya,_yb,_yc,_yd,_ye));}),new T(function(){return B(_sF(_xH,_sq,new T(function(){return B(_o4(new T(function(){return B(_fG(_y9,_yb,_yc,_y8,_ya,_yd,_ye));})));}),new T(function(){return B(_se(new T(function(){return B(_n7(_y9,_yb,_yc,_y8,_ya,_yd,_ye));})));}),_y9,_yb,_yc,_y8,_ya,_yd,_ye));}),_y2,_y5,_y6,_y7,_y3,_y8,_y9,_ya,_yb,_yc,_yd,_ye));});return function(_yg,_yh){var _yi=E(_yg),_yj=_yi[1],_yk=E(_yh),_yl=_yk[1];return B(_uc(_yj,0))!=B(_uc(_yl,0))?[0]:[1,[1,[0,_yf,_yi[2],_yk[2]],new T(function(){return B(_xi(function(_ra,_py){return [0,_yf,_ra,_py];},_yj,_yl));})]];};},_ym=function(_yn,_yo){while(1){var _yp=E(_yo);if(!_yp[0]){return false;}else{var _yq=E(_yp[1]);if(!B(A(_pz,[_yq[1],_yn,_yq[2]]))){_yo=_yp[2];continue;}else{return true;}}}},_yr=[1,_9],_ys=function(_yt,_yu,_yv,_yw,_yx,_yy,_yz,_yA,_yB,_yC,_yD){var _yE=E(_yw);return !B(A(_yE[1],[new T(function(){return B(A(_yB,[_yC]));}),_yD]))?!B(_ym(_yC,B(A(_yy,[_yD]))))?[1,[1,[0,[0,_yt,[0,_yu,_yv,_yE,_yx,_yy,_yz],_yA,_yB],_yC,_yD],_9]]:[0,[1,_,[0,_yt,[0,_yu,_yv,_yE,_yx,_yy,_yz],_yA,_yB],[3,_yv,_yx,_yC,_yD]]]:E(_yr);},_yF=function(_yG){return new F(function(){return _3r("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(55,15)-(57,42)|case");});},_yH=new T(function(){return B(_yF(_));}),_yI=new T(function(){return B(unCStr(": empty list"));}),_yJ=new T(function(){return B(unCStr("Prelude."));}),_yK=function(_yL){return new F(function(){return err(B(_e(_yJ,new T(function(){return B(_e(_yL,_yI));},1))));});},_yM=new T(function(){return B(unCStr("head"));}),_yN=new T(function(){return B(_yK(_yM));}),_yO=function(_yP){return E(E(_yP)[2]);},_yQ=function(_yR,_yS){while(1){var _yT=E(_yR);if(!_yT){return E(_yS);}else{var _yU=E(_yS);if(!_yU[0]){return [0];}else{_yR=_yT-1|0;_yS=_yU[2];continue;}}}},_yV=function(_yW,_yX){var _yY=E(_yW)[1];return _yY>=0?B(_yQ(_yY,_yX)):E(_yX);},_yZ=function(_z0){return new F(function(){return _3r("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:97:31-64|function conc");});},_z1=new T(function(){return B(_yZ(_));}),_z2=function(_z3){var _z4=E(_z3);switch(_z4[0]){case 3:return [2,_,_z4];case 4:return [4,_,_z4,_V];case 5:return [6,_,_z4,_V,_V];case 6:return [8,_,_z4,_S];case 7:return [10,_,_z4,_S,_S];default:return E(_v9);}},_z5=function(_z6){var _z7=E(_z6);if(!_z7[0]){return [0];}else{var _z8=E(_z7[1]);if(!_z8[0]){return [0];}else{return new F(function(){return _e(_z8[1],new T(function(){return B(_z5(_z7[2]));},1));});}}},_z9=function(_za){var _zb=E(_za);return [0,[1,[1,new T(function(){return B(_z5(_zb[1]));})],_9],_zb[2]];},_zc=function(_zd,_ze,_zf){return !B(_6X(_zd,_ze,_zf))?E(_zf):[1,_ze,new T(function(){return B(_kp(function(_zg){return !B(A(_6V,[_zd,_zg,_ze]))?true:false;},_zf));})];},_zh=function(_zi,_zj,_zk,_zl,_zm,_zn,_zo){return function(_zp,_zq){var _zr=E(_zp);if(!_zr[0]){return new F(function(){return _z9(_zq);});}else{var _zs=E(_zq);return [0,[1,[1,new T(function(){return B(_zc(new T(function(){return B(_uo(function(_zt,_zu){return new F(function(){return _eL(_zo,_zn,_zm,_zk,_zl,_zi,_zj,_zt);});}));}),_zr[1],B(_z5(_zs[1]))));})],_9],_zs[2]];}};},_zv=new T(function(){return B(_wV(_o6));}),_zw=function(_zx){return E(E(_zx)[1]);},_zy=function(_zz,_zA){var _zB=E(_zz);if(!_zB){return [0];}else{var _zC=E(_zA);return _zC[0]==0?[0]:[1,_zC[1],new T(function(){return B(_zy(_zB-1|0,_zC[2]));})];}},_zD=function(_zE,_zF){return _zE<0?[0]:B(_zy(_zE,_zF));},_zG=function(_zH,_zI){var _zJ=E(_zH)[1];return _zJ>0?B(_zD(_zJ,_zI)):[0];},_zK=function(_zL,_zM){return [1,_,_zL,_zM];},_zN=function(_zO){return E(E(_zO)[2]);},_zP=function(_zQ){return E(E(_zQ)[4]);},_zR=function(_zS,_zT,_zU){var _zV=E(_zS),_zW=E(_zV[2]);return new F(function(){return _ys(_zV[1],_zW[1],_zW[2],_zW[3],_zW[4],_zW[5],_zW[6],_zV[3],_zV[4],_zT,_zU);});},_zX=function(_zY,_zZ,_A0,_A1,_A2,_A3){var _A4=B(A(_A0,[_A2,_A3]));if(!_A4[0]){var _A5=B(A(_A0,[_A3,_A2]));if(!_A5[0]){var _A6=B(A(_zY,[_A2,_A3]));if(!_A6[0]){return [0,[0,new T(function(){return B(_zP(_zZ));}),_A2,_A3]];}else{var _A7=B(_A8([0,_zY,_zZ,_A0,_A1],_A6[1]));return _A7[0]==0?[0,[2,new T(function(){return B(_zP(_zZ));}),_A7[1],_A2,_A3]]:E(_A7);}}else{var _A9=E(_A5[1]);return new F(function(){return _zR(_A9[1],_A9[2],_A9[3]);});}}else{var _Aa=E(_A4[1]);return new F(function(){return _zR(_Aa[1],_Aa[2],_Aa[3]);});}},_Ab=function(_Ac){return E(E(_Ac)[6]);},_A8=function(_Ad,_Ae){var _Af=E(_Ae);if(!_Af[0]){return E(_yr);}else{var _Ag=E(_Af[1]),_Ah=E(_Ag[1]),_Ai=B(_zX(_Ah[1],_Ah[2],_Ah[3],_Ah[4],_Ag[2],_Ag[3]));if(!_Ai[0]){return [0,[1,_,_Ah,_Ai[1]]];}else{var _Aj=_Ai[1],_Ak=B(_A8(_Ad,B(_f2(function(_Al){var _Am=E(_Al),_An=_Am[1];return [0,_An,new T(function(){return B(A(_Ab,[B(_zN(_An)),_Aj,_Am[2]]));}),new T(function(){return B(A(_Ab,[B(_zN(_An)),_Aj,_Am[3]]));})];},_Af[2]))));if(!_Ak[0]){return [0,new T(function(){return B(_zK(_Ad,_Ak[1]));})];}else{var _Ao=_Ak[1];return [1,new T(function(){var _Ap=function(_Aq){var _Ar=E(_Aq);return _Ar[0]==0?E(_Ao):[1,new T(function(){var _As=E(_Ar[1]),_At=_As[1];return [0,_At,_As[2],new T(function(){return B(A(_Ab,[B(_zN(_At)),_Ao,_As[3]]));})];}),new T(function(){return B(_Ap(_Ar[2]));})];};return B(_Ap(_Aj));})];}}}},_Au=function(_Av,_Aw,_Ax,_Ay,_Az,_AA,_AB,_AC,_AD,_AE,_AF,_AG){var _AH=new T(function(){return B(_yO(_AG));}),_AI=function(_AJ,_AK){return new F(function(){return _eL(_AB,_AA,_Az,_Ax,_Ay,_Av,_Aw,_AJ);});},_AL=new T(function(){return B(_uv(_zv,_sq,new T(function(){return B(_uo(_AI));}),new T(function(){return B(_vz(_AI));}),_AB,_AA,_Az,_Ay,_Ax,_Av,_Aw));}),_AM=function(_AN,_AO){return new F(function(){return _vG(_AF,_AD,_AE,_Ay,_AB,_Ax,_AA,_Az,_Av,_Aw,_AN,_AO);});};return function(_AP,_AQ,_AR){var _AS=new T(function(){return B(A(_AC,[_AR]));});return [0,new T(function(){return B(_xi(function(_AT,_AU){var _AV=B(A(new T(function(){return B(_zh(_Av,_Aw,_Ax,_Ay,_Az,_AA,_AB));}),[new T(function(){var _AW=E(E(_AU)[1]);if(!_AW[0]){var _AX=[0];}else{var _AY=E(_AW[1]),_AX=_AY[0]==0?[0]:[1,new T(function(){var _AZ=E(_AY[1]);return _AZ[0]==0?E(_yN):B(_ow(new T(function(){var _B0=E(B(A(_AH,[_AP]))[2]);if(!_B0[0]){var _B1=E(_z1);}else{var _B2=E(_B0[1]);if(!_B2[0]){var _B3=E(_z1);}else{var _B4=_B2[1];if(!E(_B2[2])[0]){var _B5=B(_uU(_AM,_AL,_B4,_AS));if(!_B5[0]){var _B6=B(_uU(_AM,_AL,_AS,_B4));if(!_B6[0]){var _B7=B(_AM(_B4,_AS));if(!_B7[0]){var _B8=[0];}else{var _B9=B(_A8([0,_AM,_AL,function(_Ba,_Bb){return new F(function(){return _uU(_AM,_AL,_Ba,_Bb);});},_z2],_B7[1])),_B8=_B9[0]==0?[0]:E(_B9[1]);}var _Bc=_B8;}else{var _Bd=E(_B6[1]),_Be=E(_Bd[1]),_Bf=E(_Be[2]),_Bg=B(_ys(_Be[1],_Bf[1],_Bf[2],_Bf[3],_Bf[4],_Bf[5],_Bf[6],_Be[3],_Be[4],_Bd[2],_Bd[3])),_Bc=_Bg[0]==0?[0]:E(_Bg[1]);}var _Bh=_Bc;}else{var _Bi=E(_B5[1]),_Bj=E(_Bi[1]),_Bk=E(_Bj[2]),_Bl=B(_ys(_Bj[1],_Bk[1],_Bk[2],_Bk[3],_Bk[4],_Bk[5],_Bk[6],_Bj[3],_Bj[4],_Bi[2],_Bi[3])),_Bh=_Bl[0]==0?[0]:E(_Bl[1]);}var _Bm=_Bh;}else{var _Bm=E(_z1);}var _B3=_Bm;}var _B1=_B3;}var _Bn=_B1;return _Bn;}),_AZ[1]));})];}var _Bo=_AX;return _Bo;}),_AT])),_Bp=_AV[2],_Bq=E(E(_AU)[1]);if(!_Bq[0]){return E(_yH);}else{var _Br=E(_Bq[1]);if(!_Br[0]){return E(_Bq[2])[0]==0?E(_AV):E(_yH);}else{var _Bs=E(_AV[1]);if(!_Bs[0]){return [0,_9,_Bp];}else{var _Bt=E(_Bs[1]);if(!_Bt[0]){return E(_AV);}else{var _Bu=_Bt[1],_Bv=new T(function(){return [0,B(_uc(_Br[1],0))];});return [0,[1,[1,new T(function(){return B(_zG(_Bv,_Bu));})],[1,[1,new T(function(){return B(_yV(_Bv,_Bu));})],_Bs[2]]],_Bp];}}}}},_AQ,new T(function(){return B(A(new T(function(){return B(_zw(_AG));}),[_AP]));},1)));}),[0,new T(function(){return E(B(A(_AH,[_AP]))[1]);}),[1,[1,_AS,_9]]]];};},_Bw=function(_Bx){var _By=E(_Bx);return _By[0]==0?E(_By[1]):E(_1);},_Bz=function(_BA,_BB){return [0];},_BC=function(_BD){while(1){var _BE=(function(_BF){var _BG=E(_BF);if(!_BG[0]){return [0];}else{var _BH=_BG[2],_BI=E(_BG[1]);if(!_BI[0]){_BD=_BH;return null;}else{return [1,_BI[1],new T(function(){return B(_BC(_BH));})];}}})(_BD);if(_BE!=null){return _BE;}}},_BJ=function(_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT,_BU){var _BV=new T(function(){return B(_Au(_BK,_BL,_BM,_BN,_BO,_BP,_BQ,_BR,_BS,_BT,_BU,_rf));}),_BW=new T(function(){return B(_y4(_BU,_BS,_BT,_BN,_BQ,_BM,_BP,_BO,_BK,_BL));}),_BX=new T(function(){return B(_rM(new T(function(){return B(_se(new T(function(){return B(_n7(_BQ,_BP,_BO,_BN,_BM,_BK,_BL));})));})));}),_BY=[0,_BW,new T(function(){return B(_qY(_zv,_sq,new T(function(){return B(_nO(new T(function(){return B(_o4(new T(function(){return B(_fG(_BQ,_BP,_BO,_BN,_BM,_BK,_BL));})));})));}),_BX,_BQ,_BP,_BO,_BN,_BM,_BK,_BL));}),_Bz,_1];return function(_BZ,_C0,_C1){var _C2=B(_f2(function(_C3){var _C4=new T(function(){return B(A(_BV,[_C3,_C0,_C1]));}),_C5=B(A(_BW,[_C4,_C3]));if(!_C5[0]){return [0,[0,_BX,_C4,_C3]];}else{var _C6=B(_A8(_BY,_C5[1]));return _C6[0]==0?[0,[2,_BX,_C6[1],_C4,_C3]]:[1,_C3];}},E(_BZ)[1])),_C7=B(_BC(_C2));if(!_C7[0]){return [0,new T(function(){return B(_f2(_Bw,_C2));})];}else{var _C8=_C7[1],_C9=new T(function(){return B(A(_BV,[_C8,_C0,_C1]));}),_Ca=B(A(_BW,[_C8,_C9]));if(!_Ca[0]){return [0,[1,[0,_BX,_C8,_C9],_9]];}else{var _Cb=B(_A8(_BY,_Ca[1]));if(!_Cb[0]){return [0,[1,[2,_BX,_Cb[1],_C8,_C9],_9]];}else{var _Cc=_Cb[1];return [1,new T(function(){var _Cd=E(E(_C9)[2]);return [0,new T(function(){return B(_f2(function(_Ce){return new F(function(){return _p3(_Cc,_Ce);});},_Cd[1]));}),new T(function(){return B(_p3(_Cc,_Cd[2]));})];})];}}}};},_Cf=[1,_9],_Cg=[1],_Ch=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Ci=function(_Cj){return new F(function(){return err(_Ch);});},_Ck=new T(function(){return B(_Ci(_));}),_Cl=function(_Cm,_Cn,_Co){var _Cp=E(_Co);if(!_Cp[0]){var _Cq=_Cp[1],_Cr=E(_Cn);if(!_Cr[0]){var _Cs=_Cr[1],_Ct=_Cr[2];if(_Cs<=(imul(3,_Cq)|0)){return [0,(1+_Cs|0)+_Cq|0,E(E(_Cm)),E(_Cr),E(_Cp)];}else{var _Cu=E(_Cr[3]);if(!_Cu[0]){var _Cv=_Cu[1],_Cw=E(_Cr[4]);if(!_Cw[0]){var _Cx=_Cw[1],_Cy=_Cw[2],_Cz=_Cw[3];if(_Cx>=(imul(2,_Cv)|0)){var _CA=function(_CB){var _CC=E(_Cw[4]);return _CC[0]==0?[0,(1+_Cs|0)+_Cq|0,E(_Cy),E([0,(1+_Cv|0)+_CB|0,E(_Ct),E(_Cu),E(_Cz)]),E([0,(1+_Cq|0)+_CC[1]|0,E(E(_Cm)),E(_CC),E(_Cp)])]:[0,(1+_Cs|0)+_Cq|0,E(_Cy),E([0,(1+_Cv|0)+_CB|0,E(_Ct),E(_Cu),E(_Cz)]),E([0,1+_Cq|0,E(E(_Cm)),E(_Cg),E(_Cp)])];},_CD=E(_Cz);return _CD[0]==0?B(_CA(_CD[1])):B(_CA(0));}else{return [0,(1+_Cs|0)+_Cq|0,E(_Ct),E(_Cu),E([0,(1+_Cq|0)+_Cx|0,E(E(_Cm)),E(_Cw),E(_Cp)])];}}else{return E(_Ck);}}else{return E(_Ck);}}}else{return [0,1+_Cq|0,E(E(_Cm)),E(_Cg),E(_Cp)];}}else{var _CE=E(_Cn);if(!_CE[0]){var _CF=_CE[1],_CG=_CE[2],_CH=_CE[4],_CI=E(_CE[3]);if(!_CI[0]){var _CJ=_CI[1],_CK=E(_CH);if(!_CK[0]){var _CL=_CK[1],_CM=_CK[2],_CN=_CK[3];if(_CL>=(imul(2,_CJ)|0)){var _CO=function(_CP){var _CQ=E(_CK[4]);return _CQ[0]==0?[0,1+_CF|0,E(_CM),E([0,(1+_CJ|0)+_CP|0,E(_CG),E(_CI),E(_CN)]),E([0,1+_CQ[1]|0,E(E(_Cm)),E(_CQ),E(_Cg)])]:[0,1+_CF|0,E(_CM),E([0,(1+_CJ|0)+_CP|0,E(_CG),E(_CI),E(_CN)]),E([0,1,E(E(_Cm)),E(_Cg),E(_Cg)])];},_CR=E(_CN);return _CR[0]==0?B(_CO(_CR[1])):B(_CO(0));}else{return [0,1+_CF|0,E(_CG),E(_CI),E([0,1+_CL|0,E(E(_Cm)),E(_CK),E(_Cg)])];}}else{return [0,3,E(_CG),E(_CI),E([0,1,E(E(_Cm)),E(_Cg),E(_Cg)])];}}else{var _CS=E(_CH);return _CS[0]==0?[0,3,E(_CS[2]),E([0,1,E(_CG),E(_Cg),E(_Cg)]),E([0,1,E(E(_Cm)),E(_Cg),E(_Cg)])]:[0,2,E(E(_Cm)),E(_CE),E(_Cg)];}}else{return [0,1,E(E(_Cm)),E(_Cg),E(_Cg)];}}},_CT=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_CU=function(_CV){return new F(function(){return err(_CT);});},_CW=new T(function(){return B(_CU(_));}),_CX=function(_CY,_CZ,_D0){var _D1=E(_CZ);if(!_D1[0]){var _D2=_D1[1],_D3=E(_D0);if(!_D3[0]){var _D4=_D3[1],_D5=_D3[2];if(_D4<=(imul(3,_D2)|0)){return [0,(1+_D2|0)+_D4|0,E(E(_CY)),E(_D1),E(_D3)];}else{var _D6=E(_D3[3]);if(!_D6[0]){var _D7=_D6[1],_D8=_D6[2],_D9=_D6[3],_Da=E(_D3[4]);if(!_Da[0]){var _Db=_Da[1];if(_D7>=(imul(2,_Db)|0)){var _Dc=function(_Dd){var _De=E(_CY),_Df=E(_D6[4]);return _Df[0]==0?[0,(1+_D2|0)+_D4|0,E(_D8),E([0,(1+_D2|0)+_Dd|0,E(_De),E(_D1),E(_D9)]),E([0,(1+_Db|0)+_Df[1]|0,E(_D5),E(_Df),E(_Da)])]:[0,(1+_D2|0)+_D4|0,E(_D8),E([0,(1+_D2|0)+_Dd|0,E(_De),E(_D1),E(_D9)]),E([0,1+_Db|0,E(_D5),E(_Cg),E(_Da)])];},_Dg=E(_D9);return _Dg[0]==0?B(_Dc(_Dg[1])):B(_Dc(0));}else{return [0,(1+_D2|0)+_D4|0,E(_D5),E([0,(1+_D2|0)+_D7|0,E(E(_CY)),E(_D1),E(_D6)]),E(_Da)];}}else{return E(_CW);}}else{return E(_CW);}}}else{return [0,1+_D2|0,E(E(_CY)),E(_D1),E(_Cg)];}}else{var _Dh=E(_D0);if(!_Dh[0]){var _Di=_Dh[1],_Dj=_Dh[2],_Dk=_Dh[4],_Dl=E(_Dh[3]);if(!_Dl[0]){var _Dm=_Dl[1],_Dn=_Dl[2],_Do=_Dl[3],_Dp=E(_Dk);if(!_Dp[0]){var _Dq=_Dp[1];if(_Dm>=(imul(2,_Dq)|0)){var _Dr=function(_Ds){var _Dt=E(_CY),_Du=E(_Dl[4]);return _Du[0]==0?[0,1+_Di|0,E(_Dn),E([0,1+_Ds|0,E(_Dt),E(_Cg),E(_Do)]),E([0,(1+_Dq|0)+_Du[1]|0,E(_Dj),E(_Du),E(_Dp)])]:[0,1+_Di|0,E(_Dn),E([0,1+_Ds|0,E(_Dt),E(_Cg),E(_Do)]),E([0,1+_Dq|0,E(_Dj),E(_Cg),E(_Dp)])];},_Dv=E(_Do);return _Dv[0]==0?B(_Dr(_Dv[1])):B(_Dr(0));}else{return [0,1+_Di|0,E(_Dj),E([0,1+_Dm|0,E(E(_CY)),E(_Cg),E(_Dl)]),E(_Dp)];}}else{return [0,3,E(_Dn),E([0,1,E(E(_CY)),E(_Cg),E(_Cg)]),E([0,1,E(_Dj),E(_Cg),E(_Cg)])];}}else{var _Dw=E(_Dk);return _Dw[0]==0?[0,3,E(_Dj),E([0,1,E(E(_CY)),E(_Cg),E(_Cg)]),E(_Dw)]:[0,2,E(E(_CY)),E(_Cg),E(_Dh)];}}else{return [0,1,E(E(_CY)),E(_Cg),E(_Cg)];}}},_Dx=function(_Dy){return [0,1,E(E(_Dy)),E(_Cg),E(_Cg)];},_Dz=function(_DA,_DB){var _DC=E(_DB);if(!_DC[0]){return new F(function(){return _Cl(_DC[2],B(_Dz(_DA,_DC[3])),_DC[4]);});}else{return new F(function(){return _Dx(_DA);});}},_DD=function(_DE,_DF){var _DG=E(_DF);if(!_DG[0]){return new F(function(){return _CX(_DG[2],_DG[3],B(_DD(_DE,_DG[4])));});}else{return new F(function(){return _Dx(_DE);});}},_DH=function(_DI,_DJ,_DK,_DL,_DM){return new F(function(){return _CX(_DK,_DL,B(_DD(_DI,_DM)));});},_DN=function(_DO,_DP,_DQ,_DR,_DS){return new F(function(){return _Cl(_DQ,B(_Dz(_DO,_DR)),_DS);});},_DT=function(_DU,_DV,_DW,_DX,_DY,_DZ){var _E0=E(_DV);if(!_E0[0]){var _E1=_E0[1],_E2=_E0[2],_E3=_E0[3],_E4=_E0[4];if((imul(3,_E1)|0)>=_DW){if((imul(3,_DW)|0)>=_E1){return [0,(_E1+_DW|0)+1|0,E(E(_DU)),E(_E0),E([0,_DW,E(_DX),E(_DY),E(_DZ)])];}else{return new F(function(){return _CX(_E2,_E3,B(_DT(_DU,_E4,_DW,_DX,_DY,_DZ)));});}}else{return new F(function(){return _Cl(_DX,B(_E5(_DU,_E1,_E2,_E3,_E4,_DY)),_DZ);});}}else{return new F(function(){return _DN(_DU,_DW,_DX,_DY,_DZ);});}},_E5=function(_E6,_E7,_E8,_E9,_Ea,_Eb){var _Ec=E(_Eb);if(!_Ec[0]){var _Ed=_Ec[1],_Ee=_Ec[2],_Ef=_Ec[3],_Eg=_Ec[4];if((imul(3,_E7)|0)>=_Ed){if((imul(3,_Ed)|0)>=_E7){return [0,(_E7+_Ed|0)+1|0,E(E(_E6)),E([0,_E7,E(_E8),E(_E9),E(_Ea)]),E(_Ec)];}else{return new F(function(){return _CX(_E8,_E9,B(_DT(_E6,_Ea,_Ed,_Ee,_Ef,_Eg)));});}}else{return new F(function(){return _Cl(_Ee,B(_E5(_E6,_E7,_E8,_E9,_Ea,_Ef)),_Eg);});}}else{return new F(function(){return _DH(_E6,_E7,_E8,_E9,_Ea);});}},_Eh=function(_Ei,_Ej,_Ek){var _El=E(_Ej);if(!_El[0]){var _Em=_El[1],_En=_El[2],_Eo=_El[3],_Ep=_El[4],_Eq=E(_Ek);if(!_Eq[0]){var _Er=_Eq[1],_Es=_Eq[2],_Et=_Eq[3],_Eu=_Eq[4];if((imul(3,_Em)|0)>=_Er){if((imul(3,_Er)|0)>=_Em){return [0,(_Em+_Er|0)+1|0,E(E(_Ei)),E(_El),E(_Eq)];}else{return new F(function(){return _CX(_En,_Eo,B(_DT(_Ei,_Ep,_Er,_Es,_Et,_Eu)));});}}else{return new F(function(){return _Cl(_Es,B(_E5(_Ei,_Em,_En,_Eo,_Ep,_Et)),_Eu);});}}else{return new F(function(){return _DH(_Ei,_Em,_En,_Eo,_Ep);});}}else{return new F(function(){return _Dz(_Ei,_Ek);});}},_Ev=function(_Ew,_Ex,_Ey,_Ez){var _EA=E(_Ez);if(!_EA[0]){var _EB=new T(function(){var _EC=B(_Ev(_EA[1],_EA[2],_EA[3],_EA[4]));return [0,_EC[1],_EC[2]];});return [0,new T(function(){return E(E(_EB)[1]);}),new T(function(){return B(_Cl(_Ex,_Ey,E(_EB)[2]));})];}else{return [0,_Ex,_Ey];}},_ED=function(_EE,_EF,_EG,_EH){var _EI=E(_EG);if(!_EI[0]){var _EJ=new T(function(){var _EK=B(_ED(_EI[1],_EI[2],_EI[3],_EI[4]));return [0,_EK[1],_EK[2]];});return [0,new T(function(){return E(E(_EJ)[1]);}),new T(function(){return B(_CX(_EF,E(_EJ)[2],_EH));})];}else{return [0,_EF,_EH];}},_EL=function(_EM,_EN){var _EO=E(_EM);if(!_EO[0]){var _EP=_EO[1],_EQ=E(_EN);if(!_EQ[0]){var _ER=_EQ[1];if(_EP<=_ER){var _ES=B(_ED(_ER,_EQ[2],_EQ[3],_EQ[4]));return new F(function(){return _Cl(_ES[1],_EO,_ES[2]);});}else{var _ET=B(_Ev(_EP,_EO[2],_EO[3],_EO[4]));return new F(function(){return _CX(_ET[1],_ET[2],_EQ);});}}else{return E(_EO);}}else{return E(_EN);}},_EU=function(_EV,_EW,_EX,_EY,_EZ){var _F0=E(_EV);if(!_F0[0]){var _F1=_F0[1],_F2=_F0[2],_F3=_F0[3],_F4=_F0[4];if((imul(3,_F1)|0)>=_EW){if((imul(3,_EW)|0)>=_F1){return new F(function(){return _EL(_F0,[0,_EW,E(_EX),E(_EY),E(_EZ)]);});}else{return new F(function(){return _CX(_F2,_F3,B(_EU(_F4,_EW,_EX,_EY,_EZ)));});}}else{return new F(function(){return _Cl(_EX,B(_F5(_F1,_F2,_F3,_F4,_EY)),_EZ);});}}else{return [0,_EW,E(_EX),E(_EY),E(_EZ)];}},_F5=function(_F6,_F7,_F8,_F9,_Fa){var _Fb=E(_Fa);if(!_Fb[0]){var _Fc=_Fb[1],_Fd=_Fb[2],_Fe=_Fb[3],_Ff=_Fb[4];if((imul(3,_F6)|0)>=_Fc){if((imul(3,_Fc)|0)>=_F6){return new F(function(){return _EL([0,_F6,E(_F7),E(_F8),E(_F9)],_Fb);});}else{return new F(function(){return _CX(_F7,_F8,B(_EU(_F9,_Fc,_Fd,_Fe,_Ff)));});}}else{return new F(function(){return _Cl(_Fd,B(_F5(_F6,_F7,_F8,_F9,_Fe)),_Ff);});}}else{return [0,_F6,E(_F7),E(_F8),E(_F9)];}},_Fg=function(_Fh,_Fi){var _Fj=E(_Fh);if(!_Fj[0]){var _Fk=_Fj[1],_Fl=_Fj[2],_Fm=_Fj[3],_Fn=_Fj[4],_Fo=E(_Fi);if(!_Fo[0]){var _Fp=_Fo[1],_Fq=_Fo[2],_Fr=_Fo[3],_Fs=_Fo[4];if((imul(3,_Fk)|0)>=_Fp){if((imul(3,_Fp)|0)>=_Fk){return new F(function(){return _EL(_Fj,_Fo);});}else{return new F(function(){return _CX(_Fl,_Fm,B(_EU(_Fn,_Fp,_Fq,_Fr,_Fs)));});}}else{return new F(function(){return _Cl(_Fq,B(_F5(_Fk,_Fl,_Fm,_Fn,_Fr)),_Fs);});}}else{return E(_Fj);}}else{return E(_Fi);}},_Ft=function(_Fu,_Fv){var _Fw=E(_Fv);if(!_Fw[0]){var _Fx=_Fw[2],_Fy=_Fw[3],_Fz=_Fw[4];if(!B(A(_Fu,[_Fx]))){return new F(function(){return _Fg(B(_Ft(_Fu,_Fy)),B(_Ft(_Fu,_Fz)));});}else{return new F(function(){return _Eh(_Fx,B(_Ft(_Fu,_Fy)),B(_Ft(_Fu,_Fz)));});}}else{return [1];}},_FA=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_FB=new T(function(){return B(err(_FA));}),_FC=function(_FD,_FE,_FF,_FG){while(1){var _FH=E(_FF);if(!_FH[0]){_FD=_FH[1];_FE=_FH[2];_FF=_FH[3];_FG=_FH[4];continue;}else{return E(_FE);}}},_FI=function(_FJ,_FK){var _FL=B(_Ft(function(_FM){return new F(function(){return _4b(E(_FM)[2],_FJ);});},_FK));if(!_FL[0]){var _FN=E(_FL[3]);return _FN[0]==0?B(_FC(_FN[1],_FN[2],_FN[3],_FN[4])):E(_FL[2]);}else{return E(_FB);}},_FO=function(_FP,_FQ,_FR,_FS,_FT,_FU,_FV,_FW,_FX,_FY,_FZ,_G0,_G1,_G2){var _G3=function(_G4,_G5,_G6){var _G7=E(_G6);if(!_G7[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_FW,[_G5]));}),_9]],_9],[1,[1,new T(function(){return B(A(_FW,[_G5]));}),_9]]]];}else{var _G8=function(_G9){var _Ga=E(_G9);if(!_Ga[0]){return E(_Cf);}else{var _Gb=E(_Ga[1]),_Gc=B(_G3(_G4,_Gb[1],_Gb[2]));if(!_Gc[0]){return [0,_Gc[1]];}else{var _Gd=B(_G8(_Ga[2]));return _Gd[0]==0?E(_Gd):[1,[1,_Gc[1],_Gd[1]]];}}},_Ge=B(_G8(_G7[2]));return _Ge[0]==0?[0,_Ge[1]]:B(A(new T(function(){return B(_BJ(_FP,_FQ,_FR,_FS,_FT,_FU,_FV,_FW,_FX,_FY,_FZ));}),[new T(function(){return B(_FI(_G7[1],_G4));}),_Ge[1],_G5]));}};return new F(function(){return _G3(_G0,_G1,_G2);});},_Gf=function(_Gg,_Gh){while(1){var _Gi=E(_Gh);if(!_Gi[0]){return true;}else{if(!B(A(_Gg,[_Gi[1]]))){return false;}else{_Gh=_Gi[2];continue;}}}},_Gj=[3],_Gk=function(_Gl){var _Gm=E(_Gl);switch(_Gm[0]){case 1:return [0,_Gm[1]];case 3:return [3];default:return E(_Gm);}},_Gn=function(_Go,_Gp){return [0,_Gj,new T(function(){var _Gq=B(_uc(_Gp,0))-E(_Go)[1]|0,_Gr=new T(function(){return _Gq>=0?B(_yQ(_Gq,_Gp)):E(_Gp);});if(_Gq>0){var _Gs=function(_Gt,_Gu){var _Gv=E(_Gt);if(!_Gv[0]){return E(_Gr);}else{var _Gw=_Gv[1];return _Gu>1?[1,new T(function(){return B(_Gk(_Gw));}),new T(function(){return B(_Gs(_Gv[2],_Gu-1|0));})]:[1,new T(function(){return B(_Gk(_Gw));}),_Gr];}},_Gx=B(_Gs(_Gp,_Gq));}else{var _Gx=E(_Gr);}var _Gy=_Gx,_Gz=_Gy,_GA=_Gz,_GB=_GA;return _GB;})];},_GC=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_GD=[2,_GC],_GE=new T(function(){return B(unCStr("wrong number of lines cited"));}),_GF=[2,_GE],_GG=new T(function(){return B(unCStr(" is closed, and can\'t be used"));}),_GH=function(_GI){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_GI)[1],_9)),_GG));}));});},_GJ=new T(function(){return B(unCStr(" has nothing on it"));}),_GK=function(_GL){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_GL)[1],_9)),_GJ));}));});},_GM=new T(function(){return B(unCStr(" depends on something not-well-formed, and can\'t be used"));}),_GN=function(_GO){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_GO)[1],_9)),_GM));}));});},_GP=function(_GQ,_GR,_GS,_GT,_GU,_GV,_GW){var _GX=E(_GQ);if(_GX[0]==1){var _GY=E(_GR);return _GY[0]==1?[0,[1,[0,_GS,[1,_GV,[1,_GX[1],[1,_GY[1],_9]]]]],_GW]:[0,[2,new T(function(){switch(E(_GY)[0]){case 0:var _GZ=B(_GH(_GU));break;case 2:var _GZ=B(_GN(_GU));break;default:var _GZ=B(_GK(_GU));}return _GZ;})],_GW];}else{var _H0=E(_GR);return _H0[0]==1?[0,[2,new T(function(){switch(E(_GX)[0]){case 0:var _H1=B(_GH(_GT));break;case 2:var _H1=B(_GN(_GT));break;default:var _H1=B(_GK(_GT));}return _H1;})],_GW]:[0,[2,new T(function(){var _H2=new T(function(){return B(unAppCStr(" and ",new T(function(){switch(E(_H0)[0]){case 0:var _H3=B(_GH(_GU));break;case 2:var _H3=B(_GN(_GU));break;default:var _H3=B(_GK(_GU));}return _H3;})));},1);switch(E(_GX)[0]){case 0:var _H4=B(_e(B(_GH(_GT)),_H2));break;case 2:var _H4=B(_e(B(_GN(_GT)),_H2));break;default:var _H4=B(_e(B(_GK(_GT)),_H2));}return _H4;})],_GW];}},_H5=function(_H6,_H7){while(1){var _H8=E(_H6);if(!_H8[0]){return E(_H7);}else{_H6=_H8[2];var _H9=[1,_H8[1],_H7];_H7=_H9;continue;}}},_Ha=function(_Hb){return new F(function(){return _H5(_Hb,_9);});},_Hc=function(_Hd,_He){return _Hd<=B(_uc(_He,0))?[1,new T(function(){var _Hf=_Hd-1|0;if(_Hf>=0){var _Hg=B(_1s(B(_Ha(_He)),_Hf));}else{var _Hg=E(_1p);}var _Hh=_Hg,_Hi=_Hh;return _Hi;})]:[0];},_Hj=new T(function(){return B(unCStr(" is unavailable"));}),_Hk=new T(function(){return B(unCStr(" are unavailable"));}),_Hl=function(_Hm,_Hn,_Ho,_Hp,_Hq,_Hr,_Hs){var _Ht=B(_Hu(_Hm,_Hn,[1,_Gj,_Hs])),_Hv=B(_Hc(_Hp,_Ht));if(!_Hv[0]){return B(_Hc(_Hq,_Ht))[0]==0?B(_Hu(_Hm,_Hn,[1,[2,new T(function(){return B(unAppCStr("The lines ",new T(function(){return B(_e(B(_F(0,_Hp,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_Hq,_9)),_Hk));})));},1)));})));})],_Hs])):B(_Hu(_Hm,_Hn,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_Hp,_9)),_Hj));})));})],_Hs]));}else{var _Hw=B(_Hc(_Hq,_Ht));return _Hw[0]==0?B(_Hu(_Hm,_Hn,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_Hq,_9)),_Hj));})));})],_Hs])):B(_Hu(_Hm,_Hn,new T(function(){var _Hx=B(_GP(_Hv[1],_Hw[1],_Ho,[0,_Hp],[0,_Hq],_Hr,_Hs));return [1,_Hx[1],_Hx[2]];})));}},_Hy=function(_Hz,_HA,_HB,_HC,_HD,_HE,_HF){return new F(function(){return _Hl(_Hz,_HA,_HB,E(_HC)[1],E(_HD)[1],_HE,_HF);});},_HG=function(_HH,_HI,_HJ,_HK,_HL,_HM){var _HN=E(_HL);if(!_HN[0]){return new F(function(){return _Hu(_HH,_HI,[1,_GF,_HM]);});}else{var _HO=E(_HN[2]);return _HO[0]==0?B(_Hu(_HH,_HI,[1,_GF,_HM])):E(_HO[2])[0]==0?B(_Hy(_HH,_HI,_HJ,_HN[1],_HO[1],_HK,_HM)):B(_Hu(_HH,_HI,[1,_GF,_HM]));}},_HP=new T(function(){return B(unCStr("Open Subproof"));}),_HQ=[2,_HP],_HR=new T(function(){return B(unCStr("Impossible Error 2"));}),_HS=[2,_HR],_HT=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_HU=[2,_HT],_HV=new T(function(){return B(unCStr("SHOW"));}),_HW=function(_HX,_HY,_HZ,_I0,_I1,_I2){var _I3=new T(function(){return B(_Hu(_HX,_HY,[1,_Gj,_I2]));});if(_I0<=B(_uc(_I3,0))){var _I4=_I0-1|0;if(_I4>=0){var _I5=B(_1s(B(_Ha(_I3)),_I4));switch(_I5[0]){case 0:return new F(function(){return _Hu(_HX,_HY,[1,[2,new T(function(){return B(_GH([0,_I0]));})],_I2]);});break;case 1:return new F(function(){return _Hu(_HX,_HY,[1,[1,[0,_HZ,[1,_I1,[1,_I5[1],_9]]]],_I2]);});break;case 2:return new F(function(){return _Hu(_HX,_HY,[1,[2,new T(function(){return B(_GN([0,_I0]));})],_I2]);});break;default:return new F(function(){return _Hu(_HX,_HY,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_I0,_9)),_GJ));})));})],_I2]);});}}else{return E(_1p);}}else{return new F(function(){return _Hu(_HX,_HY,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_I0,_9)),_Hj));})));})],_I2]);});}},_I6=function(_I7,_I8,_I9,_Ia,_Ib,_Ic){return new F(function(){return _HW(_I7,_I8,_I9,E(_Ia)[1],_Ib,_Ic);});},_Id=function(_Ie,_If,_Ig,_Ih,_Ii,_Ij){var _Ik=E(_Ii);return _Ik[0]==0?B(_Hu(_Ie,_If,[1,_GF,_Ij])):E(_Ik[2])[0]==0?B(_I6(_Ie,_If,_Ig,_Ik[1],_Ih,_Ij)):B(_Hu(_Ie,_If,[1,_GF,_Ij]));},_Il=function(_Im,_In,_Io,_Ip,_Iq,_Ir){if(!B(_4b(_In,_HV))){var _Is=B(A(_Ip,[_In]));if(!_Is[0]){return [0,_GD,_Ir];}else{var _It=E(_Is[1]);if(!_It[0]){return [0,_HU,_Ir];}else{switch(E(E(_It[1])[1])){case 1:return new F(function(){return _Gn(new T(function(){return [0,B(_uc(_Ir,0))+1|0];},1),new T(function(){return B(_Id(_Iq,_Ip,_Im,_In,_Io,_Ir));}));});break;case 2:return new F(function(){return _Gn(new T(function(){return [0,B(_uc(_Ir,0))+1|0];},1),new T(function(){return B(_HG(_Iq,_Ip,_Im,_In,_Io,_Ir));}));});break;default:return [0,_HS,_Ir];}}}}else{return new F(function(){return _Gn(new T(function(){return [0,B(_uc(_Ir,0))+1|0];},1),new T(function(){return B(_Hu(_Iq,_Ip,[1,_HQ,_Ir]));}));});}},_Iu=[0],_Iv=new T(function(){return B(unCStr("PR"));}),_Iw=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_Ix=[2,_Iw],_Iy=new T(function(){return B(unCStr("Impossible Error 1"));}),_Iz=[2,_Iy],_IA=function(_IB,_IC,_ID,_IE,_IF){var _IG=B(_Hc(_IC,_IF));if(!_IG[0]){return B(_Hc(_ID,_IF))[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the lines ",new T(function(){return B(_e(B(_F(0,_IC,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_ID,_9)),_Hk));})));},1)));})));})],_IF]:[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_IC,_9)),_Hj));})));})],_IF];}else{var _IH=B(_Hc(_ID,_IF));return _IH[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_ID,_9)),_Hj));})));})],_IF]:B(_GP(_IG[1],_IH[1],_IB,[0,_IC],[0,_ID],_IE,_IF));}},_II=new T(function(){return B(unCStr("wrong number of premises"));}),_IJ=[2,_II],_IK=function(_IL,_IM,_IN,_IO){var _IP=E(_IN);if(!_IP[0]){return [1,_IJ,_IO];}else{var _IQ=E(_IP[2]);if(!_IQ[0]){return [1,_IJ,_IO];}else{if(!E(_IQ[2])[0]){var _IR=B(_IA(_IL,E(_IP[1])[1],E(_IQ[1])[1],_IM,_IO));return [1,_IR[1],_IR[2]];}else{return [1,_IJ,_IO];}}}},_IS=new T(function(){return B(unCStr("has nothing on it"));}),_IT=new T(function(){return B(unCStr("is unavailable"));}),_IU=function(_IV,_IW,_IX,_IY){var _IZ=B(_Hc(_IW,_IY));if(!_IZ[0]){return [0,[2,new T(function(){return B(unAppCStr("line",new T(function(){return B(_e(B(_F(0,_IW,_9)),_IT));})));})],_IY];}else{var _J0=E(_IZ[1]);switch(_J0[0]){case 0:return [0,[2,new T(function(){return B(_GH([0,_IW]));})],_IY];case 1:return [0,[1,[0,_IV,[1,_IX,[1,_J0[1],_9]]]],_IY];case 2:return [0,[2,new T(function(){return B(_GN([0,_IW]));})],_IY];default:return [0,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_IW,_9)),_IS));})));})],_IY];}}},_J1=function(_J2,_J3,_J4,_J5){var _J6=B(_IU(_J2,E(_J3)[1],_J4,_J5));return [1,_J6[1],_J6[2]];},_J7=function(_J8,_J9,_Ja,_Jb){var _Jc=E(_Ja);return _Jc[0]==0?[1,_IJ,_Jb]:E(_Jc[2])[0]==0?B(_J1(_J8,_Jc[1],_J9,_Jb)):[1,_IJ,_Jb];},_Jd=function(_Je,_Jf,_Jg,_Jh,_Ji){var _Jj=function(_Jk){var _Jl=B(A(_Jh,[_Jf]));if(!_Jl[0]){return [1,_GD,_Ji];}else{var _Jm=E(_Jl[1]);if(!_Jm[0]){switch(E(E(_Jm[1])[1])){case 1:return new F(function(){return _J7(_Je,_Jf,_Jg,_Ji);});break;case 2:return new F(function(){return _IK(_Je,_Jf,_Jg,_Ji);});break;default:return [1,_Iz,_Ji];}}else{return [1,_Ix,_Ji];}}};return !B(_4b(_Jf,_Iv))?B(_Jj(_)):E(_Jg)[0]==0?[1,[1,[0,_Je,_Iu]],_Ji]:B(_Jj(_));},_Jn=function(_Jo,_Jp,_Jq){var _Jr=E(_Jo);return new F(function(){return _Jd(_Jr[1],_Jr[2],_Jr[3],_Jp,_Jq);});},_Js=new T(function(){return B(unCStr("shouldn\'t happen"));}),_Jt=[2,_Js],_Ju=new T(function(){return B(unCStr("incomplete line"));}),_Jv=[2,_Ju],_Jw=function(_Jx,_Jy,_Jz,_JA){var _JB=E(_Jx);if(!_JB[0]){return E(_Jy)[0]==0?[1,_Jv,_JA]:[1,_Jt,_JA];}else{var _JC=_JB[1],_JD=E(_Jy);if(!_JD[0]){return new F(function(){return _Jn(_JC,_Jz,_JA);});}else{var _JE=E(_JC),_JF=B(_Il(_JE[1],_JE[2],_JE[3],_Jz,_JD,_JA));return [1,_JF[1],_JF[2]];}}},_JG=function(_JH,_JI,_JJ){var _JK=E(_JH);return new F(function(){return _Jw(_JK[1],_JK[2],_JI,_JJ);});},_Hu=function(_JL,_JM,_JN){return new F(function(){return (function(_JO,_JP){while(1){var _JQ=(function(_JR,_JS){var _JT=E(_JS);if(!_JT[0]){return E(_JR);}else{_JO=new T(function(){return B(_JG(_JT[1],_JM,_JR));});_JP=_JT[2];return null;}})(_JO,_JP);if(_JQ!=null){return _JQ;}}})(_JN,_JL);});},_JU=[0,666],_JV=[0,_,_JU],_JW=[1,_JV],_JX=[0,_JW,_Iu],_JY=function(_JZ,_K0,_K1,_K2,_K3,_K4,_K5,_K6,_K7,_K8,_K9,_Ka,_Kb,_Kc){var _Kd=B(_Hu(_Ka,_Kb,_9)),_Ke=function(_Kf,_Kg,_Kh){return B(_FO(_JZ,_K0,_K1,_K2,_K3,_K4,_K5,_Kf,_K7,_K8,_K9,_Kc,_Kg,_Kh))[0]==0?false:true;};return !B(_Gf(function(_Ki){var _Kj=E(_Ki);switch(_Kj[0]){case 0:var _Kk=E(_Kj[1]);return new F(function(){return _Ke(_K6,_Kk[1],_Kk[2]);});break;case 1:var _Kl=E(_Kj[1]);return new F(function(){return _Ke(_K6,_Kl[1],_Kl[2]);});break;case 2:return false;default:return true;}},_Kd))?[0,_Kd]:[1,new T(function(){var _Km=B(_uc(_Ka,0))-1|0;if(_Km>=0){var _Kn=B(_1s(B(_Ha(_Kd)),_Km)),_Ko=_Kn[0]==1?E(_Kn[1]):E(_JX);}else{var _Ko=E(_1p);}var _Kp=_Ko,_Kq=_Kp,_Kr=_Kq;return _Kr;})];},_Ks=function(_Kt,_Ku,_Kv,_Kw,_Kx,_Ky,_Kz,_KA,_KB,_KC,_KD,_KE,_KF,_KG){var _KH=B(_JY(_Kt,_Ku,_Kv,_Kw,_Kx,_Ky,_Kz,_KA,_KB,_KC,_KD,_KE,_KF,_KG));return _KH[0]==0?[0,_KH[1]]:[1,new T(function(){var _KI=E(_KH[1]);return B(_FO(_Kt,_Ku,_Kv,_Kw,_Kx,_Ky,_Kz,_KA,_KB,_KC,_KD,_KG,_KI[1],_KI[2]));})];},_KJ=function(_KK,_KL,_){var _KM=E(_KK);if(!_KM[0]){return _KL;}else{var _KN=B(A(_KM[1],[_KL,_])),_KO=_KN,_KP=B(_KJ(_KM[2],_KL,_)),_KQ=_KP;return _KL;}},_KR=function(_KS){return E(E(_KS)[2]);},_KT=new T(function(){return B(unCStr("But that\'s impossible."));}),_KU=new T(function(){return B(unCStr(" = "));}),_KV=new T(function(){return B(unCStr("Cannot construct infinite type "));}),_KW=new T(function(){return B(unCStr("so "));}),_KX=new T(function(){return B(unCStr("class"));}),_KY=new T(function(){return B(unCStr("uniblock"));}),_KZ=new T(function(){return B(unCStr(" with "));}),_L0=new T(function(){return B(unCStr("I need to match "));}),_L1=[0,46],_L2=[1,_L1,_9],_L3=new T(function(){return B(unCStr("br"));}),_L4=function(_L5,_){var _L6=jsCreateElem(toJSStr(E(_L3))),_L7=_L6,_L8=jsAppendChild(_L7,E(_L5)[1]);return [0,_L7];},_L9=new T(function(){return B(unCStr("div"));}),_La=function(_Lb,_Lc,_Ld,_){var _Le=jsCreateElem(toJSStr(E(_L9))),_Lf=_Le,_Lg=jsAppendChild(_Lf,E(_Ld)[1]),_Lh=[0,_Lf],_Li=B(A(_Lb,[_Lc,_Lh,_])),_Lj=_Li;return _Lh;},_Lk=function(_Ll,_Lm,_Ln){while(1){var _Lo=(function(_Lp,_Lq,_Lr){var _Ls=E(_Lr);switch(_Ls[0]){case 0:return function(_Lt,_){var _Lu=B(_id(_L0,_Lt,_)),_Lv=_Lu,_Lw=B(A(new T(function(){return B(A(_Lq,[_Ls[2]]));}),[_Lt,_])),_Lx=_Lw,_Ly=B(_id(_KZ,_Lt,_)),_Lz=_Ly,_LA=B(A(new T(function(){return B(A(_Lq,[_Ls[3]]));}),[_Lt,_])),_LB=_LA,_LC=B(_id(_L2,_Lt,_)),_LD=_LC,_LE=B(_L4(_Lt,_)),_LF=_LE,_LG=B(_id(_KT,_Lt,_)),_LH=_LG;return _Lt;};case 1:var _LI=new T(function(){return B(_zN(_Ls[2]));});_Ll=function(_LJ){return function(_58,_xf){return new F(function(){return _id(new T(function(){return B(A(_ni,[B(_KR(_LI)),_LJ]));}),_58,_xf);});};};_Lm=function(_LK){return function(_58,_xf){return new F(function(){return _id(new T(function(){return B(A(new T(function(){return B(_ni(new T(function(){return B(_zP(_LI));})));}),[_LK]));}),_58,_xf);});};};_Ln=_Ls[3];return null;case 2:return function(_LL,_){var _LM=B(_id(_L0,_LL,_)),_LN=_LM,_LO=B(_La(_j7,new T(function(){return B(A(_Lq,[_Ls[3]]));}),_LL,_)),_LP=_LO,_LQ=B(A(_ij,[_5n,_LP,_KX,_KY,_])),_LR=_LQ,_LS=B(_id(_KZ,_LL,_)),_LT=_LS,_LU=B(_La(_j7,new T(function(){return B(A(_Lq,[_Ls[4]]));}),_LL,_)),_LV=_LU,_LW=B(A(_ij,[_5n,_LV,_KX,_KY,_])),_LX=_LW,_LY=B(_id(_KW,_LL,_)),_LZ=_LY,_M0=B(A(new T(function(){return B(_Lk(_Lp,_Lq,_Ls[2]));}),[_LL,_])),_M1=_M0;return _LL;};default:return function(_M2,_){var _M3=B(_id(_KV,_M2,_)),_M4=_M3,_M5=B(A(new T(function(){return B(A(_Lp,[_Ls[3]]));}),[_M2,_])),_M6=_M5,_M7=B(_id(_KU,_M2,_)),_M8=_M7,_M9=B(A(new T(function(){return B(A(_Lq,[_Ls[4]]));}),[_M2,_])),_Ma=_M9;return _M2;};}})(_Ll,_Lm,_Ln);if(_Lo!=null){return _Lo;}}},_Mb=function(_Mc,_Md,_Me){return function(_Mf,_){var _Mg=B(_KJ(new T(function(){var _Mh=B(_f2(_Mc,_Md));return _Mh[0]==0?[0]:[1,_Mh[1],new T(function(){return B(_f6(_L4,_Mh[2]));})];}),_Mf,_)),_Mi=_Mg,_Mj=B(_L4(_Mf,_)),_Mk=_Mj,_Ml=B(_id(_ng,_Mf,_)),_Mm=_Ml,_Mn=B(A(new T(function(){return B(A(_Mc,[_Me]));}),[_Mf,_])),_Mo=_Mn;return _Mf;};},_Mp=new T(function(){return B(unCStr(" \u22a2 "));}),_Mq=new T(function(){return B(unCStr(", "));}),_Mr=function(_Ms,_){return new F(function(){return _id(_Mq,_Ms,_);});},_Mt=function(_Mu,_Mv,_Mw){return function(_Mx,_){var _My=B(_KJ(new T(function(){var _Mz=B(_f2(_Mu,_Mv));return _Mz[0]==0?[0]:[1,_Mz[1],new T(function(){return B(_f6(_Mr,_Mz[2]));})];}),_Mx,_)),_MA=_My,_MB=B(_id(_Mp,_Mx,_)),_MC=_MB,_MD=B(A(new T(function(){return B(A(_Mu,[_Mw]));}),[_Mx,_])),_ME=_MD;return _Mx;};},_MF=function(_MG){return function(_58,_xf){return new F(function(){return _id(new T(function(){return B(_ex(_MG));}),_58,_xf);});};},_MH=new T(function(){return B(unCStr("errormsg"));}),_MI=function(_Ms,_){return new F(function(){return _La(_id,_9,_Ms,_);});},_MJ=function(_MK,_){return _MK;},_ML=new T(function(){return B(unCStr("hr"));}),_MM=function(_MN,_){var _MO=jsCreateElem(toJSStr(E(_ML))),_MP=_MO,_MQ=jsAppendChild(_MP,E(_MN)[1]);return [0,_MP];},_MR=[0,10006],_MS=[1,_MR,_9],_MT=[0,10003],_MU=[1,_MT,_9],_MV=function(_MW,_MX,_MY,_MZ,_N0,_N1,_N2,_N3,_N4,_N5,_N6){return function(_N7,_N8){return function(_58,_xf){return new F(function(){return _La(_j7,new T(function(){var _N9=function(_Na,_Nb){var _Nc=B(_FO(_MW,_MX,_MY,_MZ,_N0,_N1,_N2,_N3,_N4,_N5,_N6,new T(function(){return E(E(_N7)[2]);}),_Na,_Nb));return _Nc[0]==0?function(_58,_xf){return new F(function(){return _La(_j7,function(_Nd,_){var _Ne=B(_La(_id,_MS,_Nd,_)),_Nf=_Ne,_Ng=B(_La(_j7,function(_Nh,_){return new F(function(){return _KJ(new T(function(){var _Ni=B(_f2(function(_Nj){return function(_58,_xf){return new F(function(){return _La(_j7,new T(function(){return B(_Lk(_MF,function(_Nk){var _Nl=E(_Nk);return new F(function(){return _Mb(function(_Nm){var _Nn=E(_Nm);return new F(function(){return _Mt(function(_No){return function(_58,_xf){return new F(function(){return _id(new T(function(){return B(_fa(_N2,_N1,_N0,_MZ,_MY,_MW,_MX,_No));}),_58,_xf);});};},_Nn[1],_Nn[2]);});},_Nl[1],_Nl[2]);});},_Nj));}),_58,_xf);});};},_Nc[1]));return _Ni[0]==0?[0]:[1,_Ni[1],new T(function(){return B(_f6(_MM,_Ni[2]));})];}),_Nh,_);});},_Nd,_)),_Np=_Ng,_Nq=B(A(_ij,[_5n,_Np,_KX,_MH,_])),_Nr=_Nq;return _Nd;},_58,_xf);});}:function(_58,_xf){return new F(function(){return _La(_j7,function(_Ns,_){var _Nt=B(_La(_id,_MU,_Ns,_)),_Nu=_Nt,_Nv=B(_La(_id,new T(function(){var _Nw=E(_Nc[1]);return B(_nk(new T(function(){return B(_n7(_N2,_N1,_N0,_MZ,_MY,_MW,_MX));}),new T(function(){return B(_fG(_N2,_N1,_N0,_MZ,_MY,_MW,_MX));}),_Nw[1],_Nw[2]));}),_Ns,_)),_Nx=_Nv,_Ny=B(A(_ij,[_5n,_Nx,_KX,_MH,_])),_Nz=_Ny;return _Ns;},_58,_xf);});};},_NA=function(_NB){var _NC=E(_NB);return _NC[0]==0?E(_MJ):function(_ND,_){var _NE=B(A(new T(function(){var _NF=E(_NC[1]);switch(_NF[0]){case 0:var _NG=E(_NF[1]),_NH=B(_N9(_NG[1],_NG[2]));break;case 1:var _NI=E(_NF[1]),_NH=B(_N9(_NI[1],_NI[2]));break;case 2:var _NH=function(_58,_xf){return new F(function(){return _La(_j7,function(_NJ,_){var _NK=B(_La(_id,_MS,_NJ,_)),_NL=_NK,_NM=B(_La(_id,_NF[1],_NJ,_)),_NN=_NM,_NO=B(A(_ij,[_5n,_NN,_KX,_MH,_])),_NP=_NO;return _NJ;},_58,_xf);});};break;default:var _NH=E(_MI);}return _NH;}),[_ND,_])),_NQ=_NE,_NR=B(A(new T(function(){return B(_NA(_NC[2]));}),[_ND,_])),_NS=_NR;return _ND;};};return B(_NA(_N8));}),_58,_xf);});};};},_NT=2,_NU=new T(function(){return B(unCStr("lined"));}),_NV=function(_NW,_){return [0,[0,_ix,[1,_NW]],_NW];},_NX=function(_NY){return function(_NZ,_){return [0,[0,_ix,[1,[1,_ip,new T(function(){var _O0=E(_NY);return B(_e(B(_F(0,E(_O0[2])[1],_9)),_O0[1]));})]]],_NZ];};},_O1=function(_Ms,_){return new F(function(){return _j9(_NV,_NX,_Ms,_);});},_O2=function(_O3){return function(_O4,_){return [0,[0,_ix,[1,[1,_ip,new T(function(){var _O5=E(_O3);return B(_e(B(_F(0,E(_O5[2])[1],_9)),_O5[1]));})]]],_O4];};},_O6=function(_Ms,_){return new F(function(){return _j9(_NV,_O2,_Ms,_);});},_O7=function(_O8){return function(_O9,_){return [0,[0,_ix,[1,[1,_ip,new T(function(){var _Oa=E(_O8);return B(_e(B(_F(0,E(_Oa[2])[1],_9)),_Oa[1]));})]]],_O9];};},_Ob=function(_Ms,_){return new F(function(){return _j9(_NV,_O7,_Ms,_);});},_Oc=new T(function(){return B(unCStr("rslt"));}),_Od=new T(function(){return B(unCStr("root"));}),_Oe=new T(function(){return B(unCStr("analysis"));}),_Of=new T(function(){return B(unCStr("invalid"));}),_Og=function(_Ms,_){return new F(function(){return _iX(_id,_Of,_Ms,_);});},_Oh=[1,_1x],_Oi=[0,_Og,_Oh],_Oj=function(_Ok,_){return [0,_Oi,_Ok];},_Ol=new T(function(){return B(unCStr("span"));}),_Om=function(_On,_Oo,_Op,_Oq,_){var _Or=B(A(_Op,[_Oq,_])),_Os=_Or,_Ot=E(_Os),_Ou=E(_Ot[1]),_Ov=_Ou[1];return [0,[0,function(_Ow,_){var _Ox=jsFind(toJSStr(E(_On))),_Oy=_Ox,_Oz=E(_Oy);if(!_Oz[0]){return _Ow;}else{var _OA=_Oz[1];switch(E(_Oo)){case 0:var _OB=B(A(_Ov,[_OA,_])),_OC=_OB;return _Ow;case 1:var _OD=E(_OA),_OE=_OD[1],_OF=jsGetChildren(_OE),_OG=_OF,_OH=E(_OG);if(!_OH[0]){var _OI=B(A(_Ov,[_OD,_])),_OJ=_OI;return _Ow;}else{var _OK=jsCreateElem(toJSStr(E(_Ol))),_OL=_OK,_OM=jsAddChildBefore(_OL,_OE,E(_OH[1])[1]),_ON=B(A(_Ov,[[0,_OL],_])),_OO=_ON;return _Ow;}break;default:var _OP=E(_OA),_OQ=jsClearChildren(_OP[1]),_OR=B(A(_Ov,[_OP,_])),_OS=_OR;return _Ow;}}},_Ou[2]],_Ot[2]];},_OT=function(_OU,_OV){while(1){var _OW=E(_OU);if(!_OW[0]){return E(_OV)[0]==0?1:0;}else{var _OX=E(_OV);if(!_OX[0]){return 2;}else{var _OY=E(_OW[1])[1],_OZ=E(_OX[1])[1];if(_OY!=_OZ){return _OY>_OZ?2:0;}else{_OU=_OW[2];_OV=_OX[2];continue;}}}}},_P0=new T(function(){return B(_e(_9,_9));}),_P1=function(_P2,_P3,_P4,_P5,_P6,_P7,_P8,_P9){var _Pa=[0,_P2,_P3,_P4],_Pb=function(_Pc){var _Pd=E(_P5);if(!_Pd[0]){var _Pe=E(_P9);if(!_Pe[0]){switch(B(_OT(_P2,_P6))){case 0:return [0,[0,_P6,_P7,_P8],_9];case 1:return _P3>=_P7?_P3!=_P7?[0,_Pa,_9]:_P4>=_P8?_P4!=_P8?[0,_Pa,_9]:[0,_Pa,_P0]:[0,[0,_P6,_P7,_P8],_9]:[0,[0,_P6,_P7,_P8],_9];default:return [0,_Pa,_9];}}else{return [0,[0,_P6,_P7,_P8],_Pe];}}else{switch(B(_OT(_P2,_P6))){case 0:return [0,[0,_P6,_P7,_P8],_P9];case 1:return _P3>=_P7?_P3!=_P7?[0,_Pa,_Pd]:_P4>=_P8?_P4!=_P8?[0,_Pa,_Pd]:[0,_Pa,new T(function(){return B(_e(_Pd,_P9));})]:[0,[0,_P6,_P7,_P8],_P9]:[0,[0,_P6,_P7,_P8],_P9];default:return [0,_Pa,_Pd];}}};if(!E(_P9)[0]){var _Pf=E(_P5);return _Pf[0]==0?B(_Pb(_)):[0,_Pa,_Pf];}else{return new F(function(){return _Pb(_);});}},_Pg=new T(function(){return B(_H5(_9,_9));}),_Ph=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_Pi=new T(function(){return B(err(_Ph));}),_Pj=function(_Pk,_Pl,_Pm,_Pn,_Po){var _Pp=function(_Pq,_Pr,_Ps){var _Pt=[1,_Pr,_Pq];return new F(function(){return A(_Pk,[_Ps,new T(function(){var _Pu=E(_Pq);return function(_Pv,_Pw,_Px){return new F(function(){return _Pp(_Pt,_Pv,_Pw);});};}),_Pn,_Pi,function(_Py){return new F(function(){return A(_Pm,[new T(function(){return B(_H5(_Pt,_9));}),_Ps,new T(function(){var _Pz=E(E(_Ps)[2]),_PA=E(_Py),_PB=E(_PA[1]),_PC=B(_P1(_PB[1],_PB[2],_PB[3],_PA[2],_Pz[1],_Pz[2],_Pz[3],_9));return [0,E(_PC[1]),_PC[2]];})]);});}]);});};return new F(function(){return A(_Pk,[_Pl,function(_PD,_PE,_PF){return new F(function(){return _Pp(_9,_PD,_PE);});},_Pn,_Pi,function(_PG){return new F(function(){return A(_Po,[_Pg,_Pl,new T(function(){var _PH=E(E(_Pl)[2]),_PI=E(_PG),_PJ=E(_PI[1]),_PK=B(_P1(_PJ[1],_PJ[2],_PJ[3],_PI[2],_PH[1],_PH[2],_PH[3],_9));return [0,E(_PK[1]),_PK[2]];})]);});}]);});},_PL=function(_PM,_PN){var _PO=E(_PM),_PP=E(_PO[1]),_PQ=E(_PN),_PR=E(_PQ[1]),_PS=B(_P1(_PP[1],_PP[2],_PP[3],_PO[2],_PR[1],_PR[2],_PR[3],_PQ[2]));return [0,E(_PS[1]),_PS[2]];},_PT=function(_PU,_PV,_PW,_PX,_PY,_PZ){var _Q0=function(_Q1,_Q2,_Q3,_Q4,_Q5){return new F(function(){return _Pj(_PU,_Q2,function(_Q6,_Q7,_Q8){return new F(function(){return A(_Q3,[[1,_Q1,_Q6],_Q7,new T(function(){var _Q9=E(E(_Q7)[2]),_Qa=E(_Q8),_Qb=E(_Qa[1]),_Qc=B(_P1(_Qb[1],_Qb[2],_Qb[3],_Qa[2],_Q9[1],_Q9[2],_Q9[3],_9));return [0,E(_Qc[1]),_Qc[2]];})]);});},_Q4,function(_Qd,_Qe,_Qf){return new F(function(){return A(_Q5,[[1,_Q1,_Qd],_Qe,new T(function(){var _Qg=E(E(_Qe)[2]),_Qh=E(_Qf),_Qi=E(_Qh[1]),_Qj=B(_P1(_Qi[1],_Qi[2],_Qi[3],_Qh[2],_Qg[1],_Qg[2],_Qg[3],_9));return [0,E(_Qj[1]),_Qj[2]];})]);});});});};return new F(function(){return A(_PU,[_PV,function(_Qk,_Ql,_Qm){return new F(function(){return _Q0(_Qk,_Ql,_PW,_PX,function(_Qn,_Qo,_Qp){return new F(function(){return A(_PW,[_Qn,_Qo,new T(function(){return B(_PL(_Qm,_Qp));})]);});});});},_PX,function(_Qq,_Qr,_Qs){return new F(function(){return _Q0(_Qq,_Qr,_PW,_PX,function(_Qt,_Qu,_Qv){return new F(function(){return A(_PY,[_Qt,_Qu,new T(function(){return B(_PL(_Qs,_Qv));})]);});});});},_PZ]);});},_Qw=function(_Qx,_Qy,_Qz,_QA,_QB){var _QC=function(_QD,_QE){return new F(function(){return A(_Qx,[_QE,new T(function(){var _QF=E(_QD);return function(_QG,_QH,_QI){return new F(function(){return _QC(_9,_QH);});};}),_QA,_Pi,function(_QJ){return new F(function(){return A(_Qz,[_1x,_QE,new T(function(){var _QK=E(E(_QE)[2]),_QL=E(_QJ),_QM=E(_QL[1]),_QN=B(_P1(_QM[1],_QM[2],_QM[3],_QL[2],_QK[1],_QK[2],_QK[3],_9));return [0,E(_QN[1]),_QN[2]];})]);});}]);});};return new F(function(){return A(_Qx,[_Qy,function(_QO,_QP,_QQ){return new F(function(){return _QC(_9,_QP);});},_QA,_Pi,function(_QR){return new F(function(){return A(_QB,[_1x,_Qy,new T(function(){var _QS=E(E(_Qy)[2]),_QT=E(_QR),_QU=E(_QT[1]),_QV=B(_P1(_QU[1],_QU[2],_QU[3],_QT[2],_QS[1],_QS[2],_QS[3],_9));return [0,E(_QV[1]),_QV[2]];})]);});}]);});},_QW=function(_QX,_QY,_QZ,_R0,_R1,_R2,_R3){var _R4=function(_R5,_R6,_R7,_R8,_R9){var _Ra=[1,_R5,_9],_Rb=function(_Rc,_Rd,_Re,_Rf){return new F(function(){return _QW(_QX,_QY,_Rc,function(_Rg,_Rh,_Ri){return new F(function(){return A(_Rd,[[1,_R5,_Rg],_Rh,new T(function(){var _Rj=E(E(_Rh)[2]),_Rk=E(_Ri),_Rl=E(_Rk[1]),_Rm=B(_P1(_Rl[1],_Rl[2],_Rl[3],_Rk[2],_Rj[1],_Rj[2],_Rj[3],_9));return [0,E(_Rm[1]),_Rm[2]];})]);});},_Re,function(_Rn,_Ro,_Rp){return new F(function(){return A(_Rf,[[1,_R5,_Rn],_Ro,new T(function(){var _Rq=E(E(_Ro)[2]),_Rr=E(_Rp),_Rs=E(_Rr[1]),_Rt=B(_P1(_Rs[1],_Rs[2],_Rs[3],_Rr[2],_Rq[1],_Rq[2],_Rq[3],_9));return [0,E(_Rt[1]),_Rt[2]];})]);});},function(_Ru){return new F(function(){return A(_Rf,[_Ra,_Rc,new T(function(){var _Rv=E(E(_Rc)[2]),_Rw=_Rv[1],_Rx=_Rv[2],_Ry=_Rv[3],_Rz=E(_Ru),_RA=E(_Rz[1]),_RB=B(_P1(_RA[1],_RA[2],_RA[3],_Rz[2],_Rw,_Rx,_Ry,_9)),_RC=E(_RB[1]),_RD=B(_P1(_RC[1],_RC[2],_RC[3],_RB[2],_Rw,_Rx,_Ry,_9));return [0,E(_RD[1]),_RD[2]];})]);});});});};return new F(function(){return A(_QY,[_R6,function(_RE,_RF,_RG){return new F(function(){return _Rb(_RF,_R7,_R8,function(_RH,_RI,_RJ){return new F(function(){return A(_R7,[_RH,_RI,new T(function(){return B(_PL(_RG,_RJ));})]);});});});},_R8,function(_RK,_RL,_RM){return new F(function(){return _Rb(_RL,_R7,_R8,function(_RN,_RO,_RP){return new F(function(){return A(_R9,[_RN,_RO,new T(function(){return B(_PL(_RM,_RP));})]);});});});},function(_RQ){return new F(function(){return A(_R9,[_Ra,_R6,new T(function(){var _RR=E(E(_R6)[2]),_RS=E(_RQ),_RT=E(_RS[1]),_RU=B(_P1(_RT[1],_RT[2],_RT[3],_RS[2],_RR[1],_RR[2],_RR[3],_9));return [0,E(_RU[1]),_RU[2]];})]);});}]);});};return new F(function(){return A(_QX,[_QZ,function(_RV,_RW,_RX){return new F(function(){return _R4(_RV,_RW,_R0,_R1,function(_RY,_RZ,_S0){return new F(function(){return A(_R0,[_RY,_RZ,new T(function(){return B(_PL(_RX,_S0));})]);});});});},_R1,function(_S1,_S2,_S3){return new F(function(){return _R4(_S1,_S2,_R0,_R1,function(_S4,_S5,_S6){return new F(function(){return A(_R2,[_S4,_S5,new T(function(){return B(_PL(_S3,_S6));})]);});});});},_R3]);});},_S7=function(_S8,_S9){return new F(function(){return A(_S9,[_S8]);});},_Sa=[0,34],_Sb=[1,_Sa,_9],_Sc=[0,E(_9)],_Sd=[1,_Sc,_9],_Se=function(_Sf,_Sg){var _Sh=_Sf%_Sg;if(_Sf<=0){if(_Sf>=0){return E(_Sh);}else{if(_Sg<=0){return E(_Sh);}else{var _Si=E(_Sh);return _Si==0?0:_Si+_Sg|0;}}}else{if(_Sg>=0){if(_Sf>=0){return E(_Sh);}else{if(_Sg<=0){return E(_Sh);}else{var _Sj=E(_Sh);return _Sj==0?0:_Sj+_Sg|0;}}}else{var _Sk=E(_Sh);return _Sk==0?0:_Sk+_Sg|0;}}},_Sl=new T(function(){return B(unCStr("ACK"));}),_Sm=new T(function(){return B(unCStr("BEL"));}),_Sn=new T(function(){return B(unCStr("BS"));}),_So=new T(function(){return B(unCStr("SP"));}),_Sp=[1,_So,_9],_Sq=new T(function(){return B(unCStr("US"));}),_Sr=[1,_Sq,_Sp],_Ss=new T(function(){return B(unCStr("RS"));}),_St=[1,_Ss,_Sr],_Su=new T(function(){return B(unCStr("GS"));}),_Sv=[1,_Su,_St],_Sw=new T(function(){return B(unCStr("FS"));}),_Sx=[1,_Sw,_Sv],_Sy=new T(function(){return B(unCStr("ESC"));}),_Sz=[1,_Sy,_Sx],_SA=new T(function(){return B(unCStr("SUB"));}),_SB=[1,_SA,_Sz],_SC=new T(function(){return B(unCStr("EM"));}),_SD=[1,_SC,_SB],_SE=new T(function(){return B(unCStr("CAN"));}),_SF=[1,_SE,_SD],_SG=new T(function(){return B(unCStr("ETB"));}),_SH=[1,_SG,_SF],_SI=new T(function(){return B(unCStr("SYN"));}),_SJ=[1,_SI,_SH],_SK=new T(function(){return B(unCStr("NAK"));}),_SL=[1,_SK,_SJ],_SM=new T(function(){return B(unCStr("DC4"));}),_SN=[1,_SM,_SL],_SO=new T(function(){return B(unCStr("DC3"));}),_SP=[1,_SO,_SN],_SQ=new T(function(){return B(unCStr("DC2"));}),_SR=[1,_SQ,_SP],_SS=new T(function(){return B(unCStr("DC1"));}),_ST=[1,_SS,_SR],_SU=new T(function(){return B(unCStr("DLE"));}),_SV=[1,_SU,_ST],_SW=new T(function(){return B(unCStr("SI"));}),_SX=[1,_SW,_SV],_SY=new T(function(){return B(unCStr("SO"));}),_SZ=[1,_SY,_SX],_T0=new T(function(){return B(unCStr("CR"));}),_T1=[1,_T0,_SZ],_T2=new T(function(){return B(unCStr("FF"));}),_T3=[1,_T2,_T1],_T4=new T(function(){return B(unCStr("VT"));}),_T5=[1,_T4,_T3],_T6=new T(function(){return B(unCStr("LF"));}),_T7=[1,_T6,_T5],_T8=new T(function(){return B(unCStr("HT"));}),_T9=[1,_T8,_T7],_Ta=[1,_Sn,_T9],_Tb=[1,_Sm,_Ta],_Tc=[1,_Sl,_Tb],_Td=new T(function(){return B(unCStr("ENQ"));}),_Te=[1,_Td,_Tc],_Tf=new T(function(){return B(unCStr("EOT"));}),_Tg=[1,_Tf,_Te],_Th=new T(function(){return B(unCStr("ETX"));}),_Ti=[1,_Th,_Tg],_Tj=new T(function(){return B(unCStr("STX"));}),_Tk=[1,_Tj,_Ti],_Tl=new T(function(){return B(unCStr("SOH"));}),_Tm=[1,_Tl,_Tk],_Tn=new T(function(){return B(unCStr("NUL"));}),_To=[1,_Tn,_Tm],_Tp=[0,92],_Tq=new T(function(){return B(unCStr("\\DEL"));}),_Tr=new T(function(){return B(unCStr("\\a"));}),_Ts=new T(function(){return B(unCStr("\\\\"));}),_Tt=new T(function(){return B(unCStr("\\SO"));}),_Tu=new T(function(){return B(unCStr("\\r"));}),_Tv=new T(function(){return B(unCStr("\\f"));}),_Tw=new T(function(){return B(unCStr("\\v"));}),_Tx=new T(function(){return B(unCStr("\\n"));}),_Ty=new T(function(){return B(unCStr("\\t"));}),_Tz=new T(function(){return B(unCStr("\\b"));}),_TA=function(_TB,_TC){if(_TB<=127){var _TD=E(_TB);switch(_TD){case 92:return new F(function(){return _e(_Ts,_TC);});break;case 127:return new F(function(){return _e(_Tq,_TC);});break;default:if(_TD<32){var _TE=E(_TD);switch(_TE){case 7:return new F(function(){return _e(_Tr,_TC);});break;case 8:return new F(function(){return _e(_Tz,_TC);});break;case 9:return new F(function(){return _e(_Ty,_TC);});break;case 10:return new F(function(){return _e(_Tx,_TC);});break;case 11:return new F(function(){return _e(_Tw,_TC);});break;case 12:return new F(function(){return _e(_Tv,_TC);});break;case 13:return new F(function(){return _e(_Tu,_TC);});break;case 14:return new F(function(){return _e(_Tt,new T(function(){var _TF=E(_TC);if(!_TF[0]){var _TG=[0];}else{var _TG=E(E(_TF[1])[1])==72?B(unAppCStr("\\&",_TF)):E(_TF);}return _TG;},1));});break;default:return new F(function(){return _e([1,_Tp,new T(function(){var _TH=_TE;return _TH>=0?B(_1s(_To,_TH)):E(_1p);})],_TC);});}}else{return [1,[0,_TD],_TC];}}}else{return [1,_Tp,new T(function(){var _TI=jsShowI(_TB),_TJ=_TI;return B(_e(fromJSStr(_TJ),new T(function(){var _TK=E(_TC);if(!_TK[0]){var _TL=[0];}else{var _TM=E(_TK[1])[1];if(_TM<48){var _TN=E(_TK);}else{var _TN=_TM>57?E(_TK):B(unAppCStr("\\&",_TK));}var _TO=_TN,_TP=_TO,_TL=_TP;}return _TL;},1)));})];}},_TQ=new T(function(){return B(unCStr("\\\""));}),_TR=function(_TS,_TT){var _TU=E(_TS);if(!_TU[0]){return E(_TT);}else{var _TV=_TU[2],_TW=E(E(_TU[1])[1]);if(_TW==34){return new F(function(){return _e(_TQ,new T(function(){return B(_TR(_TV,_TT));},1));});}else{return new F(function(){return _TA(_TW,new T(function(){return B(_TR(_TV,_TT));}));});}}},_TX=function(_TY,_TZ,_U0,_U1,_U2,_U3,_U4,_U5,_U6,_U7){var _U8=[0,_U2,_U3,_U4];return new F(function(){return A(_TY,[new T(function(){return B(A(_TZ,[_U1]));}),function(_U9){var _Ua=E(_U9);if(!_Ua[0]){return E(new T(function(){return B(A(_U7,[[0,E(_U8),_Sd]]));}));}else{var _Ub=E(_Ua[1]),_Uc=_Ub[1],_Ud=_Ub[2];if(!B(A(_U0,[_Uc]))){return new F(function(){return A(_U7,[[0,E(_U8),[1,[0,E([1,_Sa,new T(function(){return B(_TR([1,_Uc,_9],_Sb));})])],_9]]]);});}else{var _Ue=E(_Uc);switch(E(_Ue[1])){case 9:var _Uf=[0,_U2,_U3,(_U4+8|0)-B(_Se(_U4-1|0,8))|0];break;case 10:var _Uf=E([0,_U2,_U3+1|0,1]);break;default:var _Uf=E([0,_U2,_U3,_U4+1|0]);}var _Ug=_Uf,_Uh=[0,E(_Ug),_9],_Ui=[0,_Ud,E(_Ug),E(_U5)];return new F(function(){return A(_U6,[_Ue,_Ui,_Uh]);});}}}]);});},_Uj=new T(function(){return B(unCStr(" 	"));}),_Uk=function(_Ul){return new F(function(){return _6X(_4m,_Ul,_Uj);});},_Um=function(_Un,_Uo){return E(_Uo);},_Up=function(_Uq){return new F(function(){return err(_Uq);});},_Ur=function(_Us){return E(_Us);},_Ut=[0,_S7,_Um,_Ur,_Up],_Uu=function(_Uv){return E(E(_Uv)[3]);},_Uw=function(_Ux,_Uy){var _Uz=E(_Uy);return _Uz[0]==0?B(A(_Uu,[_Ux,_6D])):B(A(_Uu,[_Ux,[1,[0,_Uz[1],_Uz[2]]]]));},_UA=function(_UB){return new F(function(){return _Uw(_Ut,_UB);});},_UC=function(_UD,_UE,_UF,_UG,_UH){var _UI=E(_UD),_UJ=E(_UI[2]);return new F(function(){return _TX(_S7,_UA,_Uk,_UI[1],_UJ[1],_UJ[2],_UJ[3],_UI[3],_UE,_UH);});},_UK=function(_UL){return [2,E(E(_UL))];},_UM=function(_UN,_UO){switch(E(_UN)[0]){case 0:switch(E(_UO)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_UO)[0]==1?false:true;case 2:return E(_UO)[0]==2?false:true;default:return E(_UO)[0]==3?false:true;}},_UP=[2,E(_9)],_UQ=function(_UR){return new F(function(){return _UM(_UP,_UR);});},_US=function(_UT,_UU,_UV){var _UW=E(_UV);if(!_UW[0]){return [0,_UT,[1,_UP,new T(function(){return B(_kp(_UQ,_UU));})]];}else{var _UX=_UW[1],_UY=E(_UW[2]);if(!_UY[0]){var _UZ=new T(function(){return [2,E(E(_UX))];});return [0,_UT,[1,_UZ,new T(function(){return B(_kp(function(_UR){return new F(function(){return _UM(_UZ,_UR);});},_UU));})]];}else{var _V0=new T(function(){return [2,E(E(_UX))];}),_V1=function(_V2){var _V3=E(_V2);if(!_V3[0]){return [0,_UT,[1,_V0,new T(function(){return B(_kp(function(_UR){return new F(function(){return _UM(_V0,_UR);});},_UU));})]];}else{var _V4=B(_V1(_V3[2]));return [0,_V4[1],[1,new T(function(){return B(_UK(_V3[1]));}),_V4[2]]];}};return new F(function(){return (function(_V5,_V6){var _V7=B(_V1(_V6));return [0,_V7[1],[1,new T(function(){return B(_UK(_V5));}),_V7[2]]];})(_UY[1],_UY[2]);});}}},_V8=function(_V9,_Va){var _Vb=E(_V9),_Vc=B(_US(_Vb[1],_Vb[2],_Va));return [0,E(_Vc[1]),_Vc[2]];},_Vd=function(_Ve,_Vf,_Vg,_Vh,_Vi,_Vj,_Vk){return new F(function(){return A(_Ve,[_Vg,_Vh,_Vi,function(_Vl,_Vm,_Vn){return new F(function(){return A(_Vj,[_Vl,_Vm,new T(function(){var _Vo=E(_Vn),_Vp=E(_Vo[2]);if(!_Vp[0]){var _Vq=E(_Vo);}else{var _Vr=B(_US(_Vo[1],_Vp,_Vf)),_Vq=[0,E(_Vr[1]),_Vr[2]];}var _Vs=_Vq;return _Vs;})]);});},function(_Vt){return new F(function(){return A(_Vk,[new T(function(){return B(_V8(_Vt,_Vf));})]);});}]);});},_Vu=new T(function(){return B(unCStr("digit"));}),_Vv=[1,_Vu,_9],_Vw=function(_Vx){return new F(function(){return _Uw(_Ut,_Vx);});},_Vy=function(_Vz){var _VA=E(_Vz)[1];return _VA<48?false:_VA<=57;},_VB=function(_VC,_VD,_VE,_VF,_VG){var _VH=E(_VC),_VI=E(_VH[2]);return new F(function(){return _TX(_S7,_Vw,_Vy,_VH[1],_VI[1],_VI[2],_VI[3],_VH[3],_VD,_VG);});},_VJ=function(_VK,_VL,_VM,_VN,_VO){return new F(function(){return _Vd(_VB,_Vv,_VK,_VL,_VM,_VN,_VO);});},_VP=function(_VQ,_VR,_VS,_VT,_VU){return new F(function(){return _PT(_VJ,_VQ,_VR,_VS,_VT,_VU);});},_VV=function(_VW){return [0,_VW,function(_UR){return new F(function(){return _Uw(_VW,_UR);});}];},_VX=new T(function(){return B(_VV(_Ut));}),_VY=function(_VZ,_W0){return function(_W1,_W2,_W3,_W4,_W5){return new F(function(){return _Vd(function(_W6,_W7,_W8,_W9,_Wa){var _Wb=E(_VZ),_Wc=E(_W6),_Wd=E(_Wc[2]);return new F(function(){return _TX(E(_Wb[1])[1],_Wb[2],function(_We){return new F(function(){return _4j(_We,_W0);});},_Wc[1],_Wd[1],_Wd[2],_Wd[3],_Wc[3],_W7,_Wa);});},[1,[1,_Sa,new T(function(){return B(_TR([1,_W0,_9],_Sb));})],_9],_W1,_W2,_W3,_W4,_W5);});};},_Wf=[0,44],_Wg=new T(function(){return B(_VY(_VX,_Wf));}),_Wh=new T(function(){return B(err(_2a));}),_Wi=new T(function(){return B(err(_28));}),_Wj=new T(function(){return B(_dz(_dV,_dm,_e1));}),_Wk=function(_Wl){var _Wm=B(_e9(B(_3u(_Wj,_Wl))));return _Wm[0]==0?E(_Wh):E(_Wm[2])[0]==0?E(_Wm[1]):E(_Wi);},_Wn=function(_Wo,_Wp,_Wq,_Wr,_Ws){var _Wt=function(_Wu,_Wv,_Ww){var _Wx=function(_Wy,_Wz,_WA){return new F(function(){return A(_Ww,[[0,_Wo,new T(function(){return B(_f2(_Wk,_Wy));})],_Wz,new T(function(){var _WB=E(E(_Wz)[2]),_WC=E(_WA),_WD=E(_WC[1]),_WE=B(_P1(_WD[1],_WD[2],_WD[3],_WC[2],_WB[1],_WB[2],_WB[3],_9));return [0,E(_WE[1]),_WE[2]];})]);});},_WF=function(_WG){return new F(function(){return _Wx(_9,_Wu,new T(function(){var _WH=E(E(_Wu)[2]),_WI=E(_WG),_WJ=E(_WI[1]),_WK=B(_P1(_WJ[1],_WJ[2],_WJ[3],_WI[2],_WH[1],_WH[2],_WH[3],_9));return [0,E(_WK[1]),_WK[2]];},1));});};return new F(function(){return _QW(_VP,_Wg,_Wu,function(_WL,_WM,_WN){return new F(function(){return A(_Wv,[[0,_Wo,new T(function(){return B(_f2(_Wk,_WL));})],_WM,new T(function(){var _WO=E(E(_WM)[2]),_WP=E(_WN),_WQ=E(_WP[1]),_WR=B(_P1(_WQ[1],_WQ[2],_WQ[3],_WP[2],_WO[1],_WO[2],_WO[3],_9));return [0,E(_WR[1]),_WR[2]];})]);});},_WF,_Wx,_WF);});};return new F(function(){return _Qw(_UC,_Wp,function(_WS,_WT,_WU){return new F(function(){return _Wt(_WT,_Wq,function(_WV,_WW,_WX){return new F(function(){return A(_Wq,[_WV,_WW,new T(function(){return B(_PL(_WU,_WX));})]);});});});},_Wr,function(_WY,_WZ,_X0){return new F(function(){return _Wt(_WZ,_Wq,function(_X1,_X2,_X3){return new F(function(){return A(_Ws,[_X1,_X2,new T(function(){return B(_PL(_X0,_X3));})]);});});});});});},_X4=new T(function(){return B(unCStr("letter or digit"));}),_X5=[1,_X4,_9],_X6=function(_X7){var _X8=u_iswalnum(E(_X7)[1]),_X9=_X8;return E(_X9)==0?false:true;},_Xa=function(_Xb,_Xc,_Xd,_Xe,_Xf){var _Xg=E(_Xb),_Xh=E(_Xg[2]);return new F(function(){return _TX(_S7,_Vw,_X6,_Xg[1],_Xh[1],_Xh[2],_Xh[3],_Xg[3],_Xc,_Xf);});},_Xi=function(_Xj,_Xk,_Xl,_Xm,_Xn){return new F(function(){return _Vd(_Xa,_X5,_Xj,_Xk,_Xl,_Xm,_Xn);});},_Xo=function(_Xp,_Xq,_Xr,_Xs,_Xt){return new F(function(){return _PT(_Xi,_Xp,function(_Xu,_Xv,_Xw){return new F(function(){return _Wn(_Xu,_Xv,_Xq,_Xr,function(_Xx,_Xy,_Xz){return new F(function(){return A(_Xq,[_Xx,_Xy,new T(function(){return B(_PL(_Xw,_Xz));})]);});});});},_Xt,function(_XA,_XB,_XC){return new F(function(){return _Wn(_XA,_XB,_Xq,_Xr,function(_XD,_XE,_XF){return new F(function(){return A(_Xs,[_XD,_XE,new T(function(){return B(_PL(_XC,_XF));})]);});});});},_Xt);});},_XG=new T(function(){return B(unCStr("SHOW"));}),_XH=[0,_XG,_9],_XI=function(_XJ,_XK,_XL,_XM){var _XN=function(_XO){return new F(function(){return A(_XM,[[0,_XJ,_XH],_XK,new T(function(){var _XP=E(E(_XK)[2]),_XQ=_XP[1],_XR=_XP[2],_XS=_XP[3],_XT=E(_XO),_XU=E(_XT[1]),_XV=B(_P1(_XU[1],_XU[2],_XU[3],_XT[2],_XQ,_XR,_XS,_9)),_XW=E(_XV[1]),_XX=B(_P1(_XW[1],_XW[2],_XW[3],_XV[2],_XQ,_XR,_XS,_9));return [0,E(_XX[1]),_XX[2]];})]);});};return new F(function(){return _Xo(_XK,function(_XY,_XZ,_Y0){return new F(function(){return A(_XL,[[0,_XJ,_XY],_XZ,new T(function(){var _Y1=E(E(_XZ)[2]),_Y2=E(_Y0),_Y3=E(_Y2[1]),_Y4=B(_P1(_Y3[1],_Y3[2],_Y3[3],_Y2[2],_Y1[1],_Y1[2],_Y1[3],_9));return [0,E(_Y4[1]),_Y4[2]];})]);});},_XN,function(_Y5,_Y6,_Y7){return new F(function(){return A(_XM,[[0,_XJ,_Y5],_Y6,new T(function(){var _Y8=E(E(_Y6)[2]),_Y9=E(_Y7),_Ya=E(_Y9[1]),_Yb=B(_P1(_Ya[1],_Ya[2],_Ya[3],_Y9[2],_Y8[1],_Y8[2],_Y8[3],_9));return [0,E(_Yb[1]),_Yb[2]];})]);});},_XN);});},_Yc=new T(function(){return B(unCStr("sS"));}),_Yd=new T(function(){return B(_VV(_Ut));}),_Ye=[0,58],_Yf=new T(function(){return B(_VY(_Yd,_Ye));}),_Yg=[1,_X4,_9],_Yh=function(_Yi,_Yj,_Yk,_Yl,_Ym,_Yn,_Yo,_Yp,_Yq){var _Yr=function(_Ys,_Yt){var _Yu=new T(function(){var _Yv=B(_US(_Ys,_Yt,_Yg));return [0,E(_Yv[1]),_Yv[2]];});return new F(function(){return A(_Yf,[[0,_Yi,E([0,_Yj,_Yk,_Yl]),E(_Ym)],_Yn,_Yo,function(_Yw,_Yx,_Yy){return new F(function(){return A(_Yp,[_Yw,_Yx,new T(function(){return B(_PL(_Yu,_Yy));})]);});},function(_Yz){return new F(function(){return A(_Yq,[new T(function(){return B(_PL(_Yu,_Yz));})]);});}]);});},_YA=E(_Yi);if(!_YA[0]){return new F(function(){return _Yr([0,_Yj,_Yk,_Yl],_Sd);});}else{var _YB=_YA[2],_YC=E(_YA[1]),_YD=_YC[1],_YE=u_iswalnum(_YD),_YF=_YE;if(!E(_YF)){return new F(function(){return _Yr([0,_Yj,_Yk,_Yl],[1,[0,E([1,_Sa,new T(function(){return B(_TR([1,_YC,_9],_Sb));})])],_9]);});}else{switch(E(_YD)){case 9:var _YG=[0,_Yj,_Yk,(_Yl+8|0)-B(_Se(_Yl-1|0,8))|0];break;case 10:var _YG=[0,_Yj,_Yk+1|0,1];break;default:var _YG=[0,_Yj,_Yk,_Yl+1|0];}var _YH=_YG,_YI=[0,E(_YH),_9],_YJ=[0,_YB,E(_YH),E(_Ym)];return new F(function(){return A(_Yn,[_YC,_YJ,_YI]);});}}},_YK=function(_YL,_YM,_YN,_YO,_YP){var _YQ=E(_YL),_YR=E(_YQ[2]);return new F(function(){return _Yh(_YQ[1],_YR[1],_YR[2],_YR[3],_YQ[3],_YM,_YN,_YO,_YP);});},_YS=[0,10],_YT=new T(function(){return B(unCStr("lf new-line"));}),_YU=[1,_YT,_9],_YV=function(_YW){return function(_YX,_YY,_YZ,_Z0,_Z1){return new F(function(){return _Vd(new T(function(){return B(_VY(_YW,_YS));}),_YU,_YX,_YY,_YZ,_Z0,_Z1);});};},_Z2=new T(function(){return B(_YV(_Yd));}),_Z3=function(_Z4,_Z5,_Z6,_Z7,_Z8,_Z9,_Za){var _Zb=function(_Zc,_Zd,_Ze,_Zf,_Zg,_Zh){return new F(function(){return _Zi(_Zd,function(_Zj,_Zk,_Zl){return new F(function(){return A(_Ze,[[1,_Zc,_Zj],_Zk,new T(function(){var _Zm=E(E(_Zk)[2]),_Zn=E(_Zl),_Zo=E(_Zn[1]),_Zp=B(_P1(_Zo[1],_Zo[2],_Zo[3],_Zn[2],_Zm[1],_Zm[2],_Zm[3],_9));return [0,E(_Zp[1]),_Zp[2]];})]);});},_Zf,function(_Zq,_Zr,_Zs){return new F(function(){return A(_Zg,[[1,_Zc,_Zq],_Zr,new T(function(){var _Zt=E(E(_Zr)[2]),_Zu=E(_Zs),_Zv=E(_Zu[1]),_Zw=B(_P1(_Zv[1],_Zv[2],_Zv[3],_Zu[2],_Zt[1],_Zt[2],_Zt[3],_9));return [0,E(_Zw[1]),_Zw[2]];})]);});},_Zh);});},_Zi=function(_Zx,_Zy,_Zz,_ZA,_ZB){return new F(function(){return A(_Z5,[_Zx,function(_ZC,_ZD,_ZE){return new F(function(){return A(_Zy,[_9,_ZD,new T(function(){var _ZF=E(E(_ZD)[2]),_ZG=E(_ZE),_ZH=E(_ZG[1]),_ZI=B(_P1(_ZH[1],_ZH[2],_ZH[3],_ZG[2],_ZF[1],_ZF[2],_ZF[3],_9));return [0,E(_ZI[1]),_ZI[2]];})]);});},_Zz,function(_ZJ,_ZK,_ZL){return new F(function(){return A(_ZA,[_9,_ZK,new T(function(){var _ZM=E(E(_ZK)[2]),_ZN=E(_ZL),_ZO=E(_ZN[1]),_ZP=B(_P1(_ZO[1],_ZO[2],_ZO[3],_ZN[2],_ZM[1],_ZM[2],_ZM[3],_9));return [0,E(_ZP[1]),_ZP[2]];})]);});},function(_ZQ){return new F(function(){return A(_Z4,[_Zx,function(_ZR,_ZS,_ZT){return new F(function(){return _Zb(_ZR,_ZS,_Zy,_Zz,function(_ZU,_ZV,_ZW){return new F(function(){return A(_Zy,[_ZU,_ZV,new T(function(){return B(_PL(_ZT,_ZW));})]);});},function(_ZX){return new F(function(){return A(_Zz,[new T(function(){return B(_PL(_ZT,_ZX));})]);});});});},_Zz,function(_ZY,_ZZ,_100){return new F(function(){return _Zb(_ZY,_ZZ,_Zy,_Zz,function(_101,_102,_103){return new F(function(){return A(_ZA,[_101,_102,new T(function(){var _104=E(_ZQ),_105=E(_104[1]),_106=E(_100),_107=E(_106[1]),_108=E(_103),_109=E(_108[1]),_10a=B(_P1(_107[1],_107[2],_107[3],_106[2],_109[1],_109[2],_109[3],_108[2])),_10b=E(_10a[1]),_10c=B(_P1(_105[1],_105[2],_105[3],_104[2],_10b[1],_10b[2],_10b[3],_10a[2]));return [0,E(_10c[1]),_10c[2]];})]);});},function(_10d){return new F(function(){return A(_ZB,[new T(function(){var _10e=E(_ZQ),_10f=E(_10e[1]),_10g=E(_100),_10h=E(_10g[1]),_10i=E(_10d),_10j=E(_10i[1]),_10k=B(_P1(_10h[1],_10h[2],_10h[3],_10g[2],_10j[1],_10j[2],_10j[3],_10i[2])),_10l=E(_10k[1]),_10m=B(_P1(_10f[1],_10f[2],_10f[3],_10e[2],_10l[1],_10l[2],_10l[3],_10k[2]));return [0,E(_10m[1]),_10m[2]];})]);});});});},function(_10n){return new F(function(){return A(_ZB,[new T(function(){return B(_PL(_ZQ,_10n));})]);});}]);});}]);});};return new F(function(){return _Zi(_Z6,_Z7,_Z8,_Z9,_Za);});},_10o=new T(function(){return B(unCStr("tab"));}),_10p=[1,_10o,_9],_10q=[0,9],_10r=function(_10s){return function(_10t,_10u,_10v,_10w,_10x){return new F(function(){return _Vd(new T(function(){return B(_VY(_10s,_10q));}),_10p,_10t,_10u,_10v,_10w,_10x);});};},_10y=new T(function(){return B(_10r(_Yd));}),_10z=[0,39],_10A=[1,_10z,_9],_10B=new T(function(){return B(unCStr("\'\\\'\'"));}),_10C=function(_10D){var _10E=E(E(_10D)[1]);return _10E==39?E(_10B):[1,_10z,new T(function(){return B(_TA(_10E,_10A));})];},_10F=function(_10G,_10H){return [1,_Sa,new T(function(){return B(_TR(_10G,[1,_Sa,_10H]));})];},_10I=function(_10J){return new F(function(){return _e(_10B,_10J);});},_10K=function(_10L,_10M){var _10N=E(E(_10M)[1]);return _10N==39?E(_10I):function(_10O){return [1,_10z,new T(function(){return B(_TA(_10N,[1,_10z,_10O]));})];};},_10P=[0,_10K,_10C,_10F],_10Q=function(_10R,_10S,_10T,_10U,_10V){var _10W=new T(function(){return B(_ni(_10R));}),_10X=function(_10Y){return new F(function(){return A(_10U,[_1x,_10T,new T(function(){var _10Z=E(E(_10T)[2]),_110=E(_10Y),_111=E(_110[1]),_112=B(_P1(_111[1],_111[2],_111[3],_110[2],_10Z[1],_10Z[2],_10Z[3],_9));return [0,E(_112[1]),_112[2]];})]);});};return new F(function(){return A(_10S,[_10T,function(_113,_114,_115){return new F(function(){return A(_10V,[new T(function(){var _116=E(E(_114)[2]),_117=E(_115),_118=E(_117[1]),_119=B(_P1(_118[1],_118[2],_118[3],_117[2],_116[1],_116[2],_116[3],[1,new T(function(){return [1,E(B(A(_10W,[_113])))];}),_9]));return [0,E(_119[1]),_119[2]];})]);});},_10X,function(_11a,_11b,_11c){return new F(function(){return A(_10U,[_1x,_10T,new T(function(){var _11d=E(E(_10T)[2]),_11e=E(E(_11b)[2]),_11f=E(_11c),_11g=E(_11f[1]),_11h=B(_P1(_11g[1],_11g[2],_11g[3],_11f[2],_11e[1],_11e[2],_11e[3],[1,new T(function(){return [1,E(B(A(_10W,[_11a])))];}),_9])),_11i=E(_11h[1]),_11j=B(_P1(_11i[1],_11i[2],_11i[3],_11h[2],_11d[1],_11d[2],_11d[3],_9));return [0,E(_11j[1]),_11j[2]];})]);});},_10X]);});},_11k=function(_11l,_11m,_11n){return new F(function(){return _10Q(_10P,_10y,_11l,function(_11o,_11p,_11q){return new F(function(){return A(_11m,[_1x,_11p,new T(function(){var _11r=E(E(_11p)[2]),_11s=E(_11q),_11t=E(_11s[1]),_11u=B(_P1(_11t[1],_11t[2],_11t[3],_11s[2],_11r[1],_11r[2],_11r[3],_9));return [0,E(_11u[1]),_11u[2]];})]);});},_11n);});},_11v=function(_11w,_11x,_11y,_11z,_11A){return new F(function(){return A(_Z2,[_11w,function(_11B,_11C,_11D){return new F(function(){return _11k(_11C,function(_11E,_11F,_11G){return new F(function(){return A(_11x,[_11E,_11F,new T(function(){return B(_PL(_11D,_11G));})]);});},function(_11H){return new F(function(){return A(_11y,[new T(function(){return B(_PL(_11D,_11H));})]);});});});},_11y,function(_11I,_11J,_11K){return new F(function(){return _11k(_11J,function(_11L,_11M,_11N){return new F(function(){return A(_11z,[_11L,_11M,new T(function(){return B(_PL(_11K,_11N));})]);});},function(_11O){return new F(function(){return A(_11A,[new T(function(){return B(_PL(_11K,_11O));})]);});});});},_11A]);});},_11P=[0,E(_9)],_11Q=[1,_11P,_9],_11R=function(_11S,_11T,_11U,_11V,_11W,_11X,_11Y){return new F(function(){return A(_11S,[new T(function(){return B(A(_11T,[_11U]));}),function(_11Z){var _120=E(_11Z);if(!_120[0]){return E(new T(function(){return B(A(_11Y,[[0,E(_11V),_11Q]]));}));}else{var _121=E(_120[1]);return new F(function(){return A(_11X,[_121[1],[0,_121[2],E(_11V),E(_11W)],[0,E(_11V),_9]]);});}}]);});},_122=new T(function(){return B(unCStr("end of input"));}),_123=[1,_122,_9],_124=function(_125,_126,_127,_128,_129,_12a,_12b,_12c){return new F(function(){return _Vd(function(_12d,_12e,_12f,_12g,_12h){return new F(function(){return _10Q(_127,function(_12i,_12j,_12k,_12l,_12m){var _12n=E(_12i);return new F(function(){return _11R(_125,_126,_12n[1],_12n[2],_12n[3],_12j,_12m);});},_12d,_12g,_12h);});},_123,_128,_129,_12a,_12b,_12c);});},_12o=function(_12p,_12q,_12r,_12s,_12t){return new F(function(){return _Pj(_Z2,_12p,function(_12u,_12v,_12w){return new F(function(){return _124(_S7,_UA,_10P,_12v,_12q,_12r,function(_12x,_12y,_12z){return new F(function(){return A(_12q,[_12x,_12y,new T(function(){return B(_PL(_12w,_12z));})]);});},function(_12A){return new F(function(){return A(_12r,[new T(function(){return B(_PL(_12w,_12A));})]);});});});},_12r,function(_12B,_12C,_12D){return new F(function(){return _124(_S7,_UA,_10P,_12C,_12q,_12r,function(_12E,_12F,_12G){return new F(function(){return A(_12s,[_12E,_12F,new T(function(){return B(_PL(_12D,_12G));})]);});},function(_12H){return new F(function(){return A(_12t,[new T(function(){return B(_PL(_12D,_12H));})]);});});});});});},_12I=function(_12J,_12K,_12L,_12M){var _12N=function(_12O){var _12P=function(_12Q){return new F(function(){return A(_12M,[new T(function(){return B(_PL(_12O,_12Q));})]);});};return new F(function(){return _11v(_12J,_12K,_12P,function(_12R,_12S,_12T){return new F(function(){return A(_12L,[_12R,_12S,new T(function(){return B(_PL(_12O,_12T));})]);});},_12P);});};return new F(function(){return _12o(_12J,_12K,_12N,_12L,_12N);});},_12U=function(_12V,_12W,_12X,_12Y,_12Z){return new F(function(){return _12I(_12V,_12W,_12Y,_12Z);});},_130=function(_131){return true;},_132=function(_133,_134,_135,_136,_137){var _138=E(_133),_139=E(_138[2]);return new F(function(){return _TX(_S7,_UA,_130,_138[1],_139[1],_139[2],_139[3],_138[3],_134,_137);});},_13a=function(_13b,_13c,_13d,_13e,_13f){return new F(function(){return A(_10y,[_13b,function(_13g,_13h,_13i){return new F(function(){return _Z3(_132,_12U,_13h,_13c,_13d,function(_13j,_13k,_13l){return new F(function(){return A(_13c,[_13j,_13k,new T(function(){return B(_PL(_13i,_13l));})]);});},function(_13m){return new F(function(){return A(_13d,[new T(function(){return B(_PL(_13i,_13m));})]);});});});},_13d,function(_13n,_13o,_13p){return new F(function(){return _Z3(_132,_12U,_13o,_13c,_13d,function(_13q,_13r,_13s){return new F(function(){return A(_13e,[_13q,_13r,new T(function(){return B(_PL(_13p,_13s));})]);});},function(_13t){return new F(function(){return A(_13f,[new T(function(){return B(_PL(_13p,_13t));})]);});});});},_13f]);});},_13u=[0,_XG,_9],_13v=[0,_9,1,1],_13w=function(_13x){return E(_13x);},_13y=new T(function(){return B(_tA("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_13z=new T(function(){return B(_tA("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_13A=[0,_S7,_13z,_13w,_13y],_13B=function(_13C){return new F(function(){return unAppCStr("string error",new T(function(){return B(_mG(_13C));}));});},_13D=function(_13E,_13F,_13G,_13H,_13I){return new F(function(){return A(_10y,[_13F,function(_13J,_13K,_13L){return new F(function(){return A(_13G,[_13E,_13K,new T(function(){var _13M=E(E(_13K)[2]),_13N=E(_13L),_13O=E(_13N[1]),_13P=B(_P1(_13O[1],_13O[2],_13O[3],_13N[2],_13M[1],_13M[2],_13M[3],_9));return [0,E(_13P[1]),_13P[2]];})]);});},_13I,function(_13Q,_13R,_13S){return new F(function(){return A(_13H,[_13E,_13R,new T(function(){var _13T=E(E(_13R)[2]),_13U=E(_13S),_13V=E(_13U[1]),_13W=B(_P1(_13V[1],_13V[2],_13V[3],_13U[2],_13T[1],_13T[2],_13T[3],_9));return [0,E(_13W[1]),_13W[2]];})]);});},_13I]);});},_13X=function(_13Y,_13Z,_140,_141,_142){return new F(function(){return A(_Z2,[_13Y,function(_143,_144,_145){return new F(function(){return _13D(_143,_144,_13Z,function(_146,_147,_148){return new F(function(){return A(_13Z,[_146,_147,new T(function(){return B(_PL(_145,_148));})]);});},function(_149){return new F(function(){return A(_140,[new T(function(){return B(_PL(_145,_149));})]);});});});},_140,function(_14a,_14b,_14c){return new F(function(){return _13D(_14a,_14b,_13Z,function(_14d,_14e,_14f){return new F(function(){return A(_141,[_14d,_14e,new T(function(){return B(_PL(_14c,_14f));})]);});},function(_14g){return new F(function(){return A(_142,[new T(function(){return B(_PL(_14c,_14g));})]);});});});},_142]);});},_14h=function(_14i,_14j,_14k,_14l,_14m){return new F(function(){return _13X(_14i,_14j,_14k,_14l,function(_14n){var _14o=E(_14i),_14p=E(_14o[2]),_14q=E(_14o[1]);return _14q[0]==0?B(A(_14m,[new T(function(){var _14r=E(_14n),_14s=E(_14r[1]),_14t=B(_P1(_14s[1],_14s[2],_14s[3],_14r[2],_14p[1],_14p[2],_14p[3],_11Q));return [0,E(_14t[1]),_14t[2]];})])):B(A(_14j,[_14q[1],[0,_14q[2],E(_14p),E(_14o[3])],[0,E(_14p),_9]]));});});},_14u=function(_14v,_14w,_14x,_14y,_14z){return new F(function(){return _Pj(_14h,_14v,_14w,_14x,_14y);});},_14A=function(_14B,_14C,_14D){return [0,_14B,E(E(_14C)),_14D];},_14E=function(_14F,_14G,_14H){var _14I=new T(function(){return B(_Uu(_14F));}),_14J=new T(function(){return B(_Uu(_14F));});return new F(function(){return A(_14G,[_14H,function(_14K,_14L,_14M){return new F(function(){return A(_14I,[[0,new T(function(){return B(A(_14J,[new T(function(){return B(_14A(_14K,_14L,_14M));})]));})]]);});},function(_14N){return new F(function(){return A(_14I,[[0,new T(function(){return B(A(_14J,[[1,_14N]]));})]]);});},function(_14O,_14P,_14Q){return new F(function(){return A(_14I,[new T(function(){return [1,E(B(A(_14J,[new T(function(){return B(_14A(_14O,_14P,_14Q));})])))];})]);});},function(_14R){return new F(function(){return A(_14I,[new T(function(){return [1,E(B(A(_14J,[[1,_14R]])))];})]);});}]);});},_14S=function(_14T){return function(_14U,_14V,_14W,_14X,_14Y){return new F(function(){return A(_14X,[new T(function(){var _14Z=B(_14E(_13A,_150,[0,new T(function(){var _151=B(_14E(_13A,_14u,[0,_14T,E(_13v),E(_1x)]));if(!_151[0]){var _152=E(_151[1]),_153=_152[0]==0?E(_152[1]):B(_13B(_152[1]));}else{var _154=E(_151[1]),_153=_154[0]==0?E(_154[1]):B(_13B(_154[1]));}return _153;}),E(_13v),E(_1x)]));if(!_14Z[0]){var _155=E(_14Z[1]),_156=_155[0]==0?E(_155[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_mG(_155[1]));})));})],_9],_9],_13u];}else{var _157=E(_14Z[1]),_156=_157[0]==0?E(_157[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_mG(_157[1]));})));})],_9],_9],_13u];}return _156;}),_14U,new T(function(){return [0,E(E(_14U)[2]),_9];})]);});};},_158=function(_159,_15a,_15b,_15c,_15d){return new F(function(){return _13a(_159,function(_15e,_15f,_15g){return new F(function(){return A(_14S,[_15e,_15f,_15a,_15b,function(_15h,_15i,_15j){return new F(function(){return A(_15a,[_15h,_15i,new T(function(){return B(_PL(_15g,_15j));})]);});},function(_15k){return new F(function(){return A(_15b,[new T(function(){return B(_PL(_15g,_15k));})]);});}]);});},_15b,function(_15l,_15m,_15n){return new F(function(){return A(_14S,[_15l,_15m,_15a,_15b,function(_15o,_15p,_15q){return new F(function(){return A(_15c,[_15o,_15p,new T(function(){return B(_PL(_15n,_15q));})]);});},function(_15r){return new F(function(){return A(_15d,[new T(function(){return B(_PL(_15n,_15r));})]);});}]);});},_15d);});},_15s=function(_15t,_15u,_15v,_15w,_15x,_15y){var _15z=function(_15A,_15B,_15C,_15D,_15E){var _15F=function(_15G,_15H,_15I,_15J,_15K){return new F(function(){return A(_15D,[[0,[1,[0,_15t,_15H,_15I]],_15G],_15J,new T(function(){var _15L=E(_15K),_15M=E(_15L[1]),_15N=E(E(_15J)[2]),_15O=B(_P1(_15M[1],_15M[2],_15M[3],_15L[2],_15N[1],_15N[2],_15N[3],_9));return [0,E(_15O[1]),_15O[2]];})]);});},_15P=function(_15Q){return new F(function(){return _15F(_9,_XG,_9,_15A,new T(function(){var _15R=E(E(_15A)[2]),_15S=E(_15Q),_15T=E(_15S[1]),_15U=B(_P1(_15T[1],_15T[2],_15T[3],_15S[2],_15R[1],_15R[2],_15R[3],_9));return [0,E(_15U[1]),_15U[2]];}));});};return new F(function(){return _158(_15A,function(_15V,_15W,_15X){var _15Y=E(_15V),_15Z=E(_15Y[2]);return new F(function(){return A(_15B,[[0,[1,[0,_15t,_15Z[1],_15Z[2]]],_15Y[1]],_15W,new T(function(){var _160=E(_15X),_161=E(_160[1]),_162=E(E(_15W)[2]),_163=B(_P1(_161[1],_161[2],_161[3],_160[2],_162[1],_162[2],_162[3],_9));return [0,E(_163[1]),_163[2]];})]);});},_15P,function(_164,_165,_166){var _167=E(_164),_168=E(_167[2]);return new F(function(){return _15F(_167[1],_168[1],_168[2],_165,_166);});},_15P);});};return new F(function(){return A(_Z2,[_15u,function(_169,_16a,_16b){return new F(function(){return _15z(_16a,_15v,_15w,function(_16c,_16d,_16e){return new F(function(){return A(_15v,[_16c,_16d,new T(function(){return B(_PL(_16b,_16e));})]);});},function(_16f){return new F(function(){return A(_15w,[new T(function(){return B(_PL(_16b,_16f));})]);});});});},_15w,function(_16g,_16h,_16i){return new F(function(){return _15z(_16h,_15v,_15w,function(_16j,_16k,_16l){return new F(function(){return A(_15x,[_16j,_16k,new T(function(){return B(_PL(_16i,_16l));})]);});},function(_16m){return new F(function(){return A(_15y,[new T(function(){return B(_PL(_16i,_16m));})]);});});});},_15y]);});},_16n=new T(function(){return B(unCStr(" associative operator"));}),_16o=function(_16p,_16q){var _16r=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_16p,_16n));}))))];}),_9];return function(_16s,_16t,_16u,_16v,_16w){return new F(function(){return A(_16q,[_16s,function(_16x,_16y,_16z){return new F(function(){return A(_16w,[new T(function(){var _16A=E(E(_16y)[2]),_16B=E(_16z),_16C=E(_16B[1]),_16D=B(_P1(_16C[1],_16C[2],_16C[3],_16B[2],_16A[1],_16A[2],_16A[3],_16r));return [0,E(_16D[1]),_16D[2]];})]);});},_16w,function(_16E,_16F,_16G){return new F(function(){return A(_16w,[new T(function(){var _16H=E(E(_16F)[2]),_16I=E(_16G),_16J=E(_16I[1]),_16K=B(_P1(_16J[1],_16J[2],_16J[3],_16I[2],_16H[1],_16H[2],_16H[3],_16r));return [0,E(_16K[1]),_16K[2]];})]);});},_16w]);});};},_16L=function(_16M,_16N,_16O,_16P,_16Q,_16R){var _16S=E(_16M);if(!_16S[0]){return new F(function(){return A(_16R,[new T(function(){return [0,E(E(_16N)[2]),_9];})]);});}else{return new F(function(){return A(_16S[1],[_16N,_16O,_16P,_16Q,function(_16T){return new F(function(){return _16L(_16S[2],_16N,_16O,_16P,function(_16U,_16V,_16W){return new F(function(){return A(_16Q,[_16U,_16V,new T(function(){return B(_PL(_16T,_16W));})]);});},function(_16X){return new F(function(){return A(_16R,[new T(function(){return B(_PL(_16T,_16X));})]);});});});}]);});}},_16Y=new T(function(){return B(unCStr("right"));}),_16Z=new T(function(){return B(unCStr("left"));}),_170=new T(function(){return B(unCStr("non"));}),_171=new T(function(){return B(unCStr("operator"));}),_172=[1,_171,_9],_173=[1,_9,_9],_174=function(_175){var _176=E(_175);if(!_176[0]){return [0,_9,_9,_9,_9,_9];}else{var _177=_176[2],_178=E(_176[1]);switch(_178[0]){case 0:var _179=_178[1],_17a=B(_174(_177)),_17b=_17a[1],_17c=_17a[2],_17d=_17a[3],_17e=_17a[4],_17f=_17a[5];switch(E(_178[2])){case 0:return [0,_17b,_17c,[1,_179,_17d],_17e,_17f];case 1:return [0,_17b,[1,_179,_17c],_17d,_17e,_17f];default:return [0,[1,_179,_17b],_17c,_17d,_17e,_17f];}break;case 1:var _17g=B(_174(_177));return [0,_17g[1],_17g[2],_17g[3],[1,_178[1],_17g[4]],_17g[5]];default:var _17h=B(_174(_177));return [0,_17h[1],_17h[2],_17h[3],_17h[4],[1,_178[1],_17h[5]]];}}},_17i=function(_17j,_17k){while(1){var _17l=(function(_17m,_17n){var _17o=E(_17n);if(!_17o[0]){return E(_17m);}else{var _17p=new T(function(){var _17q=B(_174(_17o[1]));return [0,_17q[1],_17q[2],_17q[3],_17q[4],_17q[5]];}),_17r=new T(function(){return E(E(_17p)[2]);}),_17s=new T(function(){return B(_16o(_16Z,function(_17t,_17u,_17v,_17w,_17x){return new F(function(){return _16L(_17r,_17t,_17u,_17v,_17w,_17x);});}));}),_17y=new T(function(){return E(E(_17p)[1]);}),_17z=new T(function(){return E(E(_17p)[3]);}),_17A=new T(function(){return B(_16o(_170,function(_17B,_17C,_17D,_17E,_17F){return new F(function(){return _16L(_17z,_17B,_17C,_17D,_17E,_17F);});}));}),_17G=function(_17H,_17I,_17J,_17K,_17L,_17M){var _17N=function(_17O,_17P,_17Q,_17R,_17S){var _17T=new T(function(){return B(A(_17H,[_17O]));});return new F(function(){return _16L(new T(function(){return E(E(_17p)[5]);}),_17P,function(_17U,_17V,_17W){return new F(function(){return A(_17Q,[new T(function(){return B(A(_17U,[_17T]));}),_17V,new T(function(){var _17X=E(E(_17V)[2]),_17Y=E(_17W),_17Z=E(_17Y[1]),_180=B(_P1(_17Z[1],_17Z[2],_17Z[3],_17Y[2],_17X[1],_17X[2],_17X[3],_9));return [0,E(_180[1]),_180[2]];})]);});},_17R,function(_181,_182,_183){return new F(function(){return A(_17S,[new T(function(){return B(A(_181,[_17T]));}),_182,new T(function(){var _184=E(E(_182)[2]),_185=_184[1],_186=_184[2],_187=_184[3],_188=E(_183),_189=E(_188[1]),_18a=_189[2],_18b=_189[3],_18c=E(_188[2]);if(!_18c[0]){switch(B(_OT(_189[1],_185))){case 0:var _18d=[0,E(_184),_9];break;case 1:if(_18a>=_186){if(_18a!=_186){var _18e=[0,E(_189),_9];}else{if(_18b>=_187){var _18f=_18b!=_187?[0,E(_189),_9]:[0,E(_189),_P0];}else{var _18f=[0,E(_184),_9];}var _18g=_18f,_18e=_18g;}var _18h=_18e,_18i=_18h;}else{var _18i=[0,E(_184),_9];}var _18j=_18i,_18d=_18j;break;default:var _18d=[0,E(_189),_9];}var _18k=_18d;}else{var _18l=B(_US(_189,_18c,_173)),_18m=E(_18l[1]),_18n=B(_P1(_18m[1],_18m[2],_18m[3],_18l[2],_185,_186,_187,_9)),_18k=[0,E(_18n[1]),_18n[2]];}var _18o=_18k,_18p=_18o,_18q=_18p,_18r=_18q;return _18r;})]);});},function(_18s){return new F(function(){return A(_17S,[_17T,_17P,new T(function(){var _18t=E(E(_17P)[2]),_18u=_18t[1],_18v=_18t[2],_18w=_18t[3],_18x=E(_18s),_18y=B(_US(_18x[1],_18x[2],_173)),_18z=E(_18y[1]),_18A=B(_P1(_18z[1],_18z[2],_18z[3],_18y[2],_18u,_18v,_18w,_9)),_18B=E(_18A[1]),_18C=B(_P1(_18B[1],_18B[2],_18B[3],_18A[2],_18u,_18v,_18w,_9));return [0,E(_18C[1]),_18C[2]];})]);});});});};return new F(function(){return A(_17m,[_17I,function(_18D,_18E,_18F){return new F(function(){return _17N(_18D,_18E,_17J,_17K,function(_18G,_18H,_18I){return new F(function(){return A(_17J,[_18G,_18H,new T(function(){return B(_PL(_18F,_18I));})]);});});});},_17K,function(_18J,_18K,_18L){return new F(function(){return _17N(_18J,_18K,_17J,_17K,function(_18M,_18N,_18O){return new F(function(){return A(_17L,[_18M,_18N,new T(function(){return B(_PL(_18L,_18O));})]);});});});},_17M]);});},_18P=function(_18Q,_18R,_18S,_18T,_18U){var _18V=function(_18W,_18X,_18Y){return new F(function(){return _17G(_18W,_18X,_18R,_18S,function(_18Z,_190,_191){return new F(function(){return A(_18T,[_18Z,_190,new T(function(){return B(_PL(_18Y,_191));})]);});},function(_192){return new F(function(){return A(_18U,[new T(function(){return B(_PL(_18Y,_192));})]);});});});};return new F(function(){return _16L(new T(function(){return E(E(_17p)[4]);}),_18Q,function(_193,_194,_195){return new F(function(){return _17G(_193,_194,_18R,_18S,function(_196,_197,_198){return new F(function(){return A(_18R,[_196,_197,new T(function(){return B(_PL(_195,_198));})]);});},function(_199){return new F(function(){return A(_18S,[new T(function(){return B(_PL(_195,_199));})]);});});});},_18S,function(_19a,_19b,_19c){return new F(function(){return _18V(_19a,_19b,new T(function(){var _19d=E(_19c),_19e=E(_19d[2]);if(!_19e[0]){var _19f=E(_19d);}else{var _19g=B(_US(_19d[1],_19e,_173)),_19f=[0,E(_19g[1]),_19g[2]];}var _19h=_19f;return _19h;}));});},function(_19i){return new F(function(){return _18V(_5n,_18Q,new T(function(){var _19j=E(E(_18Q)[2]),_19k=E(_19i),_19l=B(_US(_19k[1],_19k[2],_173)),_19m=E(_19l[1]),_19n=B(_P1(_19m[1],_19m[2],_19m[3],_19l[2],_19j[1],_19j[2],_19j[3],_9));return [0,E(_19n[1]),_19n[2]];}));});});});},_19o=function(_19p,_19q,_19r,_19s,_19t,_19u){var _19v=function(_19w){return new F(function(){return A(_17s,[_19q,_19r,_19s,function(_19x,_19y,_19z){return new F(function(){return A(_19t,[_19x,_19y,new T(function(){return B(_PL(_19w,_19z));})]);});},function(_19A){return new F(function(){return A(_17A,[_19q,_19r,_19s,function(_19B,_19C,_19D){return new F(function(){return A(_19t,[_19B,_19C,new T(function(){var _19E=E(_19w),_19F=E(_19E[1]),_19G=E(_19A),_19H=E(_19G[1]),_19I=E(_19D),_19J=E(_19I[1]),_19K=B(_P1(_19H[1],_19H[2],_19H[3],_19G[2],_19J[1],_19J[2],_19J[3],_19I[2])),_19L=E(_19K[1]),_19M=B(_P1(_19F[1],_19F[2],_19F[3],_19E[2],_19L[1],_19L[2],_19L[3],_19K[2]));return [0,E(_19M[1]),_19M[2]];})]);});},function(_19N){return new F(function(){return A(_19u,[new T(function(){var _19O=E(_19w),_19P=E(_19O[1]),_19Q=E(_19A),_19R=E(_19Q[1]),_19S=E(_19N),_19T=E(_19S[1]),_19U=B(_P1(_19R[1],_19R[2],_19R[3],_19Q[2],_19T[1],_19T[2],_19T[3],_19S[2])),_19V=E(_19U[1]),_19W=B(_P1(_19P[1],_19P[2],_19P[3],_19O[2],_19V[1],_19V[2],_19V[3],_19U[2]));return [0,E(_19W[1]),_19W[2]];})]);});}]);});}]);});},_19X=function(_19Y,_19Z,_1a0,_1a1,_1a2,_1a3){var _1a4=function(_1a5,_1a6,_1a7){return new F(function(){return A(_1a0,[new T(function(){return B(A(_19Y,[_19p,_1a5]));}),_1a6,new T(function(){var _1a8=E(E(_1a6)[2]),_1a9=E(_1a7),_1aa=E(_1a9[1]),_1ab=B(_P1(_1aa[1],_1aa[2],_1aa[3],_1a9[2],_1a8[1],_1a8[2],_1a8[3],_9));return [0,E(_1ab[1]),_1ab[2]];})]);});};return new F(function(){return _18P(_19Z,function(_1ac,_1ad,_1ae){return new F(function(){return _19o(_1ac,_1ad,_1a4,_1a1,function(_1af,_1ag,_1ah){return new F(function(){return _1a4(_1af,_1ag,new T(function(){var _1ai=E(_1ae),_1aj=E(_1ai[1]),_1ak=E(_1ah),_1al=E(_1ak[1]),_1am=B(_P1(_1aj[1],_1aj[2],_1aj[3],_1ai[2],_1al[1],_1al[2],_1al[3],_1ak[2]));return [0,E(_1am[1]),_1am[2]];},1));});},function(_1an){return new F(function(){return _1a4(_1ac,_1ad,new T(function(){var _1ao=E(E(_1ad)[2]),_1ap=E(_1ae),_1aq=E(_1ap[1]),_1ar=E(_1an),_1as=E(_1ar[1]),_1at=B(_P1(_1as[1],_1as[2],_1as[3],_1ar[2],_1ao[1],_1ao[2],_1ao[3],_9)),_1au=E(_1at[1]),_1av=B(_P1(_1aq[1],_1aq[2],_1aq[3],_1ap[2],_1au[1],_1au[2],_1au[3],_1at[2]));return [0,E(_1av[1]),_1av[2]];},1));});});});},_1a1,function(_1aw,_1ax,_1ay){var _1az=function(_1aA,_1aB,_1aC){return new F(function(){return A(_1a2,[new T(function(){return B(A(_19Y,[_19p,_1aA]));}),_1aB,new T(function(){var _1aD=E(E(_1aB)[2]),_1aE=E(_1ay),_1aF=E(_1aE[1]),_1aG=E(_1aC),_1aH=E(_1aG[1]),_1aI=B(_P1(_1aF[1],_1aF[2],_1aF[3],_1aE[2],_1aH[1],_1aH[2],_1aH[3],_1aG[2])),_1aJ=E(_1aI[1]),_1aK=B(_P1(_1aJ[1],_1aJ[2],_1aJ[3],_1aI[2],_1aD[1],_1aD[2],_1aD[3],_9));return [0,E(_1aK[1]),_1aK[2]];})]);});};return new F(function(){return _19o(_1aw,_1ax,_1a4,_1a1,_1az,function(_1aL){return new F(function(){return _1az(_1aw,_1ax,new T(function(){var _1aM=E(E(_1ax)[2]),_1aN=E(_1aL),_1aO=E(_1aN[1]),_1aP=B(_P1(_1aO[1],_1aO[2],_1aO[3],_1aN[2],_1aM[1],_1aM[2],_1aM[3],_9));return [0,E(_1aP[1]),_1aP[2]];},1));});});});},_1a3);});};return new F(function(){return _16L(_17y,_19q,function(_1aQ,_1aR,_1aS){return new F(function(){return _19X(_1aQ,_1aR,_19r,_19s,function(_1aT,_1aU,_1aV){return new F(function(){return A(_19r,[_1aT,_1aU,new T(function(){return B(_PL(_1aS,_1aV));})]);});},function(_1aW){return new F(function(){return A(_19s,[new T(function(){return B(_PL(_1aS,_1aW));})]);});});});},_19s,function(_1aX,_1aY,_1aZ){return new F(function(){return _19X(_1aX,_1aY,_19r,_19s,function(_1b0,_1b1,_1b2){return new F(function(){return A(_19t,[_1b0,_1b1,new T(function(){return B(_PL(_1aZ,_1b2));})]);});},function(_1b3){return new F(function(){return _19v(new T(function(){return B(_PL(_1aZ,_1b3));}));});});});},_19v);});},_1b4=new T(function(){return B(_16o(_16Y,function(_1b5,_1b6,_1b7,_1b8,_1b9){return new F(function(){return _16L(_17y,_1b5,_1b6,_1b7,_1b8,_1b9);});}));}),_1ba=function(_1bb,_1bc,_1bd,_1be,_1bf,_1bg){var _1bh=function(_1bi){return new F(function(){return A(_1b4,[_1bc,_1bd,_1be,function(_1bj,_1bk,_1bl){return new F(function(){return A(_1bf,[_1bj,_1bk,new T(function(){return B(_PL(_1bi,_1bl));})]);});},function(_1bm){return new F(function(){return A(_17A,[_1bc,_1bd,_1be,function(_1bn,_1bo,_1bp){return new F(function(){return A(_1bf,[_1bn,_1bo,new T(function(){var _1bq=E(_1bi),_1br=E(_1bq[1]),_1bs=E(_1bm),_1bt=E(_1bs[1]),_1bu=E(_1bp),_1bv=E(_1bu[1]),_1bw=B(_P1(_1bt[1],_1bt[2],_1bt[3],_1bs[2],_1bv[1],_1bv[2],_1bv[3],_1bu[2])),_1bx=E(_1bw[1]),_1by=B(_P1(_1br[1],_1br[2],_1br[3],_1bq[2],_1bx[1],_1bx[2],_1bx[3],_1bw[2]));return [0,E(_1by[1]),_1by[2]];})]);});},function(_1bz){return new F(function(){return A(_1bg,[new T(function(){var _1bA=E(_1bi),_1bB=E(_1bA[1]),_1bC=E(_1bm),_1bD=E(_1bC[1]),_1bE=E(_1bz),_1bF=E(_1bE[1]),_1bG=B(_P1(_1bD[1],_1bD[2],_1bD[3],_1bC[2],_1bF[1],_1bF[2],_1bF[3],_1bE[2])),_1bH=E(_1bG[1]),_1bI=B(_P1(_1bB[1],_1bB[2],_1bB[3],_1bA[2],_1bH[1],_1bH[2],_1bH[3],_1bG[2]));return [0,E(_1bI[1]),_1bI[2]];})]);});}]);});}]);});},_1bJ=function(_1bK,_1bL,_1bM,_1bN,_1bO,_1bP){var _1bQ=function(_1bR){var _1bS=new T(function(){return B(A(_1bK,[_1bb,_1bR]));});return function(_1bT,_1bU,_1bV,_1bW,_1bX){return new F(function(){return _1ba(_1bS,_1bT,_1bU,_1bV,_1bW,function(_1bY){return new F(function(){return A(_1bW,[_1bS,_1bT,new T(function(){var _1bZ=E(E(_1bT)[2]),_1c0=E(_1bY),_1c1=E(_1c0[1]),_1c2=B(_P1(_1c1[1],_1c1[2],_1c1[3],_1c0[2],_1bZ[1],_1bZ[2],_1bZ[3],_9));return [0,E(_1c2[1]),_1c2[2]];})]);});});});};};return new F(function(){return _18P(_1bL,function(_1c3,_1c4,_1c5){return new F(function(){return A(_1bQ,[_1c3,_1c4,_1bM,_1bN,function(_1c6,_1c7,_1c8){return new F(function(){return A(_1bM,[_1c6,_1c7,new T(function(){return B(_PL(_1c5,_1c8));})]);});},function(_1c9){return new F(function(){return A(_1bN,[new T(function(){return B(_PL(_1c5,_1c9));})]);});}]);});},_1bN,function(_1ca,_1cb,_1cc){return new F(function(){return A(_1bQ,[_1ca,_1cb,_1bM,_1bN,function(_1cd,_1ce,_1cf){return new F(function(){return A(_1bO,[_1cd,_1ce,new T(function(){return B(_PL(_1cc,_1cf));})]);});},function(_1cg){return new F(function(){return A(_1bP,[new T(function(){return B(_PL(_1cc,_1cg));})]);});}]);});},_1bP);});};return new F(function(){return _16L(_17r,_1bc,function(_1ch,_1ci,_1cj){return new F(function(){return _1bJ(_1ch,_1ci,_1bd,_1be,function(_1ck,_1cl,_1cm){return new F(function(){return A(_1bd,[_1ck,_1cl,new T(function(){return B(_PL(_1cj,_1cm));})]);});},function(_1cn){return new F(function(){return A(_1be,[new T(function(){return B(_PL(_1cj,_1cn));})]);});});});},_1be,function(_1co,_1cp,_1cq){return new F(function(){return _1bJ(_1co,_1cp,_1bd,_1be,function(_1cr,_1cs,_1ct){return new F(function(){return A(_1bf,[_1cr,_1cs,new T(function(){return B(_PL(_1cq,_1ct));})]);});},function(_1cu){return new F(function(){return _1bh(new T(function(){return B(_PL(_1cq,_1cu));}));});});});},_1bh);});},_1cv=function(_1cw,_1cx,_1cy,_1cz,_1cA,_1cB){var _1cC=function(_1cD,_1cE,_1cF,_1cG,_1cH,_1cI){var _1cJ=function(_1cK){return function(_1cL,_1cM,_1cN,_1cO,_1cP){return new F(function(){return A(_1b4,[_1cL,_1cM,_1cN,_1cO,function(_1cQ){return new F(function(){return A(_17s,[_1cL,_1cM,_1cN,function(_1cR,_1cS,_1cT){return new F(function(){return A(_1cO,[_1cR,_1cS,new T(function(){return B(_PL(_1cQ,_1cT));})]);});},function(_1cU){return new F(function(){return A(_17A,[_1cL,_1cM,_1cN,function(_1cV,_1cW,_1cX){return new F(function(){return A(_1cO,[_1cV,_1cW,new T(function(){var _1cY=E(_1cQ),_1cZ=E(_1cY[1]),_1d0=E(_1cU),_1d1=E(_1d0[1]),_1d2=E(_1cX),_1d3=E(_1d2[1]),_1d4=B(_P1(_1d1[1],_1d1[2],_1d1[3],_1d0[2],_1d3[1],_1d3[2],_1d3[3],_1d2[2])),_1d5=E(_1d4[1]),_1d6=B(_P1(_1cZ[1],_1cZ[2],_1cZ[3],_1cY[2],_1d5[1],_1d5[2],_1d5[3],_1d4[2]));return [0,E(_1d6[1]),_1d6[2]];})]);});},function(_1d7){return new F(function(){return A(_1cO,[new T(function(){return B(A(_1cD,[_1cw,_1cK]));}),_1cL,new T(function(){var _1d8=E(E(_1cL)[2]),_1d9=E(_1cQ),_1da=E(_1d9[1]),_1db=E(_1cU),_1dc=E(_1db[1]),_1dd=E(_1d7),_1de=E(_1dd[1]),_1df=B(_P1(_1de[1],_1de[2],_1de[3],_1dd[2],_1d8[1],_1d8[2],_1d8[3],_9)),_1dg=E(_1df[1]),_1dh=B(_P1(_1dc[1],_1dc[2],_1dc[3],_1db[2],_1dg[1],_1dg[2],_1dg[3],_1df[2])),_1di=E(_1dh[1]),_1dj=B(_P1(_1da[1],_1da[2],_1da[3],_1d9[2],_1di[1],_1di[2],_1di[3],_1dh[2]));return [0,E(_1dj[1]),_1dj[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _18P(_1cE,function(_1dk,_1dl,_1dm){return new F(function(){return A(_1cJ,[_1dk,_1dl,_1cF,_1cG,function(_1dn,_1do,_1dp){return new F(function(){return A(_1cF,[_1dn,_1do,new T(function(){return B(_PL(_1dm,_1dp));})]);});},function(_1dq){return new F(function(){return A(_1cG,[new T(function(){return B(_PL(_1dm,_1dq));})]);});}]);});},_1cG,function(_1dr,_1ds,_1dt){return new F(function(){return A(_1cJ,[_1dr,_1ds,_1cF,_1cG,function(_1du,_1dv,_1dw){return new F(function(){return A(_1cH,[_1du,_1dv,new T(function(){return B(_PL(_1dt,_1dw));})]);});},function(_1dx){return new F(function(){return A(_1cI,[new T(function(){return B(_PL(_1dt,_1dx));})]);});}]);});},_1cI);});};return new F(function(){return _Vd(function(_1dy,_1dz,_1dA,_1dB,_1dC){return new F(function(){return _19o(_1cw,_1dy,_1dz,_1dA,_1dB,function(_1dD){return new F(function(){return _1ba(_1cw,_1dy,_1dz,_1dA,function(_1dE,_1dF,_1dG){return new F(function(){return A(_1dB,[_1dE,_1dF,new T(function(){return B(_PL(_1dD,_1dG));})]);});},function(_1dH){var _1dI=function(_1dJ){return new F(function(){return A(_1dB,[_1cw,_1dy,new T(function(){var _1dK=E(E(_1dy)[2]),_1dL=E(_1dD),_1dM=E(_1dL[1]),_1dN=E(_1dH),_1dO=E(_1dN[1]),_1dP=E(_1dJ),_1dQ=E(_1dP[1]),_1dR=B(_P1(_1dQ[1],_1dQ[2],_1dQ[3],_1dP[2],_1dK[1],_1dK[2],_1dK[3],_9)),_1dS=E(_1dR[1]),_1dT=B(_P1(_1dO[1],_1dO[2],_1dO[3],_1dN[2],_1dS[1],_1dS[2],_1dS[3],_1dR[2])),_1dU=E(_1dT[1]),_1dV=B(_P1(_1dM[1],_1dM[2],_1dM[3],_1dL[2],_1dU[1],_1dU[2],_1dU[3],_1dT[2]));return [0,E(_1dV[1]),_1dV[2]];})]);});};return new F(function(){return _16L(_17z,_1dy,function(_1dW,_1dX,_1dY){return new F(function(){return _1cC(_1dW,_1dX,_1dz,_1dA,function(_1dZ,_1e0,_1e1){return new F(function(){return A(_1dz,[_1dZ,_1e0,new T(function(){return B(_PL(_1dY,_1e1));})]);});},function(_1e2){return new F(function(){return A(_1dA,[new T(function(){return B(_PL(_1dY,_1e2));})]);});});});},_1dA,function(_1e3,_1e4,_1e5){return new F(function(){return _1cC(_1e3,_1e4,_1dz,_1dA,function(_1e6,_1e7,_1e8){return new F(function(){return A(_1dB,[_1e6,_1e7,new T(function(){var _1e9=E(_1dD),_1ea=E(_1e9[1]),_1eb=E(_1dH),_1ec=E(_1eb[1]),_1ed=E(_1e5),_1ee=E(_1ed[1]),_1ef=E(_1e8),_1eg=E(_1ef[1]),_1eh=B(_P1(_1ee[1],_1ee[2],_1ee[3],_1ed[2],_1eg[1],_1eg[2],_1eg[3],_1ef[2])),_1ei=E(_1eh[1]),_1ej=B(_P1(_1ec[1],_1ec[2],_1ec[3],_1eb[2],_1ei[1],_1ei[2],_1ei[3],_1eh[2])),_1ek=E(_1ej[1]),_1el=B(_P1(_1ea[1],_1ea[2],_1ea[3],_1e9[2],_1ek[1],_1ek[2],_1ek[3],_1ej[2]));return [0,E(_1el[1]),_1el[2]];})]);});},function(_1em){return new F(function(){return _1dI(new T(function(){var _1en=E(_1e5),_1eo=E(_1en[1]),_1ep=E(_1em),_1eq=E(_1ep[1]),_1er=B(_P1(_1eo[1],_1eo[2],_1eo[3],_1en[2],_1eq[1],_1eq[2],_1eq[3],_1ep[2]));return [0,E(_1er[1]),_1er[2]];},1));});});});},_1dI);});});});});});},_172,_1cx,_1cy,_1cz,_1cA,_1cB);});};_17j=function(_1es,_1et,_1eu,_1ev,_1ew){return new F(function(){return _18P(_1es,function(_1ex,_1ey,_1ez){return new F(function(){return _1cv(_1ex,_1ey,_1et,_1eu,function(_1eA,_1eB,_1eC){return new F(function(){return A(_1et,[_1eA,_1eB,new T(function(){return B(_PL(_1ez,_1eC));})]);});},function(_1eD){return new F(function(){return A(_1eu,[new T(function(){return B(_PL(_1ez,_1eD));})]);});});});},_1eu,function(_1eE,_1eF,_1eG){return new F(function(){return _1cv(_1eE,_1eF,_1et,_1eu,function(_1eH,_1eI,_1eJ){return new F(function(){return A(_1ev,[_1eH,_1eI,new T(function(){return B(_PL(_1eG,_1eJ));})]);});},function(_1eK){return new F(function(){return A(_1ew,[new T(function(){return B(_PL(_1eG,_1eK));})]);});});});},_1ew);});};_17k=_17o[2];return null;}})(_17j,_17k);if(_17l!=null){return _17l;}}},_1eL=1,_1eM=function(_1eN){var _1eO=E(_1eN);switch(_1eO){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _1eP=u_iswspace(_1eO),_1eQ=_1eP;return E(_1eQ)==0?false:true;}},_1eR=function(_1eS){return new F(function(){return _1eM(E(_1eS)[1]);});},_1eT=new T(function(){return B(unCStr("white space"));}),_1eU=[1,_1eT,_9],_1eV=new T(function(){return B(unCStr("space"));}),_1eW=[1,_1eV,_9],_1eX=function(_1eY,_1eZ,_1f0,_1f1,_1f2,_1f3,_1f4){return new F(function(){return _Vd(function(_1f5,_1f6,_1f7,_1f8,_1f9){return new F(function(){return _Qw(function(_1fa,_1fb,_1fc,_1fd,_1fe){return new F(function(){return _Vd(function(_1ff,_1fg,_1fh,_1fi,_1fj){var _1fk=E(_1ff),_1fl=E(_1fk[2]);return new F(function(){return _TX(_1eY,_1eZ,_1eR,_1fk[1],_1fl[1],_1fl[2],_1fl[3],_1fk[3],_1fg,_1fj);});},_1eW,_1fa,_1fb,_1fc,_1fd,_1fe);});},_1f5,_1f6,_1f7,_1f8);});},_1eU,_1f0,_1f1,_1f2,_1f3,_1f4);});},_1fm=[1,_],_1fn=function(_1fo,_1fp){return [5,_1fm,_1fo,_1fp];},_1fq=function(_1fr,_1fs,_1ft,_1fu,_1fv){return new F(function(){return _1eX(_S7,_Vw,_1fr,function(_1fw,_1fx,_1fy){return new F(function(){return A(_1fs,[_1fn,_1fx,new T(function(){var _1fz=E(E(_1fx)[2]),_1fA=E(_1fy),_1fB=E(_1fA[1]),_1fC=B(_P1(_1fB[1],_1fB[2],_1fB[3],_1fA[2],_1fz[1],_1fz[2],_1fz[3],_9));return [0,E(_1fC[1]),_1fC[2]];})]);});},_1ft,function(_1fD,_1fE,_1fF){return new F(function(){return A(_1fu,[_1fn,_1fE,new T(function(){var _1fG=E(E(_1fE)[2]),_1fH=E(_1fF),_1fI=E(_1fH[1]),_1fJ=B(_P1(_1fI[1],_1fI[2],_1fI[3],_1fH[2],_1fG[1],_1fG[2],_1fG[3],_9));return [0,E(_1fJ[1]),_1fJ[2]];})]);});},_1fv);});},_1fK=new T(function(){return B(unCStr("/\\"));}),_1fL=[0,8743],_1fM=[1,_1fL,_9],_1fN=function(_1fO){return E(E(_1fO)[1]);},_1fP=function(_1fQ,_1fR,_1fS,_1fT){while(1){var _1fU=E(_1fT);if(!_1fU[0]){return [0,_1fQ,_1fR,_1fS];}else{var _1fV=_1fU[2];switch(E(E(_1fU[1])[1])){case 9:var _1fW=(_1fS+8|0)-B(_Se(_1fS-1|0,8))|0;_1fT=_1fV;_1fS=_1fW;continue;case 10:var _1fX=_1fR+1|0;_1fS=1;_1fT=_1fV;_1fR=_1fX;continue;default:var _1fW=_1fS+1|0;_1fT=_1fV;_1fS=_1fW;continue;}}}},_1fY=function(_1fZ){return E(E(_1fZ)[1]);},_1g0=function(_1g1){return E(E(_1g1)[2]);},_1g2=function(_1g3){return [0,E(E(_1g3)[2]),_9];},_1g4=function(_1g5,_1g6,_1g7,_1g8,_1g9,_1ga,_1gb){var _1gc=E(_1g6);if(!_1gc[0]){return new F(function(){return A(_1ga,[_9,_1g7,new T(function(){return B(_1g2(_1g7));})]);});}else{var _1gd=E(_1g7),_1ge=E(_1gd[2]),_1gf=new T(function(){return B(_1fN(_1g5));}),_1gg=[0,E(_1ge),[1,[2,E([1,_Sa,new T(function(){return B(_TR(_1gc,_Sb));})])],_Sd]],_1gh=[2,E([1,_Sa,new T(function(){return B(_TR(_1gc,_Sb));})])],_1gi=new T(function(){var _1gj=B(_1fP(_1ge[1],_1ge[2],_1ge[3],_1gc));return [0,_1gj[1],_1gj[2],_1gj[3]];}),_1gk=function(_1gl,_1gm){var _1gn=E(_1gl);if(!_1gn[0]){return new F(function(){return A(_1g8,[_1gc,new T(function(){return [0,_1gm,E(E(_1gi)),E(_1gd[3])];}),new T(function(){return [0,E(E(_1gi)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_1fY(_1gf));}),[new T(function(){return B(A(new T(function(){return B(_1g0(_1g5));}),[_1gm]));}),function(_1go){var _1gp=E(_1go);if(!_1gp[0]){return E(new T(function(){return B(A(_1g9,[_1gg]));}));}else{var _1gq=E(_1gp[1]),_1gr=E(_1gq[1]);return E(_1gn[1])[1]!=_1gr[1]?B(A(_1g9,[[0,E(_1ge),[1,_1gh,[1,[0,E([1,_Sa,new T(function(){return B(_TR([1,_1gr,_9],_Sb));})])],_9]]]])):B(_1gk(_1gn[2],_1gq[2]));}}]);});}};return new F(function(){return A(_1fY,[_1gf,new T(function(){return B(A(_1g0,[_1g5,_1gd[1]]));}),function(_1gs){var _1gt=E(_1gs);if(!_1gt[0]){return E(new T(function(){return B(A(_1gb,[_1gg]));}));}else{var _1gu=E(_1gt[1]),_1gv=E(_1gu[1]);return E(_1gc[1])[1]!=_1gv[1]?B(A(_1gb,[[0,E(_1ge),[1,_1gh,[1,[0,E([1,_Sa,new T(function(){return B(_TR([1,_1gv,_9],_Sb));})])],_9]]]])):B(_1gk(_1gc[2],_1gu[2]));}}]);});}},_1gw=function(_1gx,_1gy,_1gz,_1gA,_1gB){var _1gC=function(_1gD,_1gE){return new F(function(){return _1fq(_1gD,_1gy,_1gz,function(_1gF,_1gG,_1gH){return new F(function(){return A(_1gA,[_1gF,_1gG,new T(function(){return B(_PL(_1gE,_1gH));})]);});},function(_1gI){return new F(function(){return A(_1gB,[new T(function(){return B(_PL(_1gE,_1gI));})]);});});});},_1gJ=function(_1gK,_1gL,_1gM){return new F(function(){return (function(_1gN,_1gO){return new F(function(){return _1fq(_1gN,_1gy,_1gz,function(_1gP,_1gQ,_1gR){return new F(function(){return A(_1gy,[_1gP,_1gQ,new T(function(){return B(_PL(_1gO,_1gR));})]);});},function(_1gS){return new F(function(){return A(_1gz,[new T(function(){return B(_PL(_1gO,_1gS));})]);});});});})(_1gL,_1gM);});};return new F(function(){return _1g4(_VX,_1fK,_1gx,_1gJ,_1gz,function(_1gT,_1gU,_1gV){return new F(function(){return _1gC(_1gU,_1gV);});},function(_1gW){return new F(function(){return _1g4(_VX,_1fM,_1gx,_1gJ,_1gz,function(_1gX,_1gY,_1gZ){return new F(function(){return _1gC(_1gY,new T(function(){return B(_PL(_1gW,_1gZ));}));});},function(_1h0){return new F(function(){return A(_1gB,[new T(function(){return B(_PL(_1gW,_1h0));})]);});});});});});},_1h1=function(_1h2,_1h3,_1h4,_1h5,_1h6){return new F(function(){return _1eX(_S7,_Vw,_1h2,function(_1h7,_1h8,_1h9){return new F(function(){return _1gw(_1h8,_1h3,_1h4,function(_1ha,_1hb,_1hc){return new F(function(){return A(_1h3,[_1ha,_1hb,new T(function(){return B(_PL(_1h9,_1hc));})]);});},function(_1hd){return new F(function(){return A(_1h4,[new T(function(){return B(_PL(_1h9,_1hd));})]);});});});},_1h4,function(_1he,_1hf,_1hg){return new F(function(){return _1gw(_1hf,_1h3,_1h4,function(_1hh,_1hi,_1hj){return new F(function(){return A(_1h5,[_1hh,_1hi,new T(function(){return B(_PL(_1hg,_1hj));})]);});},function(_1hk){return new F(function(){return A(_1h6,[new T(function(){return B(_PL(_1hg,_1hk));})]);});});});},_1h6);});},_1hl=function(_1hm,_1hn,_1ho,_1hp,_1hq){return new F(function(){return _1h1(_1hm,_1hn,_1hq,_1hp,_1hq);});},_1hr=[0,_1hl,_1eL],_1hs=[1,_1hr,_9],_1ht=[2,_],_1hu=function(_1fo,_1fp){return [5,_1ht,_1fo,_1fp];},_1hv=function(_1hw,_1hx,_1hy,_1hz,_1hA){return new F(function(){return _1eX(_S7,_Vw,_1hw,function(_1hB,_1hC,_1hD){return new F(function(){return A(_1hx,[_1hu,_1hC,new T(function(){var _1hE=E(E(_1hC)[2]),_1hF=E(_1hD),_1hG=E(_1hF[1]),_1hH=B(_P1(_1hG[1],_1hG[2],_1hG[3],_1hF[2],_1hE[1],_1hE[2],_1hE[3],_9));return [0,E(_1hH[1]),_1hH[2]];})]);});},_1hy,function(_1hI,_1hJ,_1hK){return new F(function(){return A(_1hz,[_1hu,_1hJ,new T(function(){var _1hL=E(E(_1hJ)[2]),_1hM=E(_1hK),_1hN=E(_1hM[1]),_1hO=B(_P1(_1hN[1],_1hN[2],_1hN[3],_1hM[2],_1hL[1],_1hL[2],_1hL[3],_9));return [0,E(_1hO[1]),_1hO[2]];})]);});},_1hA);});},_1hP=new T(function(){return B(unCStr("\\/"));}),_1hQ=[0,8744],_1hR=[1,_1hQ,_9],_1hS=function(_1hT,_1hU,_1hV,_1hW,_1hX){var _1hY=function(_1hZ,_1i0){return new F(function(){return _1hv(_1hZ,_1hU,_1hV,function(_1i1,_1i2,_1i3){return new F(function(){return A(_1hW,[_1i1,_1i2,new T(function(){return B(_PL(_1i0,_1i3));})]);});},function(_1i4){return new F(function(){return A(_1hX,[new T(function(){return B(_PL(_1i0,_1i4));})]);});});});},_1i5=function(_1i6,_1i7,_1i8){return new F(function(){return (function(_1i9,_1ia){return new F(function(){return _1hv(_1i9,_1hU,_1hV,function(_1ib,_1ic,_1id){return new F(function(){return A(_1hU,[_1ib,_1ic,new T(function(){return B(_PL(_1ia,_1id));})]);});},function(_1ie){return new F(function(){return A(_1hV,[new T(function(){return B(_PL(_1ia,_1ie));})]);});});});})(_1i7,_1i8);});};return new F(function(){return _1g4(_VX,_1hP,_1hT,_1i5,_1hV,function(_1if,_1ig,_1ih){return new F(function(){return _1hY(_1ig,_1ih);});},function(_1ii){return new F(function(){return _1g4(_VX,_1hR,_1hT,_1i5,_1hV,function(_1ij,_1ik,_1il){return new F(function(){return _1hY(_1ik,new T(function(){return B(_PL(_1ii,_1il));}));});},function(_1im){return new F(function(){return A(_1hX,[new T(function(){return B(_PL(_1ii,_1im));})]);});});});});});},_1in=function(_1io,_1ip,_1iq,_1ir,_1is){return new F(function(){return _1eX(_S7,_Vw,_1io,function(_1it,_1iu,_1iv){return new F(function(){return _1hS(_1iu,_1ip,_1iq,function(_1iw,_1ix,_1iy){return new F(function(){return A(_1ip,[_1iw,_1ix,new T(function(){return B(_PL(_1iv,_1iy));})]);});},function(_1iz){return new F(function(){return A(_1iq,[new T(function(){return B(_PL(_1iv,_1iz));})]);});});});},_1iq,function(_1iA,_1iB,_1iC){return new F(function(){return _1hS(_1iB,_1ip,_1iq,function(_1iD,_1iE,_1iF){return new F(function(){return A(_1ir,[_1iD,_1iE,new T(function(){return B(_PL(_1iC,_1iF));})]);});},function(_1iG){return new F(function(){return A(_1is,[new T(function(){return B(_PL(_1iC,_1iG));})]);});});});},_1is);});},_1iH=function(_1iI,_1iJ,_1iK,_1iL,_1iM){return new F(function(){return _1in(_1iI,_1iJ,_1iM,_1iL,_1iM);});},_1iN=[0,_1iH,_1eL],_1iO=[1,_1iN,_1hs],_1iP=0,_1iQ=[4,_],_1iR=function(_1fo,_1fp){return [5,_1iQ,_1fo,_1fp];},_1iS=function(_1iT,_1iU,_1iV,_1iW,_1iX){return new F(function(){return _1eX(_S7,_Vw,_1iT,function(_1iY,_1iZ,_1j0){return new F(function(){return A(_1iU,[_1iR,_1iZ,new T(function(){var _1j1=E(E(_1iZ)[2]),_1j2=E(_1j0),_1j3=E(_1j2[1]),_1j4=B(_P1(_1j3[1],_1j3[2],_1j3[3],_1j2[2],_1j1[1],_1j1[2],_1j1[3],_9));return [0,E(_1j4[1]),_1j4[2]];})]);});},_1iV,function(_1j5,_1j6,_1j7){return new F(function(){return A(_1iW,[_1iR,_1j6,new T(function(){var _1j8=E(E(_1j6)[2]),_1j9=E(_1j7),_1ja=E(_1j9[1]),_1jb=B(_P1(_1ja[1],_1ja[2],_1ja[3],_1j9[2],_1j8[1],_1j8[2],_1j8[3],_9));return [0,E(_1jb[1]),_1jb[2]];})]);});},_1iX);});},_1jc=new T(function(){return B(unCStr("<=>"));}),_1jd=[0,8596],_1je=[1,_1jd,_9],_1jf=function(_1jg,_1jh,_1ji,_1jj,_1jk){var _1jl=function(_1jm,_1jn){return new F(function(){return _1iS(_1jm,_1jh,_1ji,function(_1jo,_1jp,_1jq){return new F(function(){return A(_1jj,[_1jo,_1jp,new T(function(){return B(_PL(_1jn,_1jq));})]);});},function(_1jr){return new F(function(){return A(_1jk,[new T(function(){return B(_PL(_1jn,_1jr));})]);});});});},_1js=function(_1jt,_1ju,_1jv){return new F(function(){return (function(_1jw,_1jx){return new F(function(){return _1iS(_1jw,_1jh,_1ji,function(_1jy,_1jz,_1jA){return new F(function(){return A(_1jh,[_1jy,_1jz,new T(function(){return B(_PL(_1jx,_1jA));})]);});},function(_1jB){return new F(function(){return A(_1ji,[new T(function(){return B(_PL(_1jx,_1jB));})]);});});});})(_1ju,_1jv);});};return new F(function(){return _1g4(_VX,_1jc,_1jg,_1js,_1ji,function(_1jC,_1jD,_1jE){return new F(function(){return _1jl(_1jD,_1jE);});},function(_1jF){return new F(function(){return _1g4(_VX,_1je,_1jg,_1js,_1ji,function(_1jG,_1jH,_1jI){return new F(function(){return _1jl(_1jH,new T(function(){return B(_PL(_1jF,_1jI));}));});},function(_1jJ){return new F(function(){return A(_1jk,[new T(function(){return B(_PL(_1jF,_1jJ));})]);});});});});});},_1jK=function(_1jL,_1jM,_1jN,_1jO,_1jP){return new F(function(){return _1eX(_S7,_Vw,_1jL,function(_1jQ,_1jR,_1jS){return new F(function(){return _1jf(_1jR,_1jM,_1jN,function(_1jT,_1jU,_1jV){return new F(function(){return A(_1jM,[_1jT,_1jU,new T(function(){return B(_PL(_1jS,_1jV));})]);});},function(_1jW){return new F(function(){return A(_1jN,[new T(function(){return B(_PL(_1jS,_1jW));})]);});});});},_1jN,function(_1jX,_1jY,_1jZ){return new F(function(){return _1jf(_1jY,_1jM,_1jN,function(_1k0,_1k1,_1k2){return new F(function(){return A(_1jO,[_1k0,_1k1,new T(function(){return B(_PL(_1jZ,_1k2));})]);});},function(_1k3){return new F(function(){return A(_1jP,[new T(function(){return B(_PL(_1jZ,_1k3));})]);});});});},_1jP);});},_1k4=function(_1k5,_1k6,_1k7,_1k8,_1k9){return new F(function(){return _1jK(_1k5,_1k6,_1k9,_1k8,_1k9);});},_1ka=[0,_1k4,_1iP],_1kb=[1,_1ka,_9],_1kc=[3,_],_1kd=function(_1fo,_1fp){return [5,_1kc,_1fo,_1fp];},_1ke=function(_1kf,_1kg,_1kh,_1ki,_1kj){return new F(function(){return _1eX(_S7,_Vw,_1kf,function(_1kk,_1kl,_1km){return new F(function(){return A(_1kg,[_1kd,_1kl,new T(function(){var _1kn=E(E(_1kl)[2]),_1ko=E(_1km),_1kp=E(_1ko[1]),_1kq=B(_P1(_1kp[1],_1kp[2],_1kp[3],_1ko[2],_1kn[1],_1kn[2],_1kn[3],_9));return [0,E(_1kq[1]),_1kq[2]];})]);});},_1kh,function(_1kr,_1ks,_1kt){return new F(function(){return A(_1ki,[_1kd,_1ks,new T(function(){var _1ku=E(E(_1ks)[2]),_1kv=E(_1kt),_1kw=E(_1kv[1]),_1kx=B(_P1(_1kw[1],_1kw[2],_1kw[3],_1kv[2],_1ku[1],_1ku[2],_1ku[3],_9));return [0,E(_1kx[1]),_1kx[2]];})]);});},_1kj);});},_1ky=new T(function(){return B(unCStr("=>"));}),_1kz=[0,8594],_1kA=[1,_1kz,_9],_1kB=function(_1kC,_1kD,_1kE,_1kF,_1kG){var _1kH=function(_1kI,_1kJ){return new F(function(){return _1ke(_1kI,_1kD,_1kE,function(_1kK,_1kL,_1kM){return new F(function(){return A(_1kF,[_1kK,_1kL,new T(function(){return B(_PL(_1kJ,_1kM));})]);});},function(_1kN){return new F(function(){return A(_1kG,[new T(function(){return B(_PL(_1kJ,_1kN));})]);});});});},_1kO=function(_1kP,_1kQ,_1kR){return new F(function(){return (function(_1kS,_1kT){return new F(function(){return _1ke(_1kS,_1kD,_1kE,function(_1kU,_1kV,_1kW){return new F(function(){return A(_1kD,[_1kU,_1kV,new T(function(){return B(_PL(_1kT,_1kW));})]);});},function(_1kX){return new F(function(){return A(_1kE,[new T(function(){return B(_PL(_1kT,_1kX));})]);});});});})(_1kQ,_1kR);});};return new F(function(){return _1g4(_VX,_1ky,_1kC,_1kO,_1kE,function(_1kY,_1kZ,_1l0){return new F(function(){return _1kH(_1kZ,_1l0);});},function(_1l1){return new F(function(){return _1g4(_VX,_1kA,_1kC,_1kO,_1kE,function(_1l2,_1l3,_1l4){return new F(function(){return _1kH(_1l3,new T(function(){return B(_PL(_1l1,_1l4));}));});},function(_1l5){return new F(function(){return A(_1kG,[new T(function(){return B(_PL(_1l1,_1l5));})]);});});});});});},_1l6=function(_1l7,_1l8,_1l9,_1la,_1lb){return new F(function(){return _1eX(_S7,_Vw,_1l7,function(_1lc,_1ld,_1le){return new F(function(){return _1kB(_1ld,_1l8,_1l9,function(_1lf,_1lg,_1lh){return new F(function(){return A(_1l8,[_1lf,_1lg,new T(function(){return B(_PL(_1le,_1lh));})]);});},function(_1li){return new F(function(){return A(_1l9,[new T(function(){return B(_PL(_1le,_1li));})]);});});});},_1l9,function(_1lj,_1lk,_1ll){return new F(function(){return _1kB(_1lk,_1l8,_1l9,function(_1lm,_1ln,_1lo){return new F(function(){return A(_1la,[_1lm,_1ln,new T(function(){return B(_PL(_1ll,_1lo));})]);});},function(_1lp){return new F(function(){return A(_1lb,[new T(function(){return B(_PL(_1ll,_1lp));})]);});});});},_1lb);});},_1lq=function(_1lr,_1ls,_1lt,_1lu,_1lv){return new F(function(){return _1l6(_1lr,_1ls,_1lv,_1lu,_1lv);});},_1lw=[0,_1lq,_1iP],_1lx=[1,_1lw,_1kb],_1ly=[1,_1lx,_9],_1lz=[1,_1iO,_1ly],_1lA=[0,_],_1lB=function(_1fp){return [4,_1lA,_1fp];},_1lC=[0,45],_1lD=[1,_1lC,_9],_1lE=[0,172],_1lF=[1,_1lE,_9],_1lG=function(_1lH,_1lI,_1lJ,_1lK,_1lL){var _1lM=function(_1lN,_1lO,_1lP){return new F(function(){return (function(_1lQ,_1lR){return new F(function(){return A(_1lI,[_1lB,_1lQ,new T(function(){var _1lS=E(E(_1lQ)[2]),_1lT=E(_1lR),_1lU=E(_1lT[1]),_1lV=B(_P1(_1lU[1],_1lU[2],_1lU[3],_1lT[2],_1lS[1],_1lS[2],_1lS[3],_9));return [0,E(_1lV[1]),_1lV[2]];})]);});})(_1lO,_1lP);});};return new F(function(){return _1g4(_VX,_1lD,_1lH,_1lM,_1lJ,function(_1lW,_1lX,_1lY){return new F(function(){return A(_1lK,[_1lB,_1lX,new T(function(){var _1lZ=E(E(_1lX)[2]),_1m0=E(_1lY),_1m1=E(_1m0[1]),_1m2=B(_P1(_1m1[1],_1m1[2],_1m1[3],_1m0[2],_1lZ[1],_1lZ[2],_1lZ[3],_9));return [0,E(_1m2[1]),_1m2[2]];})]);});},function(_1m3){return new F(function(){return _1g4(_VX,_1lF,_1lH,_1lM,_1lJ,function(_1m4,_1m5,_1m6){return new F(function(){return A(_1lK,[_1lB,_1m5,new T(function(){var _1m7=E(E(_1m5)[2]),_1m8=E(_1m3),_1m9=E(_1m8[1]),_1ma=E(_1m6),_1mb=E(_1ma[1]),_1mc=B(_P1(_1m9[1],_1m9[2],_1m9[3],_1m8[2],_1mb[1],_1mb[2],_1mb[3],_1ma[2])),_1md=E(_1mc[1]),_1me=B(_P1(_1md[1],_1md[2],_1md[3],_1mc[2],_1m7[1],_1m7[2],_1m7[3],_9));return [0,E(_1me[1]),_1me[2]];})]);});},function(_1mf){return new F(function(){return A(_1lL,[new T(function(){return B(_PL(_1m3,_1mf));})]);});});});});});},_1mg=function(_1mh,_1mi,_1mj,_1mk,_1ml){return new F(function(){return _1eX(_S7,_Vw,_1mh,function(_1mm,_1mn,_1mo){return new F(function(){return _1lG(_1mn,_1mi,_1mj,function(_1mp,_1mq,_1mr){return new F(function(){return A(_1mi,[_1mp,_1mq,new T(function(){return B(_PL(_1mo,_1mr));})]);});},function(_1ms){return new F(function(){return A(_1mj,[new T(function(){return B(_PL(_1mo,_1ms));})]);});});});},_1mj,function(_1mt,_1mu,_1mv){return new F(function(){return _1lG(_1mu,_1mi,_1mj,function(_1mw,_1mx,_1my){return new F(function(){return A(_1mk,[_1mw,_1mx,new T(function(){return B(_PL(_1mv,_1my));})]);});},function(_1mz){return new F(function(){return A(_1ml,[new T(function(){return B(_PL(_1mv,_1mz));})]);});});});},_1ml);});},_1mA=function(_1mB,_1mC,_1mD,_1mE,_1mF){return new F(function(){return _1mg(_1mB,_1mC,_1mF,_1mE,_1mF);});},_1mG=[1,_1mA],_1mH=[1,_1mG,_9],_1mI=[1,_1mH,_1lz],_1mJ=new T(function(){return B(unCStr("number"));}),_1mK=[1,_1mJ,_9],_1mL=new T(function(){return B(err(_28));}),_1mM=new T(function(){return B(err(_2a));}),_1mN=new T(function(){return B(_dz(_dV,_dm,_e1));}),_1mO=function(_1mP){return function(_1mQ,_1mR,_1mS,_1mT,_1mU){return new F(function(){return A(_1mT,[new T(function(){var _1mV=B(_e9(B(_3u(_1mN,_1mP))));return _1mV[0]==0?E(_1mM):E(_1mV[2])[0]==0?E(_1mV[1]):E(_1mL);}),_1mQ,new T(function(){return [0,E(E(_1mQ)[2]),_9];})]);});};},_1mW=function(_1mX,_1mY,_1mZ,_1n0,_1n1){return new F(function(){return _PT(_VJ,_1mX,function(_1n2,_1n3,_1n4){return new F(function(){return A(_1mO,[_1n2,_1n3,_1mY,_1mZ,function(_1n5,_1n6,_1n7){return new F(function(){return A(_1mY,[_1n5,_1n6,new T(function(){return B(_PL(_1n4,_1n7));})]);});},function(_1n8){return new F(function(){return A(_1mZ,[new T(function(){return B(_PL(_1n4,_1n8));})]);});}]);});},_1mZ,function(_1n9,_1na,_1nb){return new F(function(){return A(_1mO,[_1n9,_1na,_1mY,_1mZ,function(_1nc,_1nd,_1ne){return new F(function(){return A(_1n0,[_1nc,_1nd,new T(function(){return B(_PL(_1nb,_1ne));})]);});},function(_1nf){return new F(function(){return A(_1n1,[new T(function(){return B(_PL(_1nb,_1nf));})]);});}]);});},_1n1);});},_1ng=function(_1nh,_1ni,_1nj,_1nk,_1nl){return new F(function(){return _1mW(_1nh,function(_1nm,_1nn,_1no){return new F(function(){return A(_1ni,[[1,[0,_,_1nm]],_1nn,new T(function(){var _1np=E(E(_1nn)[2]),_1nq=E(_1no),_1nr=E(_1nq[1]),_1ns=B(_P1(_1nr[1],_1nr[2],_1nr[3],_1nq[2],_1np[1],_1np[2],_1np[3],_9));return [0,E(_1ns[1]),_1ns[2]];})]);});},_1nj,function(_1nt,_1nu,_1nv){return new F(function(){return A(_1nk,[[1,[0,_,_1nt]],_1nu,new T(function(){var _1nw=E(E(_1nu)[2]),_1nx=_1nw[1],_1ny=_1nw[2],_1nz=_1nw[3],_1nA=E(_1nv),_1nB=E(_1nA[1]),_1nC=_1nB[2],_1nD=_1nB[3],_1nE=E(_1nA[2]);if(!_1nE[0]){switch(B(_OT(_1nB[1],_1nx))){case 0:var _1nF=[0,E(_1nw),_9];break;case 1:if(_1nC>=_1ny){if(_1nC!=_1ny){var _1nG=[0,E(_1nB),_9];}else{if(_1nD>=_1nz){var _1nH=_1nD!=_1nz?[0,E(_1nB),_9]:[0,E(_1nB),_P0];}else{var _1nH=[0,E(_1nw),_9];}var _1nI=_1nH,_1nG=_1nI;}var _1nJ=_1nG,_1nK=_1nJ;}else{var _1nK=[0,E(_1nw),_9];}var _1nL=_1nK,_1nF=_1nL;break;default:var _1nF=[0,E(_1nB),_9];}var _1nM=_1nF;}else{var _1nN=B(_US(_1nB,_1nE,_1mK)),_1nO=E(_1nN[1]),_1nP=B(_P1(_1nO[1],_1nO[2],_1nO[3],_1nN[2],_1nx,_1ny,_1nz,_9)),_1nM=[0,E(_1nP[1]),_1nP[2]];}var _1nQ=_1nM,_1nR=_1nQ,_1nS=_1nR,_1nT=_1nS;return _1nT;})]);});},function(_1nU){return new F(function(){return A(_1nl,[new T(function(){var _1nV=E(_1nU),_1nW=B(_US(_1nV[1],_1nV[2],_1mK));return [0,E(_1nW[1]),_1nW[2]];})]);});});});},_1nX=new T(function(){return B(unCStr("P_"));}),_1nY=function(_1nZ,_1o0,_1o1,_1o2,_1o3){return new F(function(){return _1g4(_VX,_1nX,_1nZ,function(_1o4,_1o5,_1o6){return new F(function(){return _1ng(_1o5,_1o0,_1o1,function(_1o7,_1o8,_1o9){return new F(function(){return A(_1o0,[_1o7,_1o8,new T(function(){return B(_PL(_1o6,_1o9));})]);});},function(_1oa){return new F(function(){return A(_1o1,[new T(function(){return B(_PL(_1o6,_1oa));})]);});});});},_1o1,function(_1ob,_1oc,_1od){return new F(function(){return _1ng(_1oc,_1o0,_1o1,function(_1oe,_1of,_1og){return new F(function(){return A(_1o2,[_1oe,_1of,new T(function(){return B(_PL(_1od,_1og));})]);});},function(_1oh){return new F(function(){return A(_1o3,[new T(function(){return B(_PL(_1od,_1oh));})]);});});});},_1o3);});},_1oi=[0,41],_1oj=new T(function(){return B(_VY(_VX,_1oi));}),_1ok=function(_1ol,_1om,_1on,_1oo,_1op,_1oq){return new F(function(){return A(_1oj,[_1om,function(_1or,_1os,_1ot){return new F(function(){return A(_1on,[_1ol,_1os,new T(function(){var _1ou=E(E(_1os)[2]),_1ov=E(_1ot),_1ow=E(_1ov[1]),_1ox=B(_P1(_1ow[1],_1ow[2],_1ow[3],_1ov[2],_1ou[1],_1ou[2],_1ou[3],_9));return [0,E(_1ox[1]),_1ox[2]];})]);});},_1oo,function(_1oy,_1oz,_1oA){return new F(function(){return A(_1op,[_1ol,_1oz,new T(function(){var _1oB=E(E(_1oz)[2]),_1oC=E(_1oA),_1oD=E(_1oC[1]),_1oE=B(_P1(_1oD[1],_1oD[2],_1oD[3],_1oC[2],_1oB[1],_1oB[2],_1oB[3],_9));return [0,E(_1oE[1]),_1oE[2]];})]);});},_1oq]);});},_1oF=function(_1oG,_1oH,_1oI,_1oJ,_1oK){return new F(function(){return A(_1oL,[_1oG,function(_1oM,_1oN,_1oO){return new F(function(){return _1ok(_1oM,_1oN,_1oH,_1oI,function(_1oP,_1oQ,_1oR){return new F(function(){return A(_1oH,[_1oP,_1oQ,new T(function(){return B(_PL(_1oO,_1oR));})]);});},function(_1oS){return new F(function(){return A(_1oI,[new T(function(){return B(_PL(_1oO,_1oS));})]);});});});},_1oI,function(_1oT,_1oU,_1oV){return new F(function(){return _1ok(_1oT,_1oU,_1oH,_1oI,function(_1oW,_1oX,_1oY){return new F(function(){return A(_1oJ,[_1oW,_1oX,new T(function(){return B(_PL(_1oV,_1oY));})]);});},function(_1oZ){return new F(function(){return A(_1oK,[new T(function(){return B(_PL(_1oV,_1oZ));})]);});});});},_1oK]);});},_1p0=[0,40],_1p1=new T(function(){return B(_VY(_VX,_1p0));}),_1p2=function(_1p3,_1p4,_1p5,_1p6,_1p7){var _1p8=function(_1p9){return new F(function(){return _1nY(_1p3,_1p4,_1p5,function(_1pa,_1pb,_1pc){return new F(function(){return A(_1p6,[_1pa,_1pb,new T(function(){return B(_PL(_1p9,_1pc));})]);});},function(_1pd){return new F(function(){return A(_1p7,[new T(function(){return B(_PL(_1p9,_1pd));})]);});});});};return new F(function(){return A(_1p1,[_1p3,function(_1pe,_1pf,_1pg){return new F(function(){return _1oF(_1pf,_1p4,_1p5,function(_1ph,_1pi,_1pj){return new F(function(){return A(_1p4,[_1ph,_1pi,new T(function(){return B(_PL(_1pg,_1pj));})]);});},function(_1pk){return new F(function(){return A(_1p5,[new T(function(){return B(_PL(_1pg,_1pk));})]);});});});},_1p5,function(_1pl,_1pm,_1pn){return new F(function(){return _1oF(_1pm,_1p4,_1p5,function(_1po,_1pp,_1pq){return new F(function(){return A(_1p6,[_1po,_1pp,new T(function(){return B(_PL(_1pn,_1pq));})]);});},function(_1pr){return new F(function(){return _1p8(new T(function(){return B(_PL(_1pn,_1pr));}));});});});},_1p8]);});},_1oL=new T(function(){return B(_17i(_1p2,_1mI));}),_1ps=function(_1pt,_1pu,_1pv,_1pw,_1px){return new F(function(){return A(_1oL,[_1pt,function(_1py,_1pz,_1pA){return new F(function(){return _15s(_1py,_1pz,_1pu,_1pv,function(_1pB,_1pC,_1pD){return new F(function(){return A(_1pu,[_1pB,_1pC,new T(function(){return B(_PL(_1pA,_1pD));})]);});},function(_1pE){return new F(function(){return A(_1pv,[new T(function(){return B(_PL(_1pA,_1pE));})]);});});});},_1pv,function(_1pF,_1pG,_1pH){return new F(function(){return _15s(_1pF,_1pG,_1pu,_1pv,function(_1pI,_1pJ,_1pK){return new F(function(){return A(_1pw,[_1pI,_1pJ,new T(function(){return B(_PL(_1pH,_1pK));})]);});},function(_1pL){return new F(function(){return A(_1px,[new T(function(){return B(_PL(_1pH,_1pL));})]);});});});},_1px]);});},_1pM=function(_1pN,_1pO,_1pP,_1pQ,_1pR){return new F(function(){return _Qw(_UC,_1pN,function(_1pS,_1pT,_1pU){return new F(function(){return _1ps(_1pT,_1pO,_1pP,function(_1pV,_1pW,_1pX){return new F(function(){return A(_1pO,[_1pV,_1pW,new T(function(){return B(_PL(_1pU,_1pX));})]);});},function(_1pY){return new F(function(){return A(_1pP,[new T(function(){return B(_PL(_1pU,_1pY));})]);});});});},_1pP,function(_1pZ,_1q0,_1q1){return new F(function(){return _1ps(_1q0,_1pO,_1pP,function(_1q2,_1q3,_1q4){return new F(function(){return A(_1pQ,[_1q2,_1q3,new T(function(){return B(_PL(_1q1,_1q4));})]);});},function(_1q5){return new F(function(){return A(_1pR,[new T(function(){return B(_PL(_1q1,_1q5));})]);});});});});});},_1q6=function(_1q7,_1q8,_1q9,_1qa,_1qb,_1qc,_1qd,_1qe){var _1qf=E(_1q7);if(!_1qf[0]){return new F(function(){return A(_1qe,[[0,E([0,_1q8,_1q9,_1qa]),_Sd]]);});}else{var _1qg=_1qf[1];if(!B(_6X(_4m,_1qg,_Yc))){return new F(function(){return A(_1qe,[[0,E([0,_1q8,_1q9,_1qa]),[1,[0,E([1,_Sa,new T(function(){return B(_TR([1,_1qg,_9],_Sb));})])],_9]]]);});}else{var _1qh=function(_1qi,_1qj,_1qk,_1ql){var _1qm=[0,E([0,_1qi,_1qj,_1qk]),_9],_1qn=[0,E([0,_1qi,_1qj,_1qk]),_P0];return new F(function(){return _Qw(_YK,[0,_1qf[2],E(_1ql),E(_1qb)],function(_1qo,_1qp,_1qq){return new F(function(){return _1pM(_1qp,_1qc,_1qd,function(_1qr,_1qs,_1qt){return new F(function(){return A(_1qc,[_1qr,_1qs,new T(function(){return B(_PL(_1qq,_1qt));})]);});},function(_1qu){return new F(function(){return A(_1qd,[new T(function(){return B(_PL(_1qq,_1qu));})]);});});});},_1qd,function(_1qv,_1qw,_1qx){return new F(function(){return _1pM(_1qw,_1qc,_1qd,function(_1qy,_1qz,_1qA){return new F(function(){return A(_1qc,[_1qy,_1qz,new T(function(){var _1qB=E(_1qx),_1qC=E(_1qB[1]),_1qD=E(_1qA),_1qE=E(_1qD[1]),_1qF=B(_P1(_1qC[1],_1qC[2],_1qC[3],_1qB[2],_1qE[1],_1qE[2],_1qE[3],_1qD[2])),_1qG=E(_1qF[1]),_1qH=_1qG[2],_1qI=_1qG[3],_1qJ=E(_1qF[2]);if(!_1qJ[0]){switch(B(_OT(_1qi,_1qG[1]))){case 0:var _1qK=[0,E(_1qG),_9];break;case 1:if(_1qj>=_1qH){if(_1qj!=_1qH){var _1qL=E(_1qm);}else{if(_1qk>=_1qI){var _1qM=_1qk!=_1qI?E(_1qm):E(_1qn);}else{var _1qM=[0,E(_1qG),_9];}var _1qN=_1qM,_1qL=_1qN;}var _1qO=_1qL,_1qP=_1qO;}else{var _1qP=[0,E(_1qG),_9];}var _1qQ=_1qP,_1qK=_1qQ;break;default:var _1qK=E(_1qm);}var _1qR=_1qK;}else{var _1qR=[0,E(_1qG),_1qJ];}var _1qS=_1qR,_1qT=_1qS,_1qU=_1qT,_1qV=_1qU,_1qW=_1qV,_1qX=_1qW;return _1qX;})]);});},function(_1qY){return new F(function(){return A(_1qd,[new T(function(){var _1qZ=E(_1qx),_1r0=E(_1qZ[1]),_1r1=E(_1qY),_1r2=E(_1r1[1]),_1r3=B(_P1(_1r0[1],_1r0[2],_1r0[3],_1qZ[2],_1r2[1],_1r2[2],_1r2[3],_1r1[2])),_1r4=E(_1r3[1]),_1r5=_1r4[2],_1r6=_1r4[3],_1r7=E(_1r3[2]);if(!_1r7[0]){switch(B(_OT(_1qi,_1r4[1]))){case 0:var _1r8=[0,E(_1r4),_9];break;case 1:if(_1qj>=_1r5){if(_1qj!=_1r5){var _1r9=E(_1qm);}else{if(_1qk>=_1r6){var _1ra=_1qk!=_1r6?E(_1qm):E(_1qn);}else{var _1ra=[0,E(_1r4),_9];}var _1rb=_1ra,_1r9=_1rb;}var _1rc=_1r9,_1rd=_1rc;}else{var _1rd=[0,E(_1r4),_9];}var _1re=_1rd,_1r8=_1re;break;default:var _1r8=E(_1qm);}var _1rf=_1r8;}else{var _1rf=[0,E(_1r4),_1r7];}var _1rg=_1rf,_1rh=_1rg,_1ri=_1rh,_1rj=_1ri,_1rk=_1rj,_1rl=_1rk;return _1rl;})]);});});});});});};switch(E(E(_1qg)[1])){case 9:var _1rm=(_1qa+8|0)-B(_Se(_1qa-1|0,8))|0;return new F(function(){return _1qh(_1q8,_1q9,_1rm,[0,_1q8,_1q9,_1rm]);});break;case 10:var _1rn=_1q9+1|0;return new F(function(){return _1qh(_1q8,_1rn,1,[0,_1q8,_1rn,1]);});break;default:var _1ro=_1qa+1|0;return new F(function(){return _1qh(_1q8,_1q9,_1ro,[0,_1q8,_1q9,_1ro]);});}}}},_1rp=function(_1rq,_1rr){return E(_1);},_1rs=function(_1rt,_1ru,_1rv,_1rw){var _1rx=E(_1rv);switch(_1rx[0]){case 0:var _1ry=E(_1rw);return _1ry[0]==0?E(_1):E(_1ry[1]);case 1:return new F(function(){return A(_1rt,[_1rx[1],_9]);});break;case 2:return new F(function(){return A(_1ru,[_1rx[1],[1,new T(function(){return B(_1rs(_1rt,_1ru,_1rx[2],_1rw));}),_9]]);});break;default:return new F(function(){return A(_1ru,[_1rx[1],[1,new T(function(){return B(_1rs(_1rt,_1ru,_1rx[2],_1rw));}),[1,new T(function(){return B(_1rs(_1rt,_1ru,_1rx[3],_1rw));}),_9]]]);});}},_1rz=function(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rG,_1rH){var _1rI=E(_1rG);switch(_1rI[0]){case 0:return [0];case 1:return new F(function(){return A(_1rD,[_1rI[1],_9]);});break;case 2:return new F(function(){return A(_1rA,[_1rI[1],[1,new T(function(){return B(_1rs(_1rD,_1rE,_1rI[2],_1rH));}),_9]]);});break;case 3:return new F(function(){return A(_1rA,[_1rI[1],[1,new T(function(){return B(_1rs(_1rD,_1rE,_1rI[2],_1rH));}),[1,new T(function(){return B(_1rs(_1rD,_1rE,_1rI[3],_1rH));}),_9]]]);});break;case 4:return new F(function(){return A(_1rB,[_1rI[1],[1,new T(function(){return B(_1rz(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rI[2],_1rH));}),_9]]);});break;case 5:return new F(function(){return A(_1rB,[_1rI[1],[1,new T(function(){return B(_1rz(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rI[2],_1rH));}),[1,new T(function(){return B(_1rz(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,_1rI[3],_1rH));}),_9]]]);});break;default:var _1rJ=_1rI[1],_1rK=_1rI[2];return new F(function(){return A(_1rC,[_1rJ,[1,new T(function(){return B(A(_1rF,[new T(function(){return B(A(_1rK,[_eK]));}),_1rJ]));}),[1,new T(function(){return B(_1rz(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF,B(A(_1rK,[_eK])),[1,new T(function(){return B(A(_1rF,[new T(function(){return B(A(_1rK,[_eK]));}),_1rJ]));}),_9]));}),_9]]]);});}},_1rL=[0,95],_1rM=[1,_1rL,_9],_1rN=[1,_1rM,_9],_1rO=function(_1rP){var _1rQ=function(_1rR){var _1rS=E(new T(function(){var _1rT=B(_14E(_13A,_1oL,[0,_1rP,E(_13v),E(_1x)]));if(!_1rT[0]){var _1rU=E(_1rT[1]),_1rV=_1rU[0]==0?[1,_1rU[1]]:[0,_1rU[1]];}else{var _1rW=E(_1rT[1]),_1rV=_1rW[0]==0?[1,_1rW[1]]:[0,_1rW[1]];}return _1rV;}));return _1rS[0]==0?function(_1rX,_1rY,_1rZ,_1s0,_1s1){return new F(function(){return A(_1s0,[[0,[0,new T(function(){var _1s2=E(_1rS[1]),_1s3=E(_1s2[1]);return B(_mB(_1s3[1],_1s3[2],_1s3[3],_1s2[2]));})],_9],_1rX,new T(function(){return [0,E(E(_1rX)[2]),_9];})]);});}:function(_1s4,_1s5,_1s6,_1s7,_1s8){return new F(function(){return A(_1s7,[[0,[0,new T(function(){return B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_1rS[1],_1rN));})],_9],_1s4,new T(function(){return [0,E(E(_1s4)[2]),_9];})]);});};};return function(_1s9,_1sa,_1sb,_1sc,_1sd){return new F(function(){return A(_Z2,[_1s9,function(_1se,_1sf,_1sg){return new F(function(){return A(_1rQ,[_,_1sf,_1sa,_1sb,function(_1sh,_1si,_1sj){return new F(function(){return A(_1sa,[_1sh,_1si,new T(function(){return B(_PL(_1sg,_1sj));})]);});},function(_1sk){return new F(function(){return A(_1sb,[new T(function(){return B(_PL(_1sg,_1sk));})]);});}]);});},_1sb,function(_1sl,_1sm,_1sn){return new F(function(){return A(_1rQ,[_,_1sm,_1sa,_1sb,function(_1so,_1sp,_1sq){return new F(function(){return A(_1sc,[_1so,_1sp,new T(function(){return B(_PL(_1sn,_1sq));})]);});},function(_1sr){return new F(function(){return A(_1sd,[new T(function(){return B(_PL(_1sn,_1sr));})]);});}]);});},_1sd]);});};},_1ss=function(_1st,_1su,_1sv,_1sw,_1sx,_1sy,_1sz,_1sA,_1sB,_1sC){return new F(function(){return _TX(_1st,_1su,function(_1sD){return !B(_6X(_4m,_1sD,_1sv))?true:false;},_1sw,_1sx,_1sy,_1sz,_1sA,_1sB,_1sC);});},_1sE=[0,9],_1sF=[1,_1sE,_9],_1sG=[0,10],_1sH=[1,_1sG,_1sF],_1sI=function(_1sJ,_1sK,_1sL,_1sM,_1sN){var _1sO=E(_1sJ),_1sP=E(_1sO[2]);return new F(function(){return _1ss(_S7,_UA,_1sH,_1sO[1],_1sP[1],_1sP[2],_1sP[3],_1sO[3],_1sK,_1sN);});},_1sQ=function(_1sR,_1sS,_1sT,_1sU,_1sV){return new F(function(){return _PT(_1sI,_1sR,function(_1sW,_1sX,_1sY){return new F(function(){return A(_1rO,[_1sW,_1sX,_1sS,_1sT,function(_1sZ,_1t0,_1t1){return new F(function(){return A(_1sS,[_1sZ,_1t0,new T(function(){return B(_PL(_1sY,_1t1));})]);});},function(_1t2){return new F(function(){return A(_1sT,[new T(function(){return B(_PL(_1sY,_1t2));})]);});}]);});},_1sT,function(_1t3,_1t4,_1t5){return new F(function(){return A(_1rO,[_1t3,_1t4,_1sS,_1sT,function(_1t6,_1t7,_1t8){return new F(function(){return A(_1sU,[_1t6,_1t7,new T(function(){return B(_PL(_1t5,_1t8));})]);});},function(_1t9){return new F(function(){return A(_1sV,[new T(function(){return B(_PL(_1t5,_1t9));})]);});}]);});},_1sV);});},_1ta=function(_1tb,_1tc,_1td,_1te,_1tf,_1tg){var _1th=function(_1ti,_1tj,_1tk,_1tl,_1tm,_1tn){var _1to=function(_1tp){var _1tq=[0,[1,[0,_1tb,_1ti,new T(function(){return B(_f2(_Wk,_1tp));})]],_9];return function(_1tr,_1ts,_1tt,_1tu,_1tv){return new F(function(){return A(_Z2,[_1tr,function(_1tw,_1tx,_1ty){return new F(function(){return A(_1ts,[_1tq,_1tx,new T(function(){var _1tz=E(E(_1tx)[2]),_1tA=E(_1ty),_1tB=E(_1tA[1]),_1tC=B(_P1(_1tB[1],_1tB[2],_1tB[3],_1tA[2],_1tz[1],_1tz[2],_1tz[3],_9));return [0,E(_1tC[1]),_1tC[2]];})]);});},_1tt,function(_1tD,_1tE,_1tF){return new F(function(){return A(_1tu,[_1tq,_1tE,new T(function(){var _1tG=E(E(_1tE)[2]),_1tH=E(_1tF),_1tI=E(_1tH[1]),_1tJ=B(_P1(_1tI[1],_1tI[2],_1tI[3],_1tH[2],_1tG[1],_1tG[2],_1tG[3],_9));return [0,E(_1tJ[1]),_1tJ[2]];})]);});},_1tv]);});};},_1tK=function(_1tL,_1tM,_1tN,_1tO,_1tP){var _1tQ=function(_1tR,_1tS,_1tT){return new F(function(){return A(_1to,[_1tR,_1tS,_1tM,_1tN,function(_1tU,_1tV,_1tW){return new F(function(){return A(_1tO,[_1tU,_1tV,new T(function(){return B(_PL(_1tT,_1tW));})]);});},function(_1tX){return new F(function(){return A(_1tP,[new T(function(){return B(_PL(_1tT,_1tX));})]);});}]);});},_1tY=function(_1tZ){return new F(function(){return _1tQ(_9,_1tL,new T(function(){var _1u0=E(E(_1tL)[2]),_1u1=E(_1tZ),_1u2=E(_1u1[1]),_1u3=B(_P1(_1u2[1],_1u2[2],_1u2[3],_1u1[2],_1u0[1],_1u0[2],_1u0[3],_9));return [0,E(_1u3[1]),_1u3[2]];}));});};return new F(function(){return _QW(_VP,_Wg,_1tL,function(_1u4,_1u5,_1u6){return new F(function(){return A(_1to,[_1u4,_1u5,_1tM,_1tN,function(_1u7,_1u8,_1u9){return new F(function(){return A(_1tM,[_1u7,_1u8,new T(function(){return B(_PL(_1u6,_1u9));})]);});},function(_1ua){return new F(function(){return A(_1tN,[new T(function(){return B(_PL(_1u6,_1ua));})]);});}]);});},_1tY,_1tQ,_1tY);});};return new F(function(){return _Qw(_UC,_1tj,function(_1ub,_1uc,_1ud){return new F(function(){return _1tK(_1uc,_1tk,_1tl,function(_1ue,_1uf,_1ug){return new F(function(){return A(_1tk,[_1ue,_1uf,new T(function(){return B(_PL(_1ud,_1ug));})]);});},function(_1uh){return new F(function(){return A(_1tl,[new T(function(){return B(_PL(_1ud,_1uh));})]);});});});},_1tl,function(_1ui,_1uj,_1uk){return new F(function(){return _1tK(_1uj,_1tk,_1tl,function(_1ul,_1um,_1un){return new F(function(){return A(_1tm,[_1ul,_1um,new T(function(){return B(_PL(_1uk,_1un));})]);});},function(_1uo){return new F(function(){return A(_1tn,[new T(function(){return B(_PL(_1uk,_1uo));})]);});});});});});},_1up=function(_1uq,_1ur,_1us,_1ut,_1uu){return new F(function(){return _PT(_Xi,_1uq,function(_1uv,_1uw,_1ux){return new F(function(){return _1th(_1uv,_1uw,_1ur,_1us,function(_1uy,_1uz,_1uA){return new F(function(){return A(_1ur,[_1uy,_1uz,new T(function(){return B(_PL(_1ux,_1uA));})]);});},function(_1uB){return new F(function(){return A(_1us,[new T(function(){return B(_PL(_1ux,_1uB));})]);});});});},_1uu,function(_1uC,_1uD,_1uE){return new F(function(){return _1th(_1uC,_1uD,_1ur,_1us,function(_1uF,_1uG,_1uH){return new F(function(){return A(_1ut,[_1uF,_1uG,new T(function(){return B(_PL(_1uE,_1uH));})]);});},function(_1uI){return new F(function(){return A(_1uu,[new T(function(){return B(_PL(_1uE,_1uI));})]);});});});},_1uu);});};return new F(function(){return _Qw(_UC,_1tc,function(_1uJ,_1uK,_1uL){return new F(function(){return _1up(_1uK,_1td,_1te,function(_1uM,_1uN,_1uO){return new F(function(){return A(_1td,[_1uM,_1uN,new T(function(){return B(_PL(_1uL,_1uO));})]);});},function(_1uP){return new F(function(){return A(_1te,[new T(function(){return B(_PL(_1uL,_1uP));})]);});});});},_1te,function(_1uQ,_1uR,_1uS){return new F(function(){return _1up(_1uR,_1td,_1te,function(_1uT,_1uU,_1uV){return new F(function(){return A(_1tf,[_1uT,_1uU,new T(function(){return B(_PL(_1uS,_1uV));})]);});},function(_1uW){return new F(function(){return A(_1tg,[new T(function(){return B(_PL(_1uS,_1uW));})]);});});});});});},_1uX=function(_1uY,_1uZ,_1v0,_1v1,_1v2){return new F(function(){return A(_1oL,[_1uY,function(_1v3,_1v4,_1v5){return new F(function(){return _1ta(_1v3,_1v4,_1uZ,_1v0,function(_1v6,_1v7,_1v8){return new F(function(){return A(_1uZ,[_1v6,_1v7,new T(function(){return B(_PL(_1v5,_1v8));})]);});},function(_1v9){return new F(function(){return A(_1v0,[new T(function(){return B(_PL(_1v5,_1v9));})]);});});});},_1v0,function(_1va,_1vb,_1vc){return new F(function(){return _1ta(_1va,_1vb,_1uZ,_1v0,function(_1vd,_1ve,_1vf){return new F(function(){return A(_1v1,[_1vd,_1ve,new T(function(){return B(_PL(_1vc,_1vf));})]);});},function(_1vg){return new F(function(){return A(_1v2,[new T(function(){return B(_PL(_1vc,_1vg));})]);});});});},_1v2]);});},_1vh=function(_1vi,_1vj,_1vk,_1vl){var _1vm=function(_1vn){var _1vo=E(_1vi),_1vp=E(_1vo[2]),_1vq=function(_1vr){var _1vs=function(_1vt){return new F(function(){return A(_1vl,[new T(function(){var _1vu=E(_1vn),_1vv=E(_1vu[1]),_1vw=E(_1vr),_1vx=E(_1vw[1]),_1vy=E(_1vt),_1vz=E(_1vy[1]),_1vA=B(_P1(_1vx[1],_1vx[2],_1vx[3],_1vw[2],_1vz[1],_1vz[2],_1vz[3],_1vy[2])),_1vB=E(_1vA[1]),_1vC=B(_P1(_1vv[1],_1vv[2],_1vv[3],_1vu[2],_1vB[1],_1vB[2],_1vB[3],_1vA[2]));return [0,E(_1vC[1]),_1vC[2]];})]);});};return new F(function(){return _1sQ(_1vo,_1vj,_1vs,function(_1vD,_1vE,_1vF){return new F(function(){return A(_1vk,[_1vD,_1vE,new T(function(){var _1vG=E(_1vn),_1vH=E(_1vG[1]),_1vI=E(_1vr),_1vJ=E(_1vI[1]),_1vK=E(_1vF),_1vL=E(_1vK[1]),_1vM=B(_P1(_1vJ[1],_1vJ[2],_1vJ[3],_1vI[2],_1vL[1],_1vL[2],_1vL[3],_1vK[2])),_1vN=E(_1vM[1]),_1vO=B(_P1(_1vH[1],_1vH[2],_1vH[3],_1vG[2],_1vN[1],_1vN[2],_1vN[3],_1vM[2]));return [0,E(_1vO[1]),_1vO[2]];})]);});},_1vs);});};return new F(function(){return _1q6(_1vo[1],_1vp[1],_1vp[2],_1vp[3],_1vo[3],_1vj,_1vq,_1vq);});};return new F(function(){return _1uX(_1vi,_1vj,_1vm,_1vk,_1vm);});},_1vP=function(_1vQ,_1vR,_1vS,_1vT,_1vU){return new F(function(){return _1vh(_1vQ,_1vR,_1vT,_1vU);});},_150=function(_1vV,_1vW,_1vX,_1vY,_1vZ){return new F(function(){return _PT(_1vP,_1vV,function(_1w0,_1w1,_1w2){return new F(function(){return _XI(_1w0,_1w1,_1vW,function(_1w3,_1w4,_1w5){return new F(function(){return A(_1vW,[_1w3,_1w4,new T(function(){return B(_PL(_1w2,_1w5));})]);});});});},_1vX,function(_1w6,_1w7,_1w8){return new F(function(){return _XI(_1w6,_1w7,_1vW,function(_1w9,_1wa,_1wb){return new F(function(){return A(_1vY,[_1w9,_1wa,new T(function(){return B(_PL(_1w8,_1wb));})]);});});});},_1vZ);});},_1wc=function(_1wd){var _1we=E(_1wd);return _1we[0]==0?E(_MJ):function(_1wf,_){var _1wg=B(A(new T(function(){var _1wh=E(_1we[1]);return B(_1wi(_1wh[1],_1wh[2]));}),[_1wf,_])),_1wj=_1wg,_1wk=B(A(new T(function(){return B(_1wc(_1we[2]));}),[_1wf,_])),_1wl=_1wk;return _1wf;};},_1wm=function(_1wn,_1wo){return function(_1wp,_){var _1wq=B(A(new T(function(){var _1wr=E(_1wn);return B(_1wi(_1wr[1],_1wr[2]));}),[_1wp,_])),_1ws=_1wq,_1wt=B(A(new T(function(){return B(_1wc(_1wo));}),[_1wp,_])),_1wu=_1wt;return _1wp;};},_1wv=function(_1ww,_1wx){return new F(function(){return _F(0,E(_1ww)[1],_1wx);});},_1wy=function(_1wz){return function(_58,_xf){return new F(function(){return _id(new T(function(){return B(_2J(_1wv,_1wz,_9));}),_58,_xf);});};},_1wA=function(_1wB){return function(_58,_xf){return new F(function(){return _id(new T(function(){return B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_1wB,_1rN));}),_58,_xf);});};},_1wC=new T(function(){return B(unCStr("open"));}),_1wD=new T(function(){return B(unCStr("termination"));}),_1wE=new T(function(){return B(unCStr("closed"));}),_1wF=function(_1wG){var _1wH=E(_1wG);return _1wH[0]==0?E(_MJ):function(_1wI,_){var _1wJ=B(A(new T(function(){var _1wK=E(_1wH[1]);return B(_1wi(_1wK[1],_1wK[2]));}),[_1wI,_])),_1wL=_1wJ,_1wM=B(A(new T(function(){return B(_1wF(_1wH[2]));}),[_1wI,_])),_1wN=_1wM;return _1wI;};},_1wO=function(_1wP,_1wQ){return function(_1wR,_){var _1wS=B(A(new T(function(){var _1wT=E(_1wP);return B(_1wi(_1wT[1],_1wT[2]));}),[_1wR,_])),_1wU=_1wS,_1wV=B(A(new T(function(){return B(_1wF(_1wQ));}),[_1wR,_])),_1wW=_1wV;return _1wR;};},_1wX=new T(function(){return B(unCStr("SHOW"));}),_1wi=function(_1wY,_1wZ){var _1x0=E(_1wY);if(!_1x0[0]){return function(_58,_xf){return new F(function(){return _La(_id,_1x0[1],_58,_xf);});};}else{var _1x1=E(_1x0[1]),_1x2=_1x1[1],_1x3=_1x1[2],_1x4=_1x1[3];if(!B(_4b(_1x3,_1wX))){var _1x5=E(_1wZ);return _1x5[0]==0?function(_58,_xf){return new F(function(){return _La(_j7,function(_1x6,_){var _1x7=B(_iX(_1wA,_1x2,_1x6,_)),_1x8=_1x7,_1x9=B(_iX(_j7,function(_1xa,_){var _1xb=B(_iX(_id,_1x3,_1xa,_)),_1xc=_1xb,_1xd=B(_iX(_1wy,_1x4,_1xa,_)),_1xe=_1xd;return _1xa;},_1x6,_)),_1xf=_1x9;return _1x6;},_58,_xf);});}:function(_58,_xf){return new F(function(){return _La(_j7,function(_1xg,_){var _1xh=B(_iX(_id,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_1x2,_1rN));})));}),_1xg,_)),_1xi=_1xh,_1xj=B(_La(_j7,function(_1xk,_){var _1xl=B(_iX(_j7,new T(function(){return B(_1wm(_1x5[1],_1x5[2]));}),_1xk,_)),_1xm=_1xl,_1xn=B(_La(_j7,function(_1xo,_){var _1xp=B(_iX(_id,_9,_1xo,_)),_1xq=_1xp,_1xr=B(A(_ij,[_5n,_1xq,_KX,_1wD,_])),_1xs=_1xr,_1xt=B(_iX(_j7,function(_1xu,_){var _1xv=B(_iX(_id,_1x3,_1xu,_)),_1xw=_1xv,_1xx=B(_iX(_1wy,_1x4,_1xu,_)),_1xy=_1xx;return _1xu;},_1xo,_)),_1xz=_1xt;return _1xo;},_1xk,_)),_1xA=_1xn;return _1xk;},_1xg,_)),_1xB=_1xj,_1xC=B(A(_ij,[_5n,_1xB,_KX,_1wE,_])),_1xD=_1xC;return _1xg;},_58,_xf);});};}else{var _1xE=E(_1wZ);return _1xE[0]==0?function(_58,_xf){return new F(function(){return _La(_j7,function(_Ms,_){return new F(function(){return _iX(_id,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_1x2,_1rN));})));}),_Ms,_);});},_58,_xf);});}:function(_58,_xf){return new F(function(){return _La(_j7,function(_1xF,_){var _1xG=B(_iX(_id,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_1x2,_1rN));})));}),_1xF,_)),_1xH=_1xG,_1xI=B(_La(_j7,function(_Ms,_){return new F(function(){return _iX(_j7,new T(function(){return B(_1wO(_1xE[1],_1xE[2]));}),_Ms,_);});},_1xF,_)),_1xJ=_1xI,_1xK=B(A(_ij,[_5n,_1xJ,_KX,_1wC,_])),_1xL=_1xK;return _1xF;},_58,_xf);});};}}},_1xM=function(_1xN){var _1xO=E(_1xN);return _1xO[0]==0?E(_MJ):function(_1xP,_){var _1xQ=B(A(new T(function(){var _1xR=E(_1xO[1]);return B(_1wi(_1xR[1],_1xR[2]));}),[_1xP,_])),_1xS=_1xQ,_1xT=B(A(new T(function(){return B(_1xM(_1xO[2]));}),[_1xP,_])),_1xU=_1xT;return _1xP;};},_1xV=[0,10],_1xW=[1,_1xV,_9],_1xX=function(_1xY,_1xZ,_){var _1y0=jsCreateElem(toJSStr(E(_1xY))),_1y1=_1y0,_1y2=jsAppendChild(_1y1,E(_1xZ)[1]);return [0,_1y1];},_1y3=function(_1y4,_1y5,_1y6,_){var _1y7=B(_1xX(_1y4,_1y6,_)),_1y8=_1y7,_1y9=B(A(_1y5,[_1y8,_])),_1ya=_1y9;return _1y8;},_1yb=new T(function(){return B(unCStr("()"));}),_1yc=new T(function(){return B(unCStr("GHC.Tuple"));}),_1yd=new T(function(){return B(unCStr("ghc-prim"));}),_1ye=new T(function(){var _1yf=hs_wordToWord64(2170319554),_1yg=_1yf,_1yh=hs_wordToWord64(26914641),_1yi=_1yh;return [0,_1yg,_1yi,[0,_1yg,_1yi,_1yd,_1yc,_1yb],_9];}),_1yj=function(_1yk){return E(_1ye);},_1yl=new T(function(){return B(unCStr("PerchM"));}),_1ym=new T(function(){return B(unCStr("Haste.Perch"));}),_1yn=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1yo=new T(function(){var _1yp=hs_wordToWord64(3005229400),_1yq=_1yp,_1yr=hs_wordToWord64(2682402736),_1ys=_1yr;return [0,_1yq,_1ys,[0,_1yq,_1ys,_1yn,_1ym,_1yl],_9];}),_1yt=function(_1yu){return E(_1yo);},_1yv=function(_1yw){var _1yx=E(_1yw);if(!_1yx[0]){return [0];}else{var _1yy=E(_1yx[1]);return [1,[0,_1yy[1],_1yy[2]],new T(function(){return B(_1yv(_1yx[2]));})];}},_1yz=function(_1yA,_1yB){var _1yC=E(_1yA);if(!_1yC){return [0,_9,_1yB];}else{var _1yD=E(_1yB);if(!_1yD[0]){return [0,_9,_9];}else{var _1yE=new T(function(){var _1yF=B(_1yz(_1yC-1|0,_1yD[2]));return [0,_1yF[1],_1yF[2]];});return [0,[1,_1yD[1],new T(function(){return E(E(_1yE)[1]);})],new T(function(){return E(E(_1yE)[2]);})];}}},_1yG=[0,120],_1yH=[0,48],_1yI=function(_1yJ){var _1yK=new T(function(){var _1yL=B(_1yz(8,new T(function(){var _1yM=md5(toJSStr(E(_1yJ))),_1yN=_1yM;return fromJSStr(_1yN);})));return [0,_1yL[1],_1yL[2]];}),_1yO=parseInt([0,toJSStr([1,_1yH,[1,_1yG,new T(function(){return E(E(_1yK)[1]);})]])]),_1yP=_1yO,_1yQ=new T(function(){var _1yR=B(_1yz(8,new T(function(){return E(E(_1yK)[2]);})));return [0,_1yR[1],_1yR[2]];}),_1yS=parseInt([0,toJSStr([1,_1yH,[1,_1yG,new T(function(){return E(E(_1yQ)[1]);})]])]),_1yT=_1yS,_1yU=hs_mkWord64(_1yP,_1yT),_1yV=_1yU,_1yW=parseInt([0,toJSStr([1,_1yH,[1,_1yG,new T(function(){return E(B(_1yz(8,new T(function(){return E(E(_1yQ)[2]);})))[1]);})]])]),_1yX=_1yW,_1yY=hs_mkWord64(_1yX,_1yX),_1yZ=_1yY;return [0,_1yV,_1yZ];},_1z0=function(_1z1,_1z2){var _1z3=jsShowI(_1z1),_1z4=_1z3,_1z5=md5(_1z4),_1z6=_1z5;return new F(function(){return _e(fromJSStr(_1z6),new T(function(){var _1z7=jsShowI(_1z2),_1z8=_1z7,_1z9=md5(_1z8),_1za=_1z9;return fromJSStr(_1za);},1));});},_1zb=function(_1zc){var _1zd=E(_1zc);return new F(function(){return _1z0(_1zd[1],_1zd[2]);});},_1ze=function(_1zf,_1zg){return function(_1zh){return E(new T(function(){var _1zi=B(A(_1zf,[_])),_1zj=E(_1zi[3]),_1zk=_1zj[1],_1zl=_1zj[2],_1zm=B(_e(_1zi[4],[1,new T(function(){return B(A(_1zg,[_]));}),_9]));if(!_1zm[0]){var _1zn=[0,_1zk,_1zl,_1zj,_9];}else{var _1zo=B(_1yI(new T(function(){return B(_km(B(_f2(_1zb,[1,[0,_1zk,_1zl],new T(function(){return B(_1yv(_1zm));})]))));},1))),_1zn=[0,_1zo[1],_1zo[2],_1zj,_1zm];}var _1zp=_1zn,_1zq=_1zp;return _1zq;}));};},_1zr=new T(function(){return B(_1ze(_1yt,_1yj));}),_1zs=function(_1zt,_1zu,_1zv,_){var _1zw=E(_1zu),_1zx=B(A(_1zt,[_1zv,_])),_1zy=_1zx,_1zz=B(A(_ij,[_5n,_1zy,_1zw[1],_1zw[2],_])),_1zA=_1zz;return _1zy;},_1zB=function(_1zC,_1zD){while(1){var _1zE=(function(_1zF,_1zG){var _1zH=E(_1zG);if(!_1zH[0]){return E(_1zF);}else{_1zC=function(_1zI,_){return new F(function(){return _1zs(_1zF,_1zH[1],_1zI,_);});};_1zD=_1zH[2];return null;}})(_1zC,_1zD);if(_1zE!=null){return _1zE;}}},_1zJ=new T(function(){return B(unCStr("value"));}),_1zK=new T(function(){return B(unCStr("id"));}),_1zL=new T(function(){return B(unCStr("onclick"));}),_1zM=new T(function(){return B(unCStr("checked"));}),_1zN=[0,_1zM,_9],_1zO=new T(function(){return B(unCStr("type"));}),_1zP=new T(function(){return B(unCStr("input"));}),_1zQ=function(_1zR,_){return new F(function(){return _1xX(_1zP,_1zR,_);});},_1zS=function(_1zT,_1zU,_1zV){return new F(function(){return _1zB(function(_1zI,_){return new F(function(){return _1zs(_1zT,_1zU,_1zI,_);});},_1zV);});},_1zW=function(_1zX,_1zY,_1zZ,_1A0,_1A1){var _1A2=new T(function(){var _1A3=new T(function(){return B(_1zS(_1zQ,[0,_1zO,_1zY],[1,[0,_1zK,_1zX],[1,[0,_1zJ,_1zZ],_9]]));});return !E(_1A0)?E(_1A3):B(_1zS(_1A3,_1zN,_9));}),_1A4=E(_1A1);return _1A4[0]==0?E(_1A2):B(_1zS(_1A2,[0,_1zL,_1A4[1]],_9));},_1A5=new T(function(){return B(unCStr("href"));}),_1A6=[0,97],_1A7=[1,_1A6,_9],_1A8=function(_1A9,_){return new F(function(){return _1xX(_1A7,_1A9,_);});},_1Aa=function(_1Ab,_1Ac){return function(_1Ad,_){var _1Ae=B(A(new T(function(){return B(_1zS(_1A8,[0,_1A5,_1Ab],_9));}),[_1Ad,_])),_1Af=_1Ae,_1Ag=B(A(_1Ac,[_1Af,_])),_1Ah=_1Ag;return _1Af;};},_1Ai=function(_1Aj){return new F(function(){return _1Aa(_1Aj,function(_1zI,_){return new F(function(){return _id(_1Aj,_1zI,_);});});});},_1Ak=new T(function(){return B(unCStr("option"));}),_1Al=function(_1Am,_){return new F(function(){return _1xX(_1Ak,_1Am,_);});},_1An=new T(function(){return B(unCStr("selected"));}),_1Ao=[0,_1An,_9],_1Ap=function(_1Aq,_1Ar,_1As){var _1At=new T(function(){return B(_1zS(_1Al,[0,_1zJ,_1Aq],_9));});if(!E(_1As)){return function(_1Au,_){var _1Av=B(A(_1At,[_1Au,_])),_1Aw=_1Av,_1Ax=B(A(_1Ar,[_1Aw,_])),_1Ay=_1Ax;return _1Aw;};}else{return new F(function(){return _1zS(function(_1Az,_){var _1AA=B(A(_1At,[_1Az,_])),_1AB=_1AA,_1AC=B(A(_1Ar,[_1AB,_])),_1AD=_1AC;return _1AB;},_1Ao,_9);});}},_1AE=function(_1AF,_1AG){return new F(function(){return _1Ap(_1AF,function(_1zI,_){return new F(function(){return _id(_1AF,_1zI,_);});},_1AG);});},_1AH=new T(function(){return B(unCStr("method"));}),_1AI=new T(function(){return B(unCStr("action"));}),_1AJ=new T(function(){return B(unCStr("UTF-8"));}),_1AK=new T(function(){return B(unCStr("acceptCharset"));}),_1AL=[0,_1AK,_1AJ],_1AM=new T(function(){return B(unCStr("form"));}),_1AN=function(_1AO,_){return new F(function(){return _1xX(_1AM,_1AO,_);});},_1AP=function(_1AQ,_1AR,_1AS){return function(_1AT,_){var _1AU=B(A(new T(function(){return B(_1zS(_1AN,_1AL,[1,[0,_1AI,_1AQ],[1,[0,_1AH,_1AR],_9]]));}),[_1AT,_])),_1AV=_1AU,_1AW=B(A(_1AS,[_1AV,_])),_1AX=_1AW;return _1AV;};},_1AY=new T(function(){return B(unCStr("select"));}),_1AZ=function(_1B0,_){return new F(function(){return _1xX(_1AY,_1B0,_);});},_1B1=function(_1B2,_1B3){return function(_1B4,_){var _1B5=B(A(new T(function(){return B(_1zS(_1AZ,[0,_1zK,_1B2],_9));}),[_1B4,_])),_1B6=_1B5,_1B7=B(A(_1B3,[_1B6,_])),_1B8=_1B7;return _1B6;};},_1B9=new T(function(){return B(unCStr("textarea"));}),_1Ba=function(_1Bb,_){return new F(function(){return _1xX(_1B9,_1Bb,_);});},_1Bc=function(_1Bd,_1Be){return function(_1Bf,_){var _1Bg=B(A(new T(function(){return B(_1zS(_1Ba,[0,_1zK,_1Bd],_9));}),[_1Bf,_])),_1Bh=_1Bg,_1Bi=B(_id(_1Be,_1Bh,_)),_1Bj=_1Bi;return _1Bh;};},_1Bk=new T(function(){return B(unCStr("color:red"));}),_1Bl=new T(function(){return B(unCStr("style"));}),_1Bm=[0,_1Bl,_1Bk],_1Bn=[0,98],_1Bo=[1,_1Bn,_9],_1Bp=function(_1Bq){return new F(function(){return _1zS(function(_1Br,_){var _1Bs=B(_1xX(_1Bo,_1Br,_)),_1Bt=_1Bs,_1Bu=B(A(_1Bq,[_1Bt,_])),_1Bv=_1Bu;return _1Bt;},_1Bm,_9);});},_1Bw=function(_1Bx,_1By,_){return new F(function(){return _KJ(_1Bx,_1By,_);});},_1Bz=function(_1BA,_1BB,_1BC,_){var _1BD=B(A(_1BA,[_1BC,_])),_1BE=_1BD,_1BF=B(A(_1BB,[_1BC,_])),_1BG=_1BF;return _1BC;},_1BH=[0,_ix,_1Bz,_1Bw],_1BI=[0,_1BH,_1zr,_id,_id,_1y3,_1Bp,_1Aa,_1Ai,_1zW,_1Bc,_1B1,_1Ap,_1AE,_1AP,_1zB],_1BJ=function(_1BK,_1BL,_){var _1BM=B(A(_1BL,[_])),_1BN=_1BM;return _1BK;},_1BO=function(_1BP,_1BQ,_){var _1BR=B(A(_1BQ,[_])),_1BS=_1BR;return new T(function(){return B(A(_1BP,[_1BS]));});},_1BT=[0,_1BO,_1BJ],_1BU=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1BV=new T(function(){return B(unCStr("base"));}),_1BW=new T(function(){return B(unCStr("IOException"));}),_1BX=new T(function(){var _1BY=hs_wordToWord64(4053623282),_1BZ=_1BY,_1C0=hs_wordToWord64(3693590983),_1C1=_1C0;return [0,_1BZ,_1C1,[0,_1BZ,_1C1,_1BV,_1BU,_1BW],_9];}),_1C2=function(_1C3){return E(_1BX);},_1C4=function(_1C5){var _1C6=E(_1C5);return new F(function(){return _2o(B(_2m(_1C6[1])),_1C2,_1C6[2]);});},_1C7=new T(function(){return B(unCStr(": "));}),_1C8=[0,41],_1C9=new T(function(){return B(unCStr(" ("));}),_1Ca=new T(function(){return B(unCStr("already exists"));}),_1Cb=new T(function(){return B(unCStr("does not exist"));}),_1Cc=new T(function(){return B(unCStr("protocol error"));}),_1Cd=new T(function(){return B(unCStr("failed"));}),_1Ce=new T(function(){return B(unCStr("invalid argument"));}),_1Cf=new T(function(){return B(unCStr("inappropriate type"));}),_1Cg=new T(function(){return B(unCStr("hardware fault"));}),_1Ch=new T(function(){return B(unCStr("unsupported operation"));}),_1Ci=new T(function(){return B(unCStr("timeout"));}),_1Cj=new T(function(){return B(unCStr("resource vanished"));}),_1Ck=new T(function(){return B(unCStr("interrupted"));}),_1Cl=new T(function(){return B(unCStr("resource busy"));}),_1Cm=new T(function(){return B(unCStr("resource exhausted"));}),_1Cn=new T(function(){return B(unCStr("end of file"));}),_1Co=new T(function(){return B(unCStr("illegal operation"));}),_1Cp=new T(function(){return B(unCStr("permission denied"));}),_1Cq=new T(function(){return B(unCStr("user error"));}),_1Cr=new T(function(){return B(unCStr("unsatisified constraints"));}),_1Cs=new T(function(){return B(unCStr("system error"));}),_1Ct=function(_1Cu,_1Cv){switch(E(_1Cu)){case 0:return new F(function(){return _e(_1Ca,_1Cv);});break;case 1:return new F(function(){return _e(_1Cb,_1Cv);});break;case 2:return new F(function(){return _e(_1Cl,_1Cv);});break;case 3:return new F(function(){return _e(_1Cm,_1Cv);});break;case 4:return new F(function(){return _e(_1Cn,_1Cv);});break;case 5:return new F(function(){return _e(_1Co,_1Cv);});break;case 6:return new F(function(){return _e(_1Cp,_1Cv);});break;case 7:return new F(function(){return _e(_1Cq,_1Cv);});break;case 8:return new F(function(){return _e(_1Cr,_1Cv);});break;case 9:return new F(function(){return _e(_1Cs,_1Cv);});break;case 10:return new F(function(){return _e(_1Cc,_1Cv);});break;case 11:return new F(function(){return _e(_1Cd,_1Cv);});break;case 12:return new F(function(){return _e(_1Ce,_1Cv);});break;case 13:return new F(function(){return _e(_1Cf,_1Cv);});break;case 14:return new F(function(){return _e(_1Cg,_1Cv);});break;case 15:return new F(function(){return _e(_1Ch,_1Cv);});break;case 16:return new F(function(){return _e(_1Ci,_1Cv);});break;case 17:return new F(function(){return _e(_1Cj,_1Cv);});break;default:return new F(function(){return _e(_1Ck,_1Cv);});}},_1Cw=[0,125],_1Cx=new T(function(){return B(unCStr("{handle: "));}),_1Cy=function(_1Cz,_1CA,_1CB,_1CC,_1CD,_1CE){var _1CF=new T(function(){var _1CG=new T(function(){return B(_1Ct(_1CA,new T(function(){var _1CH=E(_1CC);return _1CH[0]==0?E(_1CE):B(_e(_1C9,new T(function(){return B(_e(_1CH,[1,_1C8,_1CE]));},1)));},1)));},1),_1CI=E(_1CB);return _1CI[0]==0?E(_1CG):B(_e(_1CI,new T(function(){return B(_e(_1C7,_1CG));},1)));},1),_1CJ=E(_1CD);if(!_1CJ[0]){var _1CK=E(_1Cz);if(!_1CK[0]){return E(_1CF);}else{var _1CL=E(_1CK[1]);return _1CL[0]==0?B(_e(_1Cx,new T(function(){return B(_e(_1CL[1],[1,_1Cw,new T(function(){return B(_e(_1C7,_1CF));})]));},1))):B(_e(_1Cx,new T(function(){return B(_e(_1CL[1],[1,_1Cw,new T(function(){return B(_e(_1C7,_1CF));})]));},1)));}}else{return new F(function(){return _e(_1CJ[1],new T(function(){return B(_e(_1C7,_1CF));},1));});}},_1CM=function(_1CN){var _1CO=E(_1CN);return new F(function(){return _1Cy(_1CO[1],_1CO[2],_1CO[3],_1CO[4],_1CO[6],_9);});},_1CP=function(_1CQ,_1CR){var _1CS=E(_1CQ);return new F(function(){return _1Cy(_1CS[1],_1CS[2],_1CS[3],_1CS[4],_1CS[6],_1CR);});},_1CT=function(_1CU,_1CV){return new F(function(){return _2J(_1CP,_1CU,_1CV);});},_1CW=function(_1CX,_1CY,_1CZ){var _1D0=E(_1CY);return new F(function(){return _1Cy(_1D0[1],_1D0[2],_1D0[3],_1D0[4],_1D0[6],_1CZ);});},_1D1=[0,_1CW,_1CM,_1CT],_1D2=new T(function(){return [0,_1C2,_1D1,_1D3,_1C4];}),_1D3=function(_1D4){return [0,_1D2,_1D4];},_1D5=7,_1D6=function(_1D7){return [0,_6D,_1D5,_9,_1D7,_6D,_6D];},_1D8=function(_1D9,_){return new F(function(){return die(new T(function(){return B(_1D3(new T(function(){return B(_1D6(_1D9));})));}));});},_1Da=function(_1Db,_){return new F(function(){return _1D8(_1Db,_);});},_1Dc=function(_1Dd,_){return new F(function(){return _1Da(_1Dd,_);});},_1De=function(_1Df,_){return new F(function(){return _1Dc(_1Df,_);});},_1Dg=function(_1Dh,_1Di,_){var _1Dj=B(A(_1Dh,[_])),_1Dk=_1Dj;return new F(function(){return A(_1Di,[_1Dk,_]);});},_1Dl=function(_1Dm,_1Dn,_){var _1Do=B(A(_1Dm,[_])),_1Dp=_1Do;return new F(function(){return A(_1Dn,[_]);});},_1Dq=[0,_1Dg,_1Dl,_ix,_1De],_1Dr=[0,_1Dq,_5n],_1Ds=function(_1Dt){return E(E(_1Dt)[1]);},_1Du=function(_1Dv){return E(E(_1Dv)[2]);},_1Dw=function(_1Dx,_1Dy){var _1Dz=new T(function(){return B(_1Ds(_1Dx));});return function(_1DA){return new F(function(){return A(new T(function(){return B(_1fY(_1Dz));}),[new T(function(){return B(A(_1Du,[_1Dx,_1Dy]));}),function(_1DB){return new F(function(){return A(new T(function(){return B(_Uu(_1Dz));}),[[0,_1DB,_1DA]]);});}]);});};},_1DC=function(_1DD,_1DE){return [0,_1DD,function(_1DF){return new F(function(){return _1Dw(_1DE,_1DF);});}];},_1DG=function(_1DH,_1DI,_1DJ,_1DK){return new F(function(){return A(_1fY,[_1DH,new T(function(){return B(A(_1DI,[_1DK]));}),function(_1DL){return new F(function(){return A(_1DJ,[new T(function(){return E(E(_1DL)[1]);}),new T(function(){return E(E(_1DL)[2]);})]);});}]);});},_1DM=function(_1DN,_1DO,_1DP,_1DQ){return new F(function(){return A(_1fY,[_1DN,new T(function(){return B(A(_1DO,[_1DQ]));}),function(_1DR){return new F(function(){return A(_1DP,[new T(function(){return E(E(_1DR)[2]);})]);});}]);});},_1DS=function(_1DT,_1DU,_1DV,_1DW){return new F(function(){return _1DM(_1DT,_1DU,_1DV,_1DW);});},_1DX=function(_1DY){return E(E(_1DY)[4]);},_1DZ=function(_1E0,_1E1){return function(_1E2){return E(new T(function(){return B(A(_1DX,[_1E0,_1E1]));}));};},_1E3=function(_1E4){return [0,function(_1DU,_1DV,_1DW){return new F(function(){return _1DG(_1E4,_1DU,_1DV,_1DW);});},function(_1DU,_1DV,_1DW){return new F(function(){return _1DS(_1E4,_1DU,_1DV,_1DW);});},function(_1E5,_1E6){return new F(function(){return A(new T(function(){return B(_Uu(_1E4));}),[[0,_1E5,_1E6]]);});},function(_1DW){return new F(function(){return _1DZ(_1E4,_1DW);});}];},_1E7=function(_1E8,_1E9,_1Ea){return new F(function(){return A(_Uu,[_1E8,[0,_1E9,_1Ea]]);});},_1Eb=[0,10],_1Ec=function(_1Ed,_1Ee){var _1Ef=E(_1Ee);if(!_1Ef[0]){return E(_5n);}else{var _1Eg=_1Ef[1],_1Eh=E(_1Ef[2]);if(!_1Eh[0]){var _1Ei=E(_1Eg);return new F(function(){return _1Ej(_1Eb,_1Ei[3],_1Ei[4]);});}else{return function(_1Ek){return new F(function(){return A(new T(function(){var _1El=E(_1Eg);return B(_1Ej(_1Eb,_1El[3],_1El[4]));}),[new T(function(){return B(A(_1Ed,[new T(function(){return B(A(new T(function(){return B(_1Ec(_1Ed,_1Eh));}),[_1Ek]));})]));})]);});};}}},_1Em=new T(function(){return B(unCStr("(->)"));}),_1En=new T(function(){return B(unCStr("GHC.Prim"));}),_1Eo=new T(function(){var _1Ep=hs_wordToWord64(4173248105),_1Eq=_1Ep,_1Er=hs_wordToWord64(4270398258),_1Es=_1Er;return [0,_1Eq,_1Es,[0,_1Eq,_1Es,_1yd,_1En,_1Em],_9];}),_1Et=new T(function(){return E(E(_1Eo)[3]);}),_1Eu=new T(function(){return B(unCStr("GHC.Types"));}),_1Ev=new T(function(){return B(unCStr("[]"));}),_1Ew=new T(function(){var _1Ex=hs_wordToWord64(4033920485),_1Ey=_1Ex,_1Ez=hs_wordToWord64(786266835),_1EA=_1Ez;return [0,_1Ey,_1EA,[0,_1Ey,_1EA,_1yd,_1Eu,_1Ev],_9];}),_1EB=[1,_1ye,_9],_1EC=function(_1ED){var _1EE=E(_1ED);if(!_1EE[0]){return [0];}else{var _1EF=E(_1EE[1]);return [1,[0,_1EF[1],_1EF[2]],new T(function(){return B(_1EC(_1EE[2]));})];}},_1EG=new T(function(){var _1EH=E(_1Ew),_1EI=E(_1EH[3]),_1EJ=B(_e(_1EH[4],_1EB));if(!_1EJ[0]){var _1EK=E(_1EI);}else{var _1EL=B(_1yI(new T(function(){return B(_km(B(_f2(_1zb,[1,[0,_1EI[1],_1EI[2]],new T(function(){return B(_1EC(_1EJ));})]))));},1))),_1EK=E(_1EI);}var _1EM=_1EK,_1EN=_1EM;return _1EN;}),_1EO=[0,8],_1EP=[0,32],_1EQ=function(_1ER){return [1,_1EP,_1ER];},_1ES=new T(function(){return B(unCStr(" -> "));}),_1ET=[0,9],_1EU=[0,93],_1EV=[0,91],_1EW=[0,41],_1EX=[0,44],_1EY=function(_1ER){return [1,_1EX,_1ER];},_1EZ=[0,40],_1F0=[0,0],_1Ej=function(_1F1,_1F2,_1F3){var _1F4=E(_1F3);if(!_1F4[0]){return function(_1F5){return new F(function(){return _e(E(_1F2)[5],_1F5);});};}else{var _1F6=_1F4[1],_1F7=function(_1F8){var _1F9=E(_1F2)[5],_1Fa=function(_1Fb){var _1Fc=new T(function(){return B(_1Ec(_1EQ,_1F4));});return E(_1F1)[1]<=9?function(_1Fd){return new F(function(){return _e(_1F9,[1,_1EP,new T(function(){return B(A(_1Fc,[_1Fd]));})]);});}:function(_1Fe){return [1,_E,new T(function(){return B(_e(_1F9,[1,_1EP,new T(function(){return B(A(_1Fc,[[1,_D,_1Fe]]));})]));})];};},_1Ff=E(_1F9);if(!_1Ff[0]){return new F(function(){return _1Fa(_);});}else{if(E(E(_1Ff[1])[1])==40){var _1Fg=E(_1Ff[2]);if(!_1Fg[0]){return new F(function(){return _1Fa(_);});}else{if(E(E(_1Fg[1])[1])==44){return function(_1Fh){return [1,_1EZ,new T(function(){return B(A(new T(function(){return B(_1Ec(_1EY,_1F4));}),[[1,_1EW,_1Fh]]));})];};}else{return new F(function(){return _1Fa(_);});}}}else{return new F(function(){return _1Fa(_);});}}},_1Fi=E(_1F4[2]);if(!_1Fi[0]){var _1Fj=E(_1F2),_1Fk=E(_1EG),_1Fl=hs_eqWord64(_1Fj[1],_1Fk[1]),_1Fm=_1Fl;if(!E(_1Fm)){return new F(function(){return _1F7(_);});}else{var _1Fn=hs_eqWord64(_1Fj[2],_1Fk[2]),_1Fo=_1Fn;if(!E(_1Fo)){return new F(function(){return _1F7(_);});}else{return function(_1Fp){return [1,_1EV,new T(function(){return B(A(new T(function(){var _1Fq=E(_1F6);return B(_1Ej(_1F0,_1Fq[3],_1Fq[4]));}),[[1,_1EU,_1Fp]]));})];};}}}else{if(!E(_1Fi[2])[0]){var _1Fr=E(_1F2),_1Fs=E(_1Et),_1Ft=hs_eqWord64(_1Fr[1],_1Fs[1]),_1Fu=_1Ft;if(!E(_1Fu)){return new F(function(){return _1F7(_);});}else{var _1Fv=hs_eqWord64(_1Fr[2],_1Fs[2]),_1Fw=_1Fv;if(!E(_1Fw)){return new F(function(){return _1F7(_);});}else{var _1Fx=new T(function(){var _1Fy=E(_1Fi[1]);return B(_1Ej(_1EO,_1Fy[3],_1Fy[4]));}),_1Fz=new T(function(){var _1FA=E(_1F6);return B(_1Ej(_1ET,_1FA[3],_1FA[4]));});return E(_1F1)[1]<=8?function(_1FB){return new F(function(){return A(_1Fz,[new T(function(){return B(_e(_1ES,new T(function(){return B(A(_1Fx,[_1FB]));},1)));})]);});}:function(_1FC){return [1,_E,new T(function(){return B(A(_1Fz,[new T(function(){return B(_e(_1ES,new T(function(){return B(A(_1Fx,[[1,_D,_1FC]]));},1)));})]));})];};}}}else{return new F(function(){return _1F7(_);});}}}},_1FD=function(_1FE,_1FF){return new F(function(){return A(_1FE,[function(_){return new F(function(){return jsFind(toJSStr(E(_1FF)));});}]);});},_1FG=[0],_1FH=function(_1FI){return E(E(_1FI)[3]);},_1FJ=new T(function(){return [0,"value"];}),_1FK=function(_1FL){return E(E(_1FL)[6]);},_1FM=function(_1FN){return E(E(_1FN)[1]);},_1FO=new T(function(){return B(unCStr("Char"));}),_1FP=new T(function(){var _1FQ=hs_wordToWord64(3763641161),_1FR=_1FQ,_1FS=hs_wordToWord64(1343745632),_1FT=_1FS;return [0,_1FR,_1FT,[0,_1FR,_1FT,_1yd,_1Eu,_1FO],_9];}),_1FU=function(_1FV){return E(_1FP);},_1FW=function(_1FX){return E(_1Ew);},_1FY=new T(function(){return B(_1ze(_1FW,_1FU));}),_1FZ=new T(function(){return B(A(_1FY,[_]));}),_1G0=function(_1G1,_1G2,_1G3,_1G4,_1G5,_1G6,_1G7,_1G8,_1G9){var _1Ga=new T(function(){return B(A(_1G4,[_1FG]));});return new F(function(){return A(_1G2,[new T(function(){return B(_1FD(E(_1G1)[2],_1G9));}),function(_1Gb){var _1Gc=E(_1Gb);return _1Gc[0]==0?E(_1Ga):B(A(_1G2,[new T(function(){return B(A(E(_1G1)[2],[function(_){var _1Gd=jsGet(E(_1Gc[1])[1],E(_1FJ)[1]),_1Ge=_1Gd;return [1,new T(function(){return fromJSStr(_1Ge);})];}]));}),function(_1Gf){var _1Gg=E(_1Gf);if(!_1Gg[0]){return E(_1Ga);}else{var _1Gh=_1Gg[1];if(!E(new T(function(){var _1Gi=B(A(_1G6,[_])),_1Gj=E(_1FZ),_1Gk=hs_eqWord64(_1Gi[1],_1Gj[1]),_1Gl=_1Gk;if(!E(_1Gl)){var _1Gm=false;}else{var _1Gn=hs_eqWord64(_1Gi[2],_1Gj[2]),_1Go=_1Gn,_1Gm=E(_1Go)==0?false:true;}var _1Gp=_1Gm,_1Gq=_1Gp;return _1Gq;}))){var _1Gr=function(_1Gs){return new F(function(){return A(_1G4,[[1,_1Gh,new T(function(){return B(A(new T(function(){return B(_1FK(_1G8));}),[new T(function(){return B(A(new T(function(){return B(_1FH(_1G8));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1Gh,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1Gt=B(A(_1G6,[_]));return B(A(_1Ej,[_1F0,_1Gt[3],_1Gt[4],_9]));})));})));})));})]));})]));})]]);});},_1Gu=B(A(new T(function(){return B(A(_1FM,[_1G7,_gh]));}),[_1Gh]));if(!_1Gu[0]){return new F(function(){return _1Gr(_);});}else{var _1Gv=E(_1Gu[1]);return E(_1Gv[2])[0]==0?E(_1Gu[2])[0]==0?B(A(_1G4,[[2,_1Gv[1]]])):B(_1Gr(_)):B(_1Gr(_));}}else{return new F(function(){return A(_1G4,[[2,_1Gh]]);});}}}]));}]);});},_1Gw=function(_1Gx){return E(E(_1Gx)[10]);},_1Gy=function(_1Gz){return new F(function(){return _3E([1,function(_1GA){return new F(function(){return A(_bL,[_1GA,function(_1GB){return E(new T(function(){return B(_d1(function(_1GC){var _1GD=E(_1GC);return _1GD[0]==0?B(A(_1Gz,[_1GD[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_dn(_1GE,_1Gz))];}));});},_1GE=function(_1GF,_1GG){return new F(function(){return _1Gy(_1GG);});},_1GH=[0,91],_1GI=[1,_1GH,_9],_1GJ=function(_1GK,_1GL){var _1GM=function(_1GN,_1GO){return [1,function(_1GP){return new F(function(){return A(_bL,[_1GP,function(_1GQ){return E(new T(function(){return B(_d1(function(_1GR){var _1GS=E(_1GR);if(_1GS[0]==2){var _1GT=E(_1GS[1]);if(!_1GT[0]){return [2];}else{var _1GU=_1GT[2];switch(E(E(_1GT[1])[1])){case 44:return E(_1GU)[0]==0?!E(_1GN)?[2]:E(new T(function(){return B(A(_1GK,[_dm,function(_1GV){return new F(function(){return _1GM(_7i,function(_1GW){return new F(function(){return A(_1GO,[[1,_1GV,_1GW]]);});});});}]));})):[2];case 93:return E(_1GU)[0]==0?E(new T(function(){return B(A(_1GO,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1GX=function(_1GY){return new F(function(){return _3E([1,function(_1GZ){return new F(function(){return A(_bL,[_1GZ,function(_1H0){return E(new T(function(){return B(_d1(function(_1H1){var _1H2=E(_1H1);return _1H2[0]==2?!B(_4b(_1H2[1],_1GI))?[2]:E(new T(function(){return B(_3E(B(_1GM(_7h,_1GY)),new T(function(){return B(A(_1GK,[_dm,function(_1H3){return new F(function(){return _1GM(_7i,function(_1H4){return new F(function(){return A(_1GY,[[1,_1H3,_1H4]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_dn(function(_1H5,_1H6){return new F(function(){return _1GX(_1H6);});},_1GY))];}));});};return new F(function(){return _1GX(_1GL);});},_1H7=function(_1H8){return new F(function(){return _3E(B(_3E([1,function(_1H9){return new F(function(){return A(_bL,[_1H9,function(_1Ha){return E(new T(function(){return B(_d1(function(_1Hb){var _1Hc=E(_1Hb);return _1Hc[0]==1?B(A(_1H8,[_1Hc[1]])):[2];}));}));}]);});}],new T(function(){return B(_1GJ(_1GE,_1H8));}))),new T(function(){return [1,B(_dn(_1Hd,_1H8))];}));});},_1Hd=function(_1He,_1Hf){return new F(function(){return _1H7(_1Hf);});},_1Hg=new T(function(){return B(_1H7(_4I));}),_1Hh=function(_1Hi){return new F(function(){return _3u(_1Hg,_1Hi);});},_1Hj=new T(function(){return B(_1Gy(_4I));}),_1Hk=function(_1Hi){return new F(function(){return _3u(_1Hj,_1Hi);});},_1Hl=function(_1Hm){return E(_1Hk);},_1Hn=[0,_1Hl,_1Hh,_1GE,_1Hd],_1Ho=function(_1Hp){return E(E(_1Hp)[4]);},_1Hq=function(_1Hr,_1Hs,_1Ht){return new F(function(){return _1GJ(new T(function(){return B(_1Ho(_1Hr));}),_1Ht);});},_1Hu=function(_1Hv){return function(_58){return new F(function(){return _3u(new T(function(){return B(_1GJ(new T(function(){return B(_1Ho(_1Hv));}),_4I));}),_58);});};},_1Hw=function(_1Hx,_1Hy){return function(_58){return new F(function(){return _3u(new T(function(){return B(A(_1Ho,[_1Hx,_1Hy,_4I]));}),_58);});};},_1Hz=function(_1HA){return [0,function(_1Hi){return new F(function(){return _1Hw(_1HA,_1Hi);});},new T(function(){return B(_1Hu(_1HA));}),new T(function(){return B(_1Ho(_1HA));}),function(_1HB,_1Hi){return new F(function(){return _1Hq(_1HA,_1HB,_1Hi);});}];},_1HC=new T(function(){return B(_1Hz(_1Hn));}),_1HD=function(_1HE,_1HF,_1HG){var _1HH=new T(function(){return B(_1Gw(_1HE));}),_1HI=new T(function(){return B(_1Ds(_1HG));}),_1HJ=new T(function(){return B(_Uu(_1HI));});return function(_1HK,_1HL){return new F(function(){return A(new T(function(){return B(_1fY(_1HI));}),[new T(function(){return B(A(new T(function(){return B(_1fY(_1HI));}),[new T(function(){return B(A(new T(function(){return B(_Uu(_1HI));}),[[0,_1HL,_1HL]]));}),function(_1HM){var _1HN=new T(function(){return E(E(_1HM)[1]);}),_1HO=new T(function(){return E(E(_1HN)[2]);});return new F(function(){return A(new T(function(){return B(_1fY(_1HI));}),[new T(function(){return B(A(new T(function(){return B(_Uu(_1HI));}),[[0,_1x,new T(function(){var _1HP=E(_1HN);return [0,_1HP[1],new T(function(){return [0,E(_1HO)[1]+1|0];}),_1HP[3],_1HP[4],_1HP[5],_1HP[6],_1HP[7]];})]]));}),function(_1HQ){return new F(function(){return A(new T(function(){return B(_Uu(_1HI));}),[[0,[1,_ip,new T(function(){return B(_e(B(_F(0,E(_1HO)[1],_9)),new T(function(){return E(E(_1HN)[1]);},1)));})],new T(function(){return E(E(_1HQ)[2]);})]]);});}]);});}]));}),function(_1HR){var _1HS=new T(function(){return E(E(_1HR)[1]);});return new F(function(){return A(new T(function(){return B(_1fY(_1HI));}),[new T(function(){return B(A(_1G0,[new T(function(){return B(_1DC(new T(function(){return B(_1E3(_1HI));}),_1HG));}),function(_1HT,_1zI,_1HU){return new F(function(){return _1DG(_1HI,_1HT,_1zI,_1HU);});},function(_1HT,_1zI,_1HU){return new F(function(){return _1DS(_1HI,_1HT,_1zI,_1HU);});},function(_1zI,_1HU){return new F(function(){return _1E7(_1HI,_1zI,_1HU);});},function(_1HU){return new F(function(){return _1DZ(_1HI,_1HU);});},_1FY,_1HC,_1HE,_1HS,new T(function(){return E(E(_1HR)[2]);})]));}),function(_1HV){var _1HW=E(_1HV),_1HX=_1HW[2],_1HY=E(_1HW[1]);switch(_1HY[0]){case 0:return new F(function(){return A(_1HJ,[[0,[0,new T(function(){return B(A(_1HH,[_1HS,_1HK]));}),_6D],_1HX]]);});break;case 1:return new F(function(){return A(_1HJ,[[0,[0,new T(function(){return B(A(_1HH,[_1HS,_1HY[1]]));}),_6D],_1HX]]);});break;default:var _1HZ=_1HY[1];return new F(function(){return A(_1HJ,[[0,[0,new T(function(){return B(A(_1HH,[_1HS,_1HZ]));}),[1,_1HZ]],_1HX]]);});}}]);});}]);});};},_1I0=new T(function(){return B(_1HD(_1BI,_1BT,_1Dr));}),_1I1=function(_1I2){return E(E(_1I2)[2]);},_1I3=function(_1I4){return E(E(_1I4)[1]);},_1I5=function(_1I6,_1I7,_1I8){return function(_1I9,_){var _1Ia=B(A(_1I7,[_1I9,_])),_1Ib=_1Ia,_1Ic=E(_1Ib),_1Id=E(_1Ic[1]),_1Ie=new T(function(){return B(A(new T(function(){return B(_1I1(_1I6));}),[_1I8,function(_){var _1If=E(E(_1I9)[4]),_1Ig=B(A(_1If[1],[_])),_1Ih=_1Ig,_1Ii=E(_1Ih);if(!_1Ii[0]){return _1x;}else{var _1Ij=B(A(_1If[2],[_1Ii[1],_])),_1Ik=_1Ij;return _1x;}}]));});return [0,[0,function(_1Il,_){var _1Im=B(A(_1Id[1],[_1Il,_])),_1In=_1Im,_1Io=E(_1In),_1Ip=E(_1Ie),_1Iq=jsSetCB(_1Io[1],toJSStr(E(new T(function(){return B(A(_1I3,[_1I6,_1I8]));}))),_1Ie),_1Ir=_1Iq;return _1Io;},_1Id[2]],_1Ic[2]];};},_1Is=function(_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID){return function(_1IE,_1IF){return function(_58,_xf){return new F(function(){return _j9(function(_1IG,_){var _1IH=B(A(new T(function(){return B(_1I5(_ic,new T(function(){return B(_1I5(_ic,new T(function(){return B(A(_1I0,[_1IF]));}),_ev));}),_eu));}),[_1IG,_])),_1II=_1IH,_1IJ=E(_1II),_1IK=E(_1IJ[1]);return [0,[0,function(_1IL,_){var _1IM=B(A(_1IK[1],[_1IL,_])),_1IN=_1IM,_1IO=B(A(_ij,[_5n,_1IN,_KX,_NU,_])),_1IP=_1IO;return _1IN;},_1IK[2]],_1IJ[2]];},function(_1IQ){var _1IR=new T(function(){var _1IS=B(_14E(_13A,_150,[0,new T(function(){return B(_e(_1IQ,_1xW));}),E(_13v),E(_1x)]));if(!_1IS[0]){var _1IT=E(_1IS[1]);if(!_1IT[0]){var _1IU=E(E(_1IT[1])[1]);}else{var _1IU=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_mG(_1IT[1]));})));})],_9],_9];}var _1IV=_1IU;}else{var _1IW=E(_1IS[1]);if(!_1IW[0]){var _1IX=E(E(_1IW[1])[1]);}else{var _1IX=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_mG(_1IW[1]));})));})],_9],_9];}var _1IV=_1IX;}return _1IV;});return function(_58,_xf){return new F(function(){return _j9(_O1,function(_1IY,_1IZ,_){return new F(function(){return _j9(_O6,function(_1J0,_1J1,_){return new F(function(){return _j9(_Ob,function(_1J2,_1J3,_){return new F(function(){return _j9(function(_1J4,_){return [0,[0,function(_1J5,_){var _1J6=B(_La(_id,_9,_1J5,_)),_1J7=_1J6,_1J8=B(A(_ij,[_5n,_1J7,_iv,_1IY,_])),_1J9=_1J8,_1Ja=B(A(_ij,[_5n,_1J7,_KX,_Oc,_])),_1Jb=_1Ja;return _1J7;},_Oh],_1J4];},function(_1Jc,_1Jd,_){return new F(function(){return _j9(function(_1Je,_){return [0,[0,function(_1Jf,_){var _1Jg=B(_iX(_j7,new T(function(){return B(_1xM(_1IR));}),_1Jf,_)),_1Jh=_1Jg,_1Ji=B(A(_ij,[_5n,_1Jh,_iv,_1J0,_])),_1Jj=_1Ji,_1Jk=B(A(_ij,[_5n,_1Jh,_KX,_Od,_])),_1Jl=_1Jk;return _1Jh;},_Oh],_1Je];},function(_1Jm){return E(new T(function(){var _1Jn=E(new T(function(){return B(_Ks(_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IR,new T(function(){return E(E(_1IE)[1]);}),new T(function(){return E(E(_1IE)[2]);})));}));if(!_1Jn[0]){var _1Jo=function(_1Jp,_){return [0,[0,function(_1Jq,_){var _1Jr=B(A(new T(function(){return B(A(new T(function(){return B(_MV(_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID));}),[_1IE,new T(function(){return B(_Ha(_1Jn[1]));})]));}),[_1Jq,_])),_1Js=_1Jr,_1Jt=B(A(_ij,[_5n,_1Js,_iv,_1J2,_])),_1Ju=_1Jt,_1Jv=B(A(_ij,[_5n,_1Js,_KX,_Oe,_])),_1Jw=_1Jv;return _1Js;},_Oh],_1Jp];};}else{var _1Jx=E(_1Jn[1]);if(!_1Jx[0]){var _1Jy=function(_Ms,_){return new F(function(){return _Om(_1IY,_NT,_Oj,_Ms,_);});};}else{var _1Jy=function(_58,_xf){return new F(function(){return _Om(_1IY,_NT,function(_1Jz,_){return [0,[0,function(_Ms,_){return new F(function(){return _iX(_id,new T(function(){var _1JA=E(_1Jx[1]);return B(_nk(new T(function(){return B(_n7(_1Iz,_1Iy,_1Ix,_1Iw,_1Iv,_1It,_1Iu));}),new T(function(){return B(_fG(_1Iz,_1Iy,_1Ix,_1Iw,_1Iv,_1It,_1Iu));}),_1JA[1],_1JA[2]));}),_Ms,_);});},_Oh],_1Jz];},_58,_xf);});};}var _1Jo=_1Jy;}return _1Jo;}));},_1Jd,_);});},_1J3,_);});},_1J1,_);});},_1IZ,_);});},_58,_xf);});};},_58,_xf);});};};},_1JB=function(_1JC,_1JD,_1JE,_1JF){return new F(function(){return A(_1JC,[function(_){var _1JG=jsSet(E(_1JD)[1],toJSStr(E(_1JE)),toJSStr(E(_1JF)));return _1x;}]);});},_1JH=new T(function(){return B(unCStr("innerHTML"));}),_1JI=new T(function(){return B(unCStr("textContent"));}),_1JJ=function(_1JK,_1JL,_1JM,_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_1JV,_1JW,_){var _1JX=B(_1j(_1JW,_1JI,_)),_1JY=_1JX,_1JZ=[0,_1JW],_1K0=B(A(_1JB,[_5n,_1JZ,_1JH,_9,_])),_1K1=_1K0,_1K2=E(_gJ)[1],_1K3=takeMVar(_1K2),_1K4=_1K3,_1K5=B(A(_1Is,[_1JK,_1JL,_1JM,_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_1JV,_1JY,_1K4,_])),_1K6=_1K5,_1K7=E(_1K6),_1K8=E(_1K7[1]),_=putMVar(_1K2,_1K7[2]),_1K9=B(A(_1K8[1],[_1JZ,_])),_1Ka=_1K9;return _1K8[2];},_1Kb=function(_){var _1Kc=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1Kd=_1Kc;return _1x;},_1Ke=new T(function(){return B(unCStr("embedding complete"));}),_1Kf=new T(function(){return B(unCStr("proofbox"));}),_1Kg=function(_1Kh,_1Ki,_1Kj,_1Kk,_1Kl,_1Km,_1Kn,_1Ko,_1Kp,_1Kq,_1Kr,_1Ks,_){var _1Kt=jsElemsByClassName(toJSStr(E(_1Kf))),_1Ku=_1Kt,_1Kv=B((function(_1Kw,_){while(1){var _1Kx=E(_1Kw);if(!_1Kx[0]){return _1x;}else{var _1Ky=B(_1JJ(_1Kh,_1Ki,_1Kj,_1Kk,_1Kl,_1Km,_1Kn,_1Ko,_1Kp,_1Kq,_1Kr,_1Ks,E(_1Kx[1])[1],_)),_1Kz=_1Ky;_1Kw=_1Kx[2];continue;}}})(_1Ku,_)),_1KA=_1Kv,_1KB=jsLog(toJSStr(E(_1Ke))),_1KC=jsSetTimeout(60,_1Kb);return _1x;},_1KD=new T(function(){return [0,"wheel"];}),_1KE=new T(function(){return B(unCStr("ADD"));}),_1KF=new T(function(){return B(unCStr("ADJ"));}),_1KG=new T(function(){return B(unCStr("BC"));}),_1KH=[0,1],_1KI=[1,_1KH],_1KJ=[1,_1KI],_1KK=[0,_1KH],_1KL=[1,_1KK],_1KM=new T(function(){return B(unCStr("DN"));}),_1KN=new T(function(){return B(_4b(_9,_1KM));}),_1KO=new T(function(){return B(unCStr("MTP"));}),_1KP=new T(function(){return B(unCStr("MT"));}),_1KQ=new T(function(){return B(unCStr("MP"));}),_1KR=new T(function(){return B(unCStr("ID"));}),_1KS=new T(function(){return B(unCStr("DD"));}),_1KT=new T(function(){return B(unCStr("CD"));}),_1KU=new T(function(){return B(unCStr("CB"));}),_1KV=[0,2],_1KW=[1,_1KV],_1KX=[1,_1KW],_1KY=[0,_1KV],_1KZ=[1,_1KY],_1L0=function(_1L1){if(!B(_4b(_1L1,_1KE))){if(!B(_4b(_1L1,_1KF))){if(!B(_4b(_1L1,_1KG))){if(!B(_4b(_1L1,_1KU))){if(!B(_4b(_1L1,_1KT))){if(!B(_4b(_1L1,_1KS))){if(!B(_4b(_1L1,_1KR))){if(!B(_4b(_1L1,_1KQ))){if(!B(_4b(_1L1,_1KP))){if(!B(_4b(_1L1,_1KO))){var _1L2=E(_1L1);return _1L2[0]==0?!E(_1KN)?[0]:E(_1KL):E(E(_1L2[1])[1])==83?E(_1L2[2])[0]==0?E(_1KL):!B(_4b(_1L2,_1KM))?[0]:E(_1KL):!B(_4b(_1L2,_1KM))?[0]:E(_1KL);}else{return E(_1KZ);}}else{return E(_1KZ);}}else{return E(_1KZ);}}else{return E(_1KX);}}else{return E(_1KJ);}}else{return E(_1KJ);}}else{return E(_1KZ);}}else{return E(_1KL);}}else{return E(_1KZ);}}else{return E(_1KL);}},_1L3=function(_1L4){return E(E(_1L4)[2]);},_1L5=function(_1L6,_1L7,_1L8){while(1){var _1L9=E(_1L7);if(!_1L9[0]){return E(_1L8)[0]==0?1:0;}else{var _1La=E(_1L8);if(!_1La[0]){return 2;}else{var _1Lb=B(A(_1L3,[_1L6,_1L9[1],_1La[1]]));if(_1Lb==1){_1L7=_1L9[2];_1L8=_1La[2];continue;}else{return E(_1Lb);}}}}},_1Lc=function(_1Ld){return E(E(_1Ld)[3]);},_1Le=function(_1Lf,_1Lg,_1Lh,_1Li,_1Lj){switch(B(_1L5(_1Lf,_1Lg,_1Li))){case 0:return true;case 1:return new F(function(){return A(_1Lc,[_1Lf,_1Lh,_1Lj]);});break;default:return false;}},_1Lk=function(_1Ll,_1Lm,_1Ln,_1Lo){var _1Lp=E(_1Ln),_1Lq=E(_1Lo);return new F(function(){return _1Le(_1Lm,_1Lp[1],_1Lp[2],_1Lq[1],_1Lq[2]);});},_1Lr=function(_1Ls){return E(E(_1Ls)[6]);},_1Lt=function(_1Lu,_1Lv,_1Lw,_1Lx,_1Ly){switch(B(_1L5(_1Lu,_1Lv,_1Lx))){case 0:return true;case 1:return new F(function(){return A(_1Lr,[_1Lu,_1Lw,_1Ly]);});break;default:return false;}},_1Lz=function(_1LA,_1LB,_1LC,_1LD){var _1LE=E(_1LC),_1LF=E(_1LD);return new F(function(){return _1Lt(_1LB,_1LE[1],_1LE[2],_1LF[1],_1LF[2]);});},_1LG=function(_1LH){return E(E(_1LH)[5]);},_1LI=function(_1LJ,_1LK,_1LL,_1LM,_1LN){switch(B(_1L5(_1LJ,_1LK,_1LM))){case 0:return false;case 1:return new F(function(){return A(_1LG,[_1LJ,_1LL,_1LN]);});break;default:return true;}},_1LO=function(_1LP,_1LQ,_1LR,_1LS){var _1LT=E(_1LR),_1LU=E(_1LS);return new F(function(){return _1LI(_1LQ,_1LT[1],_1LT[2],_1LU[1],_1LU[2]);});},_1LV=function(_1LW){return E(E(_1LW)[4]);},_1LX=function(_1LY,_1LZ,_1M0,_1M1,_1M2){switch(B(_1L5(_1LY,_1LZ,_1M1))){case 0:return false;case 1:return new F(function(){return A(_1LV,[_1LY,_1M0,_1M2]);});break;default:return true;}},_1M3=function(_1M4,_1M5,_1M6,_1M7){var _1M8=E(_1M6),_1M9=E(_1M7);return new F(function(){return _1LX(_1M5,_1M8[1],_1M8[2],_1M9[1],_1M9[2]);});},_1Ma=function(_1Mb,_1Mc,_1Md,_1Me,_1Mf){switch(B(_1L5(_1Mb,_1Mc,_1Me))){case 0:return 0;case 1:return new F(function(){return A(_1L3,[_1Mb,_1Md,_1Mf]);});break;default:return 2;}},_1Mg=function(_1Mh,_1Mi,_1Mj,_1Mk){var _1Ml=E(_1Mj),_1Mm=E(_1Mk);return new F(function(){return _1Ma(_1Mi,_1Ml[1],_1Ml[2],_1Mm[1],_1Mm[2]);});},_1Mn=function(_1Mo,_1Mp,_1Mq,_1Mr){var _1Ms=E(_1Mq),_1Mt=_1Ms[1],_1Mu=_1Ms[2],_1Mv=E(_1Mr),_1Mw=_1Mv[1],_1Mx=_1Mv[2];switch(B(_1L5(_1Mp,_1Mt,_1Mw))){case 0:return [0,_1Mw,_1Mx];case 1:return !B(A(_1Lr,[_1Mp,_1Mu,_1Mx]))?[0,_1Mt,_1Mu]:[0,_1Mw,_1Mx];default:return [0,_1Mt,_1Mu];}},_1My=function(_1Mz,_1MA,_1MB,_1MC){var _1MD=E(_1MB),_1ME=_1MD[1],_1MF=_1MD[2],_1MG=E(_1MC),_1MH=_1MG[1],_1MI=_1MG[2];switch(B(_1L5(_1MA,_1ME,_1MH))){case 0:return [0,_1ME,_1MF];case 1:return !B(A(_1Lr,[_1MA,_1MF,_1MI]))?[0,_1MH,_1MI]:[0,_1ME,_1MF];default:return [0,_1MH,_1MI];}},_1MJ=function(_1MK,_1ML){return [0,_1MK,function(_nQ,_nR){return new F(function(){return _1Mg(_1MK,_1ML,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Lk(_1MK,_1ML,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1M3(_1MK,_1ML,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1LO(_1MK,_1ML,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Lz(_1MK,_1ML,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Mn(_1MK,_1ML,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1My(_1MK,_1ML,_nQ,_nR);});}];},_1MM=function(_1MN,_1MO,_1MP,_1MQ){return !B(A(_1MN,[_1MP,_1MQ]))?B(_OT(B(A(_1MO,[_1MP,_uj])),B(A(_1MO,[_1MQ,_uj]))))==2?false:true:false;},_1MR=function(_1MS,_1MT,_1MU,_1MV){return new F(function(){return _1MM(E(_1MS)[1],_1MT,_1MU,_1MV);});},_1MW=function(_1MX,_1MY,_1MZ,_1N0){return B(_OT(B(A(_1MY,[_1MZ,_uj])),B(A(_1MY,[_1N0,_uj]))))==2?false:true;},_1N1=function(_1N2,_1N3,_1N4,_1N5){return !B(A(_1N2,[_1N4,_1N5]))?B(_OT(B(A(_1N3,[_1N4,_uj])),B(A(_1N3,[_1N5,_uj]))))==2?true:false:false;},_1N6=function(_1N7,_1N8,_1N9,_1Na){return new F(function(){return _1N1(E(_1N7)[1],_1N8,_1N9,_1Na);});},_1Nb=function(_1Nc,_1Nd,_1Ne,_1Nf){return !B(A(_1Nc,[_1Ne,_1Nf]))?B(_OT(B(A(_1Nd,[_1Ne,_uj])),B(A(_1Nd,[_1Nf,_uj]))))==2?true:false:true;},_1Ng=function(_1Nh,_1Ni,_1Nj,_1Nk){return new F(function(){return _1Nb(E(_1Nh)[1],_1Ni,_1Nj,_1Nk);});},_1Nl=function(_1Nm,_1Nn,_1No,_1Np){return !B(A(_1Nm,[_1No,_1Np]))?B(_OT(B(A(_1Nn,[_1No,_uj])),B(A(_1Nn,[_1Np,_uj]))))==2?2:0:1;},_1Nq=function(_1Nr,_1Ns,_1Nt,_1Nu){return new F(function(){return _1Nl(E(_1Nr)[1],_1Ns,_1Nt,_1Nu);});},_1Nv=function(_1Nw,_1Nx,_1Ny,_1Nz){return B(_OT(B(A(_1Nx,[_1Ny,_uj])),B(A(_1Nx,[_1Nz,_uj]))))==2?E(_1Ny):E(_1Nz);},_1NA=function(_1NB,_1NC,_1ND,_1NE){return B(_OT(B(A(_1NC,[_1ND,_uj])),B(A(_1NC,[_1NE,_uj]))))==2?E(_1NE):E(_1ND);},_1NF=function(_1NG,_1NH){return [0,_1NG,function(_fO,_fP){return new F(function(){return _1Nq(_1NG,_1NH,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1MR(_1NG,_1NH,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1Ng(_1NG,_1NH,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1N6(_1NG,_1NH,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1MW(_1NG,_1NH,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1Nv(_1NG,_1NH,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1NA(_1NG,_1NH,_fO,_fP);});}];},_1NI=function(_1NJ,_1NK,_1NL,_1NM,_1NN,_1NO,_1NP){var _1NQ=function(_1NR,_1NS){return new F(function(){return _eL(_1NJ,_1NK,_1NL,_1NN,_1NM,_1NP,_1NO,_1NR);});};return function(_1NT,_1NU){var _1NV=E(_1NT);if(!_1NV[0]){var _1NW=E(_1NU);return _1NW[0]==0?B(_OT(B(_ex(_1NV[1])),B(_ex(_1NW[1]))))==2?false:true:true;}else{var _1NX=E(_1NU);return _1NX[0]==0?false:B(_1L5(new T(function(){return B(_1NF(new T(function(){return B(_uo(_1NQ));}),_1NQ));}),_1NV[1],_1NX[1]))==2?false:true;}};},_1NY=function(_1NZ,_1O0,_1O1,_1O2,_1O3,_1O4,_1O5,_1O6,_1O7,_1O8){return !B(A(_1NI,[_1O0,_1O1,_1O2,_1O3,_1O4,_1O5,_1O6,_1O7,_1O8]))?E(_1O7):E(_1O8);},_1O9=function(_1Oa,_1Ob,_1Oc,_1Od,_1Oe,_1Of,_1Og,_1Oh,_1Oi,_1Oj){return !B(A(_1NI,[_1Ob,_1Oc,_1Od,_1Oe,_1Of,_1Og,_1Oh,_1Oi,_1Oj]))?E(_1Oj):E(_1Oi);},_1Ok=function(_1Ol,_1Om,_1On,_1Oo,_1Op,_1Oq,_1Or){var _1Os=function(_1Ot,_1Ou){return new F(function(){return _eL(_1Ol,_1Om,_1On,_1Op,_1Oo,_1Or,_1Oq,_1Ot);});};return function(_1Ov,_1Ow){var _1Ox=E(_1Ov);if(!_1Ox[0]){var _1Oy=_1Ox[1],_1Oz=E(_1Ow);if(!_1Oz[0]){var _1OA=_1Oz[1];return B(_o6(_1Oy,_1OA,_1))[0]==0?B(_OT(B(_ex(_1Oy)),B(_ex(_1OA))))==2?false:true:false;}else{return true;}}else{var _1OB=E(_1Ow);return _1OB[0]==0?false:B(_1L5(new T(function(){return B(_1NF(new T(function(){return B(_uo(_1Os));}),_1Os));}),_1Ox[1],_1OB[1]))==0?true:false;}};},_1OC=function(_1OD,_1OE,_1OF,_1OG,_1OH,_1OI,_1OJ){var _1OK=function(_1OL,_1OM){return new F(function(){return _eL(_1OD,_1OE,_1OF,_1OH,_1OG,_1OJ,_1OI,_1OL);});};return function(_1ON,_1OO){var _1OP=E(_1ON);if(!_1OP[0]){var _1OQ=_1OP[1],_1OR=E(_1OO);if(!_1OR[0]){var _1OS=_1OR[1];return B(_o6(_1OQ,_1OS,_1))[0]==0?B(_OT(B(_ex(_1OQ)),B(_ex(_1OS))))==2?true:false:false;}else{return false;}}else{var _1OT=E(_1OO);return _1OT[0]==0?true:B(_1L5(new T(function(){return B(_1NF(new T(function(){return B(_uo(_1OK));}),_1OK));}),_1OP[1],_1OT[1]))==2?true:false;}};},_1OU=function(_1OV,_1OW,_1OX,_1OY,_1OZ,_1P0,_1P1){var _1P2=function(_1P3,_1P4){return new F(function(){return _eL(_1OV,_1OW,_1OX,_1OZ,_1OY,_1P1,_1P0,_1P3);});};return function(_1P5,_1P6){var _1P7=E(_1P5);if(!_1P7[0]){var _1P8=_1P7[1],_1P9=E(_1P6);if(!_1P9[0]){var _1Pa=_1P9[1];return B(_o6(_1P8,_1Pa,_1))[0]==0?B(_OT(B(_ex(_1P8)),B(_ex(_1Pa))))==2?true:false:true;}else{return false;}}else{var _1Pb=E(_1P6);return _1Pb[0]==0?true:B(_1L5(new T(function(){return B(_1NF(new T(function(){return B(_uo(_1P2));}),_1P2));}),_1P7[1],_1Pb[1]))==0?false:true;}};},_1Pc=function(_1Pd,_1Pe,_1Pf,_1Pg,_1Ph,_1Pi,_1Pj){var _1Pk=function(_1Pl,_1Pm){return new F(function(){return _eL(_1Pd,_1Pe,_1Pf,_1Ph,_1Pg,_1Pj,_1Pi,_1Pl);});};return function(_1Pn,_1Po){var _1Pp=E(_1Pn);if(!_1Pp[0]){var _1Pq=_1Pp[1],_1Pr=E(_1Po);if(!_1Pr[0]){var _1Ps=_1Pr[1];return B(_o6(_1Pq,_1Ps,_1))[0]==0?B(_OT(B(_ex(_1Pq)),B(_ex(_1Ps))))==2?2:0:1;}else{return 0;}}else{var _1Pt=E(_1Po);return _1Pt[0]==0?2:B(_1L5(new T(function(){return B(_1NF(new T(function(){return B(_uo(_1Pk));}),_1Pk));}),_1Pp[1],_1Pt[1]));}};},_1Pu=function(_1Pv,_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC){return [0,_1Pv,new T(function(){return B(_1Pc(_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC));}),new T(function(){return B(_1Ok(_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC));}),new T(function(){return B(_1OU(_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC));}),new T(function(){return B(_1OC(_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC));}),new T(function(){return B(_1NI(_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC));}),function(_fO,_fP){return new F(function(){return _1NY(_1Pv,_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC,_fO,_fP);});},function(_fO,_fP){return new F(function(){return _1O9(_1Pv,_1Pw,_1Px,_1Py,_1Pz,_1PA,_1PB,_1PC,_fO,_fP);});}];},_1PD=new T(function(){return B(_fG(_Q,_u,_Q,_Q,_N,_2,_15));}),_1PE=new T(function(){return B(_1Pu(_1PD,_Q,_u,_Q,_Q,_N,_15,_2));}),_1PF=new T(function(){return B(_o4(_1PD));}),_1PG=new T(function(){return B(_1MJ(_1PF,_1PE));}),_1PH=function(_1PI,_1PJ,_1PK,_1PL){var _1PM=E(_1PK),_1PN=E(_1PL);return new F(function(){return _1Le(_1PJ,_1PM[1],_1PM[2],_1PN[1],_1PN[2]);});},_1PO=function(_1PP,_1PQ,_1PR,_1PS){var _1PT=E(_1PR),_1PU=E(_1PS);return new F(function(){return _1Lt(_1PQ,_1PT[1],_1PT[2],_1PU[1],_1PU[2]);});},_1PV=function(_1PW,_1PX,_1PY,_1PZ){var _1Q0=E(_1PY),_1Q1=E(_1PZ);return new F(function(){return _1LI(_1PX,_1Q0[1],_1Q0[2],_1Q1[1],_1Q1[2]);});},_1Q2=function(_1Q3,_1Q4,_1Q5,_1Q6){var _1Q7=E(_1Q5),_1Q8=E(_1Q6);return new F(function(){return _1LX(_1Q4,_1Q7[1],_1Q7[2],_1Q8[1],_1Q8[2]);});},_1Q9=function(_1Qa,_1Qb,_1Qc,_1Qd){var _1Qe=E(_1Qc),_1Qf=E(_1Qd);return new F(function(){return _1Ma(_1Qb,_1Qe[1],_1Qe[2],_1Qf[1],_1Qf[2]);});},_1Qg=function(_1Qh,_1Qi,_1Qj,_1Qk){var _1Ql=E(_1Qj),_1Qm=_1Ql[1],_1Qn=_1Ql[2],_1Qo=E(_1Qk),_1Qp=_1Qo[1],_1Qq=_1Qo[2];switch(B(_1L5(_1Qi,_1Qm,_1Qp))){case 0:return [0,_1Qp,_1Qq];case 1:return !B(A(_1Lr,[_1Qi,_1Qn,_1Qq]))?[0,_1Qm,_1Qn]:[0,_1Qp,_1Qq];default:return [0,_1Qm,_1Qn];}},_1Qr=function(_1Qs,_1Qt,_1Qu,_1Qv){var _1Qw=E(_1Qu),_1Qx=_1Qw[1],_1Qy=_1Qw[2],_1Qz=E(_1Qv),_1QA=_1Qz[1],_1QB=_1Qz[2];switch(B(_1L5(_1Qt,_1Qx,_1QA))){case 0:return [0,_1Qx,_1Qy];case 1:return !B(A(_1Lr,[_1Qt,_1Qy,_1QB]))?[0,_1QA,_1QB]:[0,_1Qx,_1Qy];default:return [0,_1QA,_1QB];}},_1QC=function(_1QD,_1QE){return [0,_1QD,function(_nQ,_nR){return new F(function(){return _1Q9(_1QD,_1QE,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1PH(_1QD,_1QE,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Q2(_1QD,_1QE,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1PV(_1QD,_1QE,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1PO(_1QD,_1QE,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Qg(_1QD,_1QE,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Qr(_1QD,_1QE,_nQ,_nR);});}];},_1QF=function(_1QG,_1QH){return B(_OT(_1QG,_1QH))==0?false:true;},_1QI=function(_1QJ){return E(E(_1QJ)[1]);},_1QK=function(_1QL){return function(_1QM,_1QN){var _1QO=E(_1QM),_1QP=E(_1QN);switch(B(_1L5(new T(function(){return B(_1QC(new T(function(){return B(_nO(new T(function(){return B(_1QI(_1QL));})));}),_1QL));}),_1QO[1],_1QP[1]))){case 0:return false;case 1:return new F(function(){return _1QF(_1QO[2],_1QP[2]);});break;default:return true;}};},_1QQ=new T(function(){return B(_1QK(_1PG));}),_1QR=function(_1QS,_1QT,_1QU){var _1QV=E(_1QS);if(_1QV==1){var _1QW=E(_1QU);return _1QW[0]==0?[0,new T(function(){return [0,1,E(E(_1QT)),E(_Cg),E(_Cg)];}),_9,_9]:!B(A(_1QQ,[_1QT,_1QW[1]]))?[0,new T(function(){return [0,1,E(E(_1QT)),E(_Cg),E(_Cg)];}),_1QW,_9]:[0,new T(function(){return [0,1,E(E(_1QT)),E(_Cg),E(_Cg)];}),_9,_1QW];}else{var _1QX=B(_1QR(_1QV>>1,_1QT,_1QU)),_1QY=_1QX[1],_1QZ=_1QX[3],_1R0=E(_1QX[2]);if(!_1R0[0]){return [0,_1QY,_9,_1QZ];}else{var _1R1=_1R0[1],_1R2=E(_1R0[2]);if(!_1R2[0]){return [0,new T(function(){return B(_DD(_1R1,_1QY));}),_9,_1QZ];}else{var _1R3=_1R2[1];if(!B(A(_1QQ,[_1R1,_1R3]))){var _1R4=B(_1QR(_1QV>>1,_1R3,_1R2[2]));return [0,new T(function(){return B(_Eh(_1R1,_1QY,_1R4[1]));}),_1R4[2],_1R4[3]];}else{return [0,_1QY,_9,_1R0];}}}}},_1R5=function(_1R6,_1R7){return B(_OT(_1R6,_1R7))==2?false:true;},_1R8=function(_1R9){return function(_1Ra,_1Rb){var _1Rc=E(_1Ra),_1Rd=E(_1Rb);switch(B(_1L5(new T(function(){return B(_1QC(new T(function(){return B(_nO(new T(function(){return B(_1QI(_1R9));})));}),_1R9));}),_1Rc[1],_1Rd[1]))){case 0:return true;case 1:return new F(function(){return _1R5(_1Rc[2],_1Rd[2]);});break;default:return false;}};},_1Re=function(_1Rf,_1Rg,_1Rh,_1Ri){return !B(A(_1R8,[_1Rg,_1Rh,_1Ri]))?E(_1Rh):E(_1Ri);},_1Rj=function(_1Rk,_1Rl,_1Rm,_1Rn){return !B(A(_1R8,[_1Rl,_1Rm,_1Rn]))?E(_1Rn):E(_1Rm);},_1Ro=function(_1Rp,_1Rq){return B(_OT(_1Rp,_1Rq))==0?true:false;},_1Rr=function(_1Rs){return function(_1Rt,_1Ru){var _1Rv=E(_1Rt),_1Rw=E(_1Ru);switch(B(_1L5(new T(function(){return B(_1QC(new T(function(){return B(_nO(new T(function(){return B(_1QI(_1Rs));})));}),_1Rs));}),_1Rv[1],_1Rw[1]))){case 0:return true;case 1:return new F(function(){return _1Ro(_1Rv[2],_1Rw[2]);});break;default:return false;}};},_1Rx=function(_1Ry,_1Rz){return B(_OT(_1Ry,_1Rz))==2?true:false;},_1RA=function(_1RB){return function(_1RC,_1RD){var _1RE=E(_1RC),_1RF=E(_1RD);switch(B(_1L5(new T(function(){return B(_1QC(new T(function(){return B(_nO(new T(function(){return B(_1QI(_1RB));})));}),_1RB));}),_1RE[1],_1RF[1]))){case 0:return false;case 1:return new F(function(){return _1Rx(_1RE[2],_1RF[2]);});break;default:return true;}};},_1RG=function(_1RH){return function(_1RI,_1RJ){var _1RK=E(_1RI),_1RL=E(_1RJ);switch(B(_1L5(new T(function(){return B(_1QC(new T(function(){return B(_nO(new T(function(){return B(_1QI(_1RH));})));}),_1RH));}),_1RK[1],_1RL[1]))){case 0:return 0;case 1:return new F(function(){return _OT(_1RK[2],_1RL[2]);});break;default:return 2;}};},_1RM=function(_1RN,_1RO){return [0,_1RN,new T(function(){return B(_1RG(_1RO));}),new T(function(){return B(_1Rr(_1RO));}),new T(function(){return B(_1QK(_1RO));}),new T(function(){return B(_1RA(_1RO));}),new T(function(){return B(_1R8(_1RO));}),function(_nQ,_nR){return new F(function(){return _1Re(_1RN,_1RO,_nQ,_nR);});},function(_nQ,_nR){return new F(function(){return _1Rj(_1RN,_1RO,_nQ,_nR);});}];},_1RP=function(_1RQ,_1RR,_1RS,_1RT,_1RU){return !B(_nq(new T(function(){return B(_nO(_1RQ));}),_1RR,_1RT))?true:!B(_4b(_1RS,_1RU))?true:false;},_1RV=function(_1RW,_1RX,_1RY){var _1RZ=E(_1RX),_1S0=E(_1RY);return new F(function(){return _1RP(_1RW,_1RZ[1],_1RZ[2],_1S0[1],_1S0[2]);});},_1S1=function(_1S2){return function(_1S3,_1S4){var _1S5=E(_1S3),_1S6=E(_1S4);return !B(_nq(new T(function(){return B(_nO(_1S2));}),_1S5[1],_1S6[1]))?false:B(_4b(_1S5[2],_1S6[2]));};},_1S7=function(_1S8){return [0,new T(function(){return B(_1S1(_1S8));}),function(_nQ,_nR){return new F(function(){return _1RV(_1S8,_nQ,_nR);});}];},_1S9=new T(function(){return B(_1S7(_1PF));}),_1Sa=new T(function(){return B(_1RM(_1S9,_1PG));}),_1Sb=function(_1Sc,_1Sd,_1Se){var _1Sf=E(_1Sd),_1Sg=E(_1Se);if(!_1Sg[0]){var _1Sh=_1Sg[2],_1Si=_1Sg[3],_1Sj=_1Sg[4];switch(B(A(_1L3,[_1Sc,_1Sf,_1Sh]))){case 0:return new F(function(){return _Cl(_1Sh,B(_1Sb(_1Sc,_1Sf,_1Si)),_1Sj);});break;case 1:return [0,_1Sg[1],E(_1Sf),E(_1Si),E(_1Sj)];default:return new F(function(){return _CX(_1Sh,_1Si,B(_1Sb(_1Sc,_1Sf,_1Sj)));});}}else{return [0,1,E(_1Sf),E(_Cg),E(_Cg)];}},_1Sk=function(_1Sl,_1Sm){while(1){var _1Sn=E(_1Sm);if(!_1Sn[0]){return E(_1Sl);}else{var _1So=B(_1Sb(_1Sa,_1Sn[1],_1Sl));_1Sm=_1Sn[2];_1Sl=_1So;continue;}}},_1Sp=function(_1Sq,_1Sr,_1Ss){return new F(function(){return _1Sk(B(_1Sb(_1Sa,_1Sr,_1Sq)),_1Ss);});},_1St=function(_1Su,_1Sv,_1Sw){while(1){var _1Sx=E(_1Sw);if(!_1Sx[0]){return E(_1Sv);}else{var _1Sy=_1Sx[1],_1Sz=E(_1Sx[2]);if(!_1Sz[0]){return new F(function(){return _DD(_1Sy,_1Sv);});}else{var _1SA=_1Sz[1];if(!B(A(_1QQ,[_1Sy,_1SA]))){var _1SB=B(_1QR(_1Su,_1SA,_1Sz[2])),_1SC=_1SB[1],_1SD=E(_1SB[3]);if(!_1SD[0]){var _1SE=_1Su<<1,_1SF=B(_Eh(_1Sy,_1Sv,_1SC));_1Sw=_1SB[2];_1Su=_1SE;_1Sv=_1SF;continue;}else{return new F(function(){return _1Sp(B(_Eh(_1Sy,_1Sv,_1SC)),_1SD[1],_1SD[2]);});}}else{return new F(function(){return _1Sp(_1Sv,_1Sy,_1Sz);});}}}}},_1SG=function(_1SH,_1SI,_1SJ,_1SK){var _1SL=E(_1SK);if(!_1SL[0]){return new F(function(){return _DD(_1SJ,_1SI);});}else{var _1SM=_1SL[1];if(!B(A(_1QQ,[_1SJ,_1SM]))){var _1SN=B(_1QR(_1SH,_1SM,_1SL[2])),_1SO=_1SN[1],_1SP=E(_1SN[3]);if(!_1SP[0]){return new F(function(){return _1St(_1SH<<1,B(_Eh(_1SJ,_1SI,_1SO)),_1SN[2]);});}else{return new F(function(){return _1Sp(B(_Eh(_1SJ,_1SI,_1SO)),_1SP[1],_1SP[2]);});}}else{return new F(function(){return _1Sp(_1SI,_1SJ,_1SL);});}}},_1SQ=function(_1SR){var _1SS=E(_1SR);if(!_1SS[0]){return [1];}else{var _1ST=_1SS[1],_1SU=E(_1SS[2]);if(!_1SU[0]){return [0,1,E(E(_1ST)),E(_Cg),E(_Cg)];}else{var _1SV=_1SU[1],_1SW=_1SU[2];if(!B(A(_1QQ,[_1ST,_1SV]))){return new F(function(){return _1SG(1,[0,1,E(E(_1ST)),E(_Cg),E(_Cg)],_1SV,_1SW);});}else{return new F(function(){return _1Sp([0,1,E(E(_1ST)),E(_Cg),E(_Cg)],_1SV,_1SW);});}}}},_1SX=new T(function(){return B(_F(0,1,_9));}),_1SY=new T(function(){return B(unCStr("\u0394_"));}),_1SZ=new T(function(){return B(_e(_1SY,_1SX));}),_1T0=[9,_,_,_1SZ],_1T1=[0,_1T0],_1T2=[1,_1T1,_9],_1T3=new T(function(){return B(unCStr("\u03c6_"));}),_1T4=new T(function(){return B(_e(_1T3,_1SX));}),_1T5=[3,_,_,_1T4],_1T6=[2,_,_1T5],_1T7=[1,_1T6,_9],_1T8=[1,_1T7],_1T9=[0,_1T2,_1T8],_1Ta=new T(function(){return B(_F(0,2,_9));}),_1Tb=new T(function(){return B(_e(_1T3,_1Ta));}),_1Tc=[3,_,_,_1Tb],_1Td=[2,_,_1Tc],_1Te=[1,_1Td,_9],_1Tf=[1,_1Te],_1Tg=new T(function(){return B(_e(_1SY,_1Ta));}),_1Th=[9,_,_,_1Tg],_1Ti=[0,_1Th],_1Tj=[1,_1Ti,_9],_1Tk=[0,_1Tj,_1Tf],_1Tl=[1,_1Tk,_9],_1Tm=[1,_1T9,_1Tl],_1Tn=function(_1To,_1Tp){var _1Tq=E(_1To);if(!_1Tq[0]){return [0];}else{var _1Tr=_1Tq[1],_1Ts=_1Tq[2],_1Tt=function(_1Tu,_1Tv,_1Tw){var _1Tx=E(_1Tv);if(!_1Tx[0]){return [0,_1Ts,_1Tw];}else{var _1Ty=_1Tx[1],_1Tz=new T(function(){var _1TA=B(_1Tt(function(_1TB){return new F(function(){return A(_1Tu,[[1,_1Ty,_1TB]]);});},_1Tx[2],_1Tw));return [0,_1TA[1],_1TA[2]];}),_1TC=new T(function(){return E(E(_1Tz)[1]);});return [0,[1,_1Ty,_1TC],[1,new T(function(){return B(A(_1Tu,[[1,_1Tr,[1,_1Ty,_1TC]]]));}),new T(function(){return E(E(_1Tz)[2]);})]];}},_1TD=function(_1TE){var _1TF=E(_1TE);return _1TF[0]==0?E(new T(function(){return B(_1Tn(_1Ts,[1,_1Tr,_1Tp]));})):E(B(_1Tt(_5n,_1TF[1],new T(function(){return B(_1TD(_1TF[2]));})))[2]);};return new F(function(){return _1TD([1,_1Tp,new T(function(){return B(_1Tn(_1Tp,_9));})]);});}},_1TG=new T(function(){return B(_1Tn(_1Tm,_9));}),_1TH=[1,_1Tm,_1TG],_1TI=[9,_,_1fm,_1T6,_1Td],_1TJ=[1,_1TI,_9],_1TK=[1,_1TJ],_1TL=[1,_1T1,_1Tj],_1TM=[0,_1TL,_1TK],_1TN=function(_1TO){return [0,_1TO,_1TM];},_1TP=new T(function(){return B(_f2(_1TN,_1TH));}),_1TQ=[0,_1TP,_1KF],_1TR=[1,_1T9,_9],_1TS=[9,_,_1ht,_1T6,_1Td],_1TT=[1,_1TS,_9],_1TU=[1,_1TT],_1TV=[0,_1T2,_1TU],_1TW=[0,_1TR,_1TV],_1TX=[9,_,_1ht,_1Td,_1T6],_1TY=[1,_1TX,_9],_1TZ=[1,_1TY],_1U0=[0,_1T2,_1TZ],_1U1=[0,_1TR,_1U0],_1U2=[1,_1U1,_9],_1U3=[1,_1TW,_1U2],_1U4=[0,_1U3,_1KE],_1U5=[9,_,_1kc,_1Td,_1T6],_1U6=[1,_1U5,_9],_1U7=[1,_1U6],_1U8=[0,_1T2,_1U7],_1U9=[9,_,_1iQ,_1T6,_1Td],_1Ua=[1,_1U9,_9],_1Ub=[1,_1Ua],_1Uc=[0,_1T2,_1Ub],_1Ud=[1,_1Uc,_9],_1Ue=[0,_1Ud,_1U8],_1Uf=[9,_,_1kc,_1T6,_1Td],_1Ug=[1,_1Uf,_9],_1Uh=[1,_1Ug],_1Ui=[0,_1T2,_1Uh],_1Uj=[0,_1Ud,_1Ui],_1Uk=[1,_1Uj,_9],_1Ul=[1,_1Ue,_1Uk],_1Um=[0,_1Ul,_1KG],_1Un=[1,_1Um,_9],_1Uo=[0,_1Tj,_1Uh],_1Up=[1,_1Uo,_9],_1Uq=[1,_1U8,_1Up],_1Ur=new T(function(){return B(_1Tn(_1Uq,_9));}),_1Us=[1,_1Uq,_1Ur],_1Ut=[0,_1TL,_1Ub],_1Uu=function(_1Uv){return [0,_1Uv,_1Ut];},_1Uw=new T(function(){return B(_f2(_1Uu,_1Us));}),_1Ux=[0,_1Uw,_1KU],_1Uy=[1,_1Ux,_1Un],_1Uz=[0,_1TR,_1T9],_1UA=[1,_1Uz,_9],_1UB=[0,_1UA,_1KS],_1UC=[1,_1UB,_1Uy],_1UD=[1,_1T8,_1T2],_1UE=[0,_1UD,_1Tf],_1UF=[7,_,_1lA,_1Td],_1UG=[1,_1UF,_9],_1UH=[1,_1UG],_1UI=[1,_1T8,_1Tj],_1UJ=[0,_1UI,_1UH],_1UK=[1,_1UJ,_9],_1UL=[1,_1UE,_1UK],_1UM=new T(function(){return B(_1Tn(_1UL,_9));}),_1UN=[7,_,_1lA,_1T6],_1UO=[1,_1UN,_9],_1UP=[1,_1UO],_1UQ=[0,_1TL,_1UP],_1UR=[0,_1TL,_1T8],_1US=function(_1UT){return [0,_1UT,_1UR];},_1UU=[0,_1T2,_1Tf],_1UV=[1,_1UU,_9],_1UW=[0,_1Tj,_1UH],_1UX=[1,_1UW,_1UV],_1UY=new T(function(){return B(_1Tn(_1UX,_9));}),_1UZ=[1,_1UX,_1UY],_1V0=new T(function(){return B(_f2(_1US,_1UZ));}),_1V1=function(_1V2){var _1V3=E(_1V2);return _1V3[0]==0?E(_1V0):[1,[0,_1V3[1],_1UR],new T(function(){return B(_1V1(_1V3[2]));})];},_1V4=function(_1V5,_1V6){return [1,[0,_1V5,_1UR],new T(function(){return B(_1V1(_1V6));})];},_1V7=[1,_1UP,_1Tj],_1V8=[0,_1V7,_1UH],_1V9=[1,_1V8,_1UV],_1Va=new T(function(){return B(_1Tn(_1V9,_9));}),_1Vb=new T(function(){return B(_1V4(_1V9,_1Va));}),_1Vc=function(_1Vd){var _1Ve=E(_1Vd);return _1Ve[0]==0?E(_1Vb):[1,[0,_1Ve[1],_1UR],new T(function(){return B(_1Vc(_1Ve[2]));})];},_1Vf=function(_1Vg,_1Vh){return [1,[0,_1Vg,_1UR],new T(function(){return B(_1Vc(_1Vh));})];},_1Vi=[1,_1UP,_1T2],_1Vj=[0,_1Vi,_1Tf],_1Vk=[1,_1Vj,_9],_1Vl=[1,_1UW,_1Vk],_1Vm=new T(function(){return B(_1Tn(_1Vl,_9));}),_1Vn=new T(function(){return B(_1Vf(_1Vl,_1Vm));}),_1Vo=function(_1Vp){var _1Vq=E(_1Vp);return _1Vq[0]==0?E(_1Vn):[1,[0,_1Vq[1],_1UR],new T(function(){return B(_1Vo(_1Vq[2]));})];},_1Vr=function(_1Vs,_1Vt){return [1,[0,_1Vs,_1UR],new T(function(){return B(_1Vo(_1Vt));})];},_1Vu=[1,_1V8,_1Vk],_1Vv=new T(function(){return B(_1Tn(_1Vu,_9));}),_1Vw=new T(function(){return B(_1Vr(_1Vu,_1Vv));}),_1Vx=function(_1Vy){var _1Vz=E(_1Vy);return _1Vz[0]==0?E(_1Vw):[1,[0,_1Vz[1],_1UQ],new T(function(){return B(_1Vx(_1Vz[2]));})];},_1VA=function(_1VB,_1VC){return [1,[0,_1VB,_1UQ],new T(function(){return B(_1Vx(_1VC));})];},_1VD=[1,_1UW,_9],_1VE=[1,_1UU,_1VD],_1VF=new T(function(){return B(_1Tn(_1VE,_9));}),_1VG=new T(function(){return B(_1VA(_1VE,_1VF));}),_1VH=function(_1VI){var _1VJ=E(_1VI);return _1VJ[0]==0?E(_1VG):[1,[0,_1VJ[1],_1UQ],new T(function(){return B(_1VH(_1VJ[2]));})];},_1VK=function(_1VL,_1VM){return [1,[0,_1VL,_1UQ],new T(function(){return B(_1VH(_1VM));})];},_1VN=[1,_1UE,_1VD],_1VO=new T(function(){return B(_1Tn(_1VN,_9));}),_1VP=new T(function(){return B(_1VK(_1VN,_1VO));}),_1VQ=function(_1VR){var _1VS=E(_1VR);return _1VS[0]==0?E(_1VP):[1,[0,_1VS[1],_1UQ],new T(function(){return B(_1VQ(_1VS[2]));})];},_1VT=function(_1VU,_1VV){return [1,[0,_1VU,_1UQ],new T(function(){return B(_1VQ(_1VV));})];},_1VW=[1,_1UU,_1UK],_1VX=new T(function(){return B(_1Tn(_1VW,_9));}),_1VY=new T(function(){return B(_1VT(_1VW,_1VX));}),_1VZ=function(_1W0){var _1W1=E(_1W0);return _1W1[0]==0?E(_1VY):[1,[0,_1W1[1],_1UQ],new T(function(){return B(_1VZ(_1W1[2]));})];},_1W2=function(_1W3,_1W4){return [1,[0,_1W3,_1UQ],new T(function(){return B(_1VZ(_1W4));})];},_1W5=new T(function(){return B(_1W2(_1UL,_1UM));}),_1W6=[0,_1W5,_1KR],_1W7=[1,_1W6,_1UC],_1W8=[1,_1U4,_1W7],_1W9=[0,83],_1Wa=[1,_1W9,_9],_1Wb=[0,_1T2,_1TK],_1Wc=[1,_1Wb,_9],_1Wd=[0,_1Wc,_1T9],_1We=[0,_1Wc,_1UU],_1Wf=[1,_1We,_9],_1Wg=[1,_1Wd,_1Wf],_1Wh=[0,_1Wg,_1Wa],_1Wi=[1,_1Wh,_1W8],_1Wj=[1,_1U0,_1VD],_1Wk=new T(function(){return B(_1Tn(_1Wj,_9));}),_1Wl=[0,_1Tj,_1UP],_1Wm=[1,_1Wl,_9],_1Wn=[1,_1U0,_1Wm],_1Wo=new T(function(){return B(_1Tn(_1Wn,_9));}),_1Wp=[1,_1Wn,_1Wo],_1Wq=[0,_1TL,_1Tf],_1Wr=function(_1Ws){return [0,_1Ws,_1Wq];},_1Wt=new T(function(){return B(_f2(_1Wr,_1Wp));}),_1Wu=function(_1Wv){var _1Ww=E(_1Wv);return _1Ww[0]==0?E(_1Wt):[1,[0,_1Ww[1],_1UR],new T(function(){return B(_1Wu(_1Ww[2]));})];},_1Wx=function(_1Wy,_1Wz){return [1,[0,_1Wy,_1UR],new T(function(){return B(_1Wu(_1Wz));})];},_1WA=new T(function(){return B(_1Wx(_1Wj,_1Wk));}),_1WB=[0,_1WA,_1KO],_1WC=[1,_1WB,_1Wi],_1WD=[0,_1T2,_1UH],_1WE=[1,_1WD,_1Up],_1WF=new T(function(){return B(_1Tn(_1WE,_9));}),_1WG=[1,_1WE,_1WF],_1WH=function(_1WI){return [0,_1WI,_1UQ];},_1WJ=new T(function(){return B(_f2(_1WH,_1WG));}),_1WK=[0,_1WJ,_1KP],_1WL=[1,_1WK,_1WC],_1WM=[1,_1T9,_1Up],_1WN=new T(function(){return B(_1Tn(_1WM,_9));}),_1WO=[1,_1WM,_1WN],_1WP=new T(function(){return B(_f2(_1Wr,_1WO));}),_1WQ=[0,_1WP,_1KQ],_1WR=[1,_1WQ,_1WL],_1WS=[1,_1UE,_9],_1WT=[0,_1WS,_1Ui],_1WU=[0,_1UV,_1Ui],_1WV=[1,_1WU,_9],_1WW=[1,_1WT,_1WV],_1WX=[0,_1WW,_1KT],_1WY=[1,_1WX,_1WR],_1WZ=[1,_1TQ,_1WY],_1X0=new T(function(){return B(_1SQ(_1WZ));}),_1X1=[0,_1L0,_1X0],_1X2=[0,0],_1X3=function(_1X4,_1X5){if(_1X4<=_1X5){var _1X6=function(_1X7){return [1,[0,_1X7],new T(function(){if(_1X7!=_1X5){var _1X8=B(_1X6(_1X7+1|0));}else{var _1X8=[0];}var _1X9=_1X8;return _1X9;})];};return new F(function(){return _1X6(_1X4);});}else{return [0];}},_1Xa=[0,42],_1Xb=[1,_1Xa,_9],_1Xc=[0,_1Xb,_9],_1Xd=[1,_1Xc,_9],_1Xe=new T(function(){return B(unCStr("lneg"));}),_1Xf=new T(function(){return B(unCStr("lor"));}),_1Xg=[1,_1Xe,_9],_1Xh=new T(function(){return B(unCStr("liff"));}),_1Xi=[1,_1Xh,_1Xg],_1Xj=new T(function(){return B(unCStr("lif"));}),_1Xk=[1,_1Xj,_1Xi],_1Xl=[1,_1Xf,_1Xk],_1Xm=[1,_1Xh,_9],_1Xn=[1,_1Xj,_1Xm],_1Xo=[1,_1Xf,_1Xn],_1Xp=new T(function(){return B(unCStr("land"));}),_1Xq=function(_1Xr){var _1Xs=E(_1Xr);if(!_1Xs){return E(_1Xd);}else{var _1Xt=_1Xs-1|0,_1Xu=function(_1Xv){while(1){var _1Xw=(function(_1Xx){var _1Xy=E(_1Xx);if(!_1Xy[0]){return [0];}else{var _1Xz=_1Xy[2],_1XA=E(_1Xy[1])[1],_1XB=new T(function(){return B(_1Xq(_1XA));}),_1XC=new T(function(){return B(_1Xq(_1Xt-_1XA|0));}),_1XD=function(_1XE){while(1){var _1XF=(function(_1XG){var _1XH=E(_1XG);if(!_1XH[0]){return [0];}else{var _1XI=_1XH[1],_1XJ=_1XH[2],_1XK=function(_1XL){while(1){var _1XM=(function(_1XN){var _1XO=E(_1XN);if(!_1XO[0]){return [0];}else{var _1XP=_1XO[1],_1XQ=_1XO[2],_1XR=[0,_1XI,[1,_1XP,_9]],_1XS=E(_1XC);if(!_1XS[0]){_1XL=_1XQ;return null;}else{var _1XT=_1XS[2];return !E(new T(function(){return B(_4b(_1XI,_1Xe));}))?[1,[0,_1XI,[1,_1XP,[1,_1XS[1],_9]]],new T(function(){var _1XU=function(_1XV){var _1XW=E(_1XV);return _1XW[0]==0?[0]:[1,[0,_1XI,[1,_1XP,[1,_1XW[1],_9]]],new T(function(){return B(_1XU(_1XW[2]));})];};return B(_e(B(_1XU(_1XT)),new T(function(){return B(_1XK(_1XQ));},1)));})]:[1,_1XR,new T(function(){var _1XX=function(_1XY){var _1XZ=E(_1XY);return _1XZ[0]==0?[0]:[1,_1XR,new T(function(){return B(_1XX(_1XZ[2]));})];};return B(_e(B(_1XX(_1XT)),new T(function(){return B(_1XK(_1XQ));},1)));})];}}})(_1XL);if(_1XM!=null){return _1XM;}}},_1Y0=B(_1XK(_1XB));if(!_1Y0[0]){_1XE=_1XJ;return null;}else{return [1,_1Y0[1],new T(function(){return B(_e(_1Y0[2],new T(function(){return B(_1XD(_1XJ));},1)));})];}}})(_1XE);if(_1XF!=null){return _1XF;}}},_1Y1=function(_1Y2,_1Y3){var _1Y4=function(_1Y5){while(1){var _1Y6=(function(_1Y7){var _1Y8=E(_1Y7);if(!_1Y8[0]){return [0];}else{var _1Y9=_1Y8[1],_1Ya=_1Y8[2],_1Yb=[0,_1Y2,[1,_1Y9,_9]],_1Yc=E(_1XC);if(!_1Yc[0]){_1Y5=_1Ya;return null;}else{var _1Yd=_1Yc[2];return !E(new T(function(){return B(_4b(_1Y2,_1Xe));}))?[1,[0,_1Y2,[1,_1Y9,[1,_1Yc[1],_9]]],new T(function(){var _1Ye=function(_1Yf){var _1Yg=E(_1Yf);return _1Yg[0]==0?[0]:[1,[0,_1Y2,[1,_1Y9,[1,_1Yg[1],_9]]],new T(function(){return B(_1Ye(_1Yg[2]));})];};return B(_e(B(_1Ye(_1Yd)),new T(function(){return B(_1Y4(_1Ya));},1)));})]:[1,_1Yb,new T(function(){var _1Yh=function(_1Yi){var _1Yj=E(_1Yi);return _1Yj[0]==0?[0]:[1,_1Yb,new T(function(){return B(_1Yh(_1Yj[2]));})];};return B(_e(B(_1Yh(_1Yd)),new T(function(){return B(_1Y4(_1Ya));},1)));})];}}})(_1Y5);if(_1Y6!=null){return _1Y6;}}},_1Yk=B(_1Y4(_1XB));return _1Yk[0]==0?B(_1XD(_1Y3)):[1,_1Yk[1],new T(function(){return B(_e(_1Yk[2],new T(function(){return B(_1XD(_1Y3));},1)));})];};if(_1XA!=_1Xt){var _1Yl=B(_1Y1(_1Xp,_1Xo));if(!_1Yl[0]){_1Xv=_1Xz;return null;}else{return [1,_1Yl[1],new T(function(){return B(_e(_1Yl[2],new T(function(){return B(_1Xu(_1Xz));},1)));})];}}else{var _1Ym=B(_1Y1(_1Xp,_1Xl));if(!_1Ym[0]){_1Xv=_1Xz;return null;}else{return [1,_1Ym[1],new T(function(){return B(_e(_1Ym[2],new T(function(){return B(_1Xu(_1Xz));},1)));})];}}}})(_1Xv);if(_1Xw!=null){return _1Xw;}}};return new F(function(){return _1Xu(B(_1X3(0,_1Xt)));});}},_1Yn=function(_1Yo,_1Yp){return !E(_1Yo)?!E(_1Yp)?true:false:E(_1Yp);},_1Yq=function(_1Yr,_1Ys){return !E(_1Yr)?true:E(_1Ys);},_1Yt=function(_1Yu,_1Yv){return !E(_1Yu)?false:E(_1Yv);},_1Yw=function(_1Yx){return !E(_1Yx)?true:false;},_1Yy=function(_1Yz,_1YA){return !E(_1Yz)?E(_1YA):true;},_1YB=function(_1YC,_1YD){switch(E(_1YD)[0]){case 0:return E(_1Yw);case 1:return E(_1Yt);case 2:return E(_1Yy);case 3:return E(_1Yq);default:return E(_1Yn);}},_1YE=function(_1YF,_1YG){return new F(function(){return A(_1YF,[E(_1YG)[2]]);});},_1YH=function(_1YI,_1YJ,_1YK,_1YL){var _1YM=E(_1YL);switch(_1YM[0]){case 0:return E(_1);case 1:return new F(function(){return A(_1YJ,[_1YK,_1YM[1]]);});break;case 2:return new F(function(){return A(_1YI,[_1YK,_1YM[1],new T(function(){return B(_1YH(_1YI,_1YJ,_1YK,_1YM[2]));})]);});break;default:return new F(function(){return A(_1YI,[_1YK,_1YM[1],new T(function(){return B(_1YH(_1YI,_1YJ,_1YK,_1YM[2]));}),new T(function(){return B(_1YH(_1YI,_1YJ,_1YK,_1YM[3]));})]);});}},_1YN=function(_1YO,_1YP,_1YQ,_1YR,_1YS,_1YT,_1YU){var _1YV=E(_1YU);switch(_1YV[0]){case 0:return E(_1);case 1:return new F(function(){return A(_1YS,[_1YT,_1YV[1]]);});break;case 2:return new F(function(){return A(_1YO,[_1YT,_1YV[1],new T(function(){return B(_1YH(_1YR,_1YS,_1YT,_1YV[2]));})]);});break;case 3:return new F(function(){return A(_1YO,[_1YT,_1YV[1],new T(function(){return B(_1YH(_1YR,_1YS,_1YT,_1YV[2]));}),new T(function(){return B(_1YH(_1YR,_1YS,_1YT,_1YV[3]));})]);});break;case 4:return new F(function(){return A(_1YP,[_1YT,_1YV[1],new T(function(){return B(_1YN(_1YO,_1YP,_1YQ,_1YR,_1YS,_1YT,_1YV[2]));})]);});break;case 5:return new F(function(){return A(_1YP,[_1YT,_1YV[1],new T(function(){return B(_1YN(_1YO,_1YP,_1YQ,_1YR,_1YS,_1YT,_1YV[2]));}),new T(function(){return B(_1YN(_1YO,_1YP,_1YQ,_1YR,_1YS,_1YT,_1YV[3]));})]);});break;default:return new F(function(){return A(_1YQ,[_1YT,_1YV[1],function(_1YW){return new F(function(){return _1YN(_1YO,_1YP,_1YQ,_1YR,_1YS,_1YT,B(A(_1YV[2],[[1,_1YW]])));});}]);});}},_1YX=function(_1YY,_1YZ){return E(_1);},_1Z0=[1,_7h,_9],_1Z1=function(_1Z2){return false;},_1Z3=[1,_1Z1,_9],_1Z4=function(_1Z5){var _1Z6=E(_1Z5);if(!_1Z6){return E(_1Z3);}else{var _1Z7=new T(function(){return B(_1Z4(_1Z6-1|0));}),_1Z8=function(_1Z9){while(1){var _1Za=(function(_1Zb){var _1Zc=E(_1Zb);if(!_1Zc[0]){return [0];}else{var _1Zd=_1Zc[2],_1Ze=function(_1Zf){var _1Zg=E(_1Zf);return _1Zg[0]==0?[0]:[1,function(_1Zh){var _1Zi=E(_1Zh);return _1Zi[1]>=_1Z6?E(_1Zc[1]):B(A(_1Zg[1],[_1Zi]));},new T(function(){return B(_1Ze(_1Zg[2]));})];},_1Zj=B(_1Ze(_1Z7));if(!_1Zj[0]){_1Z9=_1Zd;return null;}else{return [1,_1Zj[1],new T(function(){return B(_e(_1Zj[2],new T(function(){return B(_1Z8(_1Zd));},1)));})];}}})(_1Z9);if(_1Za!=null){return _1Za;}}};return new F(function(){return (function(_1Zk,_1Zl){var _1Zm=function(_1Zn){var _1Zo=E(_1Zn);return _1Zo[0]==0?[0]:[1,function(_1Zp){var _1Zq=E(_1Zp);return _1Zq[1]>=_1Z6?E(_1Zk):B(A(_1Zo[1],[_1Zq]));},new T(function(){return B(_1Zm(_1Zo[2]));})];},_1Zr=B(_1Zm(_1Z7));return _1Zr[0]==0?B(_1Z8(_1Zl)):[1,_1Zr[1],new T(function(){return B(_e(_1Zr[2],new T(function(){return B(_1Z8(_1Zl));},1)));})];})(_7i,_1Z0);});}},_1Zs=function(_1Zt,_1Zu){var _1Zv=function(_1Zw){var _1Zx=E(_1Zw);return _1Zx[0]==0?[0]:[1,new T(function(){return B(_1YN(_1YX,_1YB,_1YX,_1YX,_1YE,_1Zx[1],_1Zu));}),new T(function(){return B(_1Zv(_1Zx[2]));})];};return new F(function(){return _Gf(_5n,B(_1Zv(B(_1Z4(_1Zt)))));});},_1Zy=function(_1Zz,_1ZA){while(1){var _1ZB=E(_1Zz);if(!_1ZB[0]){return E(_1ZA);}else{_1Zz=_1ZB[2];var _1ZC=_1ZA+E(_1ZB[1])[1]|0;_1ZA=_1ZC;continue;}}},_1ZD=function(_1ZE){return [0,B(_1ZF(E(_1ZE)[2]))];},_1ZF=function(_1ZG){var _1ZH=E(_1ZG);if(!_1ZH[0]){return 1;}else{return new F(function(){return _1Zy(B(_f2(_1ZD,_1ZH)),0);});}},_1ZI=function(_1ZJ,_1ZK){var _1ZL=E(_1ZK);return new F(function(){return _1ZM(_1ZJ,_1ZL[1],_1ZL[2]);});},_1ZM=function(_1ZN,_1ZO,_1ZP){var _1ZQ=E(_1ZP);if(!_1ZQ[0]){return [1,[0,_,new T(function(){var _1ZR=E(_1ZN);return _1ZR[0]==0?E(_yN):E(_1ZR[1]);})]];}else{var _1ZS=_1ZQ[1],_1ZT=E(_1ZQ[2]);if(!_1ZT[0]){return [4,_1lA,new T(function(){return B(_1ZI(_1ZN,_1ZS));})];}else{if(!E(_1ZT[2])[0]){var _1ZU=new T(function(){var _1ZV=E(_1ZS),_1ZW=_1ZV[2];return B(_1ZM(new T(function(){var _1ZX=B(_1ZF(_1ZW));if(_1ZX>0){var _1ZY=_1ZX<0?[0]:B(_zy(_1ZX,_1ZN));}else{var _1ZY=[0];}var _1ZZ=_1ZY,_200=_1ZZ;return _200;}),_1ZV[1],_1ZW));}),_201=new T(function(){var _202=E(_1ZT[1]);return B(_1ZM(new T(function(){var _203=B(_1ZF(E(_1ZS)[2]));return _203>=0?B(_yQ(_203,_1ZN)):E(_1ZN);}),_202[1],_202[2]));});return !B(_4b(_1ZO,_1Xp))?!B(_4b(_1ZO,_1Xj))?!B(_4b(_1ZO,_1Xh))?!B(_4b(_1ZO,_1Xf))?[5,_1fm,_1ZU,_201]:[5,_1ht,_1ZU,_201]:[5,_1iQ,_1ZU,_201]:[5,_1kc,_1ZU,_201]:[5,_1fm,_1ZU,_201];}else{return [4,_1lA,new T(function(){return B(_1ZI(_1ZN,_1ZS));})];}}}},_204=function(_205,_206){while(1){var _207=E(_206);if(!_207[0]){return E(_205);}else{var _208=_207[2],_209=E(_207[1])[1];if(_205>_209){_206=_208;continue;}else{_205=_209;_206=_208;continue;}}}},_20a=new T(function(){return B(unCStr("maximum"));}),_20b=new T(function(){return B(_yK(_20a));}),_20c=function(_20d){while(1){var _20e=(function(_20f){var _20g=E(_20f);if(!_20g[0]){return [0];}else{var _20h=_20g[2],_20i=E(_20g[1]);if(!_20i[0]){return E(_20b);}else{var _20j=function(_20k){var _20l=E(_20k);return _20l[0]==0?[0]:[1,[1,_20l[1],_20i],new T(function(){return B(_20j(_20l[2]));})];},_20m=B(_20j(B(_1X3(1,B(_204(E(_20i[1])[1],_20i[2]))+1|0))));if(!_20m[0]){_20d=_20h;return null;}else{return [1,_20m[1],new T(function(){return B(_e(_20m[2],new T(function(){return B(_20c(_20h));},1)));})];}}}})(_20d);if(_20e!=null){return _20e;}}},_20n=[0,1],_20o=[1,_20n,_9],_20p=[1,_20o,_9],_20q=function(_20r){var _20s=E(_20r);if(_20s==1){return E(_20p);}else{return new F(function(){return _20c(B(_20q(_20s-1|0)));});}},_20t=function(_20u){while(1){var _20v=(function(_20w){var _20x=E(_20w);if(!_20x[0]){return [0];}else{var _20y=_20x[2],_20z=E(_20x[1]),_20A=_20z[2],_20B=function(_20C){var _20D=E(_20C);return _20D[0]==0?[0]:[1,new T(function(){return B(_1ZM(_20D[1],_20z[1],_20A));}),new T(function(){return B(_20B(_20D[2]));})];},_20E=B(_20B(B(_20q(B(_1ZF(_20A))))));if(!_20E[0]){_20u=_20y;return null;}else{return [1,_20E[1],new T(function(){return B(_e(_20E[2],new T(function(){return B(_20t(_20y));},1)));})];}}})(_20u);if(_20v!=null){return _20v;}}},_20F=function(_20G){return new F(function(){return _kp(function(_20H){return new F(function(){return _1Zs(_20G+1|0,_20H);});},B(_20t(B(_1Xq(_20G)))));});},_20I=function(_20J){return [1,new T(function(){return B(_20F(_20J));}),new T(function(){var _20K=E(_20J);if(_20K==2147483647){var _20L=[0];}else{var _20L=B(_20I(_20K+1|0));}return _20L;})];},_20M=new T(function(){return B(_20I(1));}),_20N=new T(function(){return B(_km(_20M));}),_20O=new T(function(){return B(unCStr("value"));}),_20P=new T(function(){return B(unCStr("textarea"));}),_20Q=new T(function(){return B(unCStr("mainBox"));}),_20R=function(_20S,_){var _20T=jsFind(toJSStr(E(_20Q))),_20U=_20T,_20V=E(_20U);if(!_20V[0]){return _1x;}else{var _20W=jsQuerySelectorAll(E(_20V[1])[1],toJSStr(E(_20P))),_20X=_20W;return new F(function(){return (function(_20Y,_){while(1){var _20Z=E(_20Y);if(!_20Z[0]){return _1x;}else{var _210=B(A(_1JB,[_5n,_20Z[1],_20O,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_20S,_1rN));})));}),_])),_211=_210;_20Y=_20Z[2];continue;}}})(_20X,_);});}},_212=new T(function(){return [0,"click"];}),_213=new T(function(){return B(unCStr("innerHTML"));}),_214=new T(function(){return B(unCStr("div"));}),_215=function(_216,_){var _217=jsCreateElem(toJSStr(E(_214))),_218=_217,_219=jsSet(_218,toJSStr(E(_213)),toJSStr(B(_1rz(_Q,_u,_Q,_N,_Q,_1rp,_216,_1rN)))),_21a=jsSetCB(_218,E(_212)[1],function(_21b,_21c,_){return new F(function(){return _20R(_216,_);});}),_21d=_21a;return [0,_218];},_21e=new T(function(){return B(_f2(_215,_20N));}),_21f=function(_){var _21g=jsElemsByClassName("scrollbox"),_21h=_21g,_21i=nMV(_1X2),_21j=_21i,_21k=[0,_21j],_21l=function(_,_21m){return new F(function(){return _1Kg(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1X1,_);});},_21n=E(_21h);if(!_21n[0]){return new F(function(){return _21l(_,_1x);});}else{var _21o=_21n[1],_21p=E(_1KD)[1],_21q=jsSetCB(E(_21o)[1],_21p,function(_21r,_21s,_){return new F(function(){return _eg(_21k,_21e,E(_21o)[1],_);});}),_21t=_21q,_21u=B((function(_21v,_){while(1){var _21w=(function(_21x,_){var _21y=E(_21x);if(!_21y[0]){return _1x;}else{var _21z=_21y[1],_21A=jsSetCB(E(_21z)[1],_21p,function(_21B,_21C,_){return new F(function(){return _eg(_21k,_21e,E(_21z)[1],_);});}),_21D=_21A;_21v=_21y[2];return null;}})(_21v,_);if(_21w!=null){return _21w;}}})(_21n[2],_)),_21E=_21u;return new F(function(){return _21l(_,_21E);});}},_21F=function(_){return new F(function(){return _21f(_);});};
var hasteMain = function() {B(A(_21F, [0]));};window.onload = hasteMain;