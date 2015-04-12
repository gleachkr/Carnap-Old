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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr("wheel"));}),_1r=new T(function(){return B(unCStr("mouseout"));}),_1s=new T(function(){return B(unCStr("mouseover"));}),_1t=new T(function(){return B(unCStr("mousemove"));}),_1u=new T(function(){return B(unCStr("blur"));}),_1v=new T(function(){return B(unCStr("focus"));}),_1w=new T(function(){return B(unCStr("change"));}),_1x=new T(function(){return B(unCStr("unload"));}),_1y=new T(function(){return B(unCStr("load"));}),_1z=new T(function(){return B(unCStr("submit"));}),_1A=new T(function(){return B(unCStr("keydown"));}),_1B=new T(function(){return B(unCStr("keyup"));}),_1C=new T(function(){return B(unCStr("keypress"));}),_1D=new T(function(){return B(unCStr("mouseup"));}),_1E=new T(function(){return B(unCStr("mousedown"));}),_1F=new T(function(){return B(unCStr("dblclick"));}),_1G=new T(function(){return B(unCStr("click"));}),_1H=function(_1I){switch(E(_1I)[0]){case 0:return E(_1y);case 1:return E(_1x);case 2:return E(_1w);case 3:return E(_1v);case 4:return E(_1u);case 5:return E(_1t);case 6:return E(_1s);case 7:return E(_1r);case 8:return E(_1G);case 9:return E(_1F);case 10:return E(_1E);case 11:return E(_1D);case 12:return E(_1C);case 13:return E(_1B);case 14:return E(_1A);case 15:return E(_1z);default:return E(_1q);}},_1J=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_1K=new T(function(){return B(unCStr("main"));}),_1L=new T(function(){return B(unCStr("EventData"));}),_1M=new T(function(){var _1N=hs_wordToWord64(3703396926),_1O=_1N,_1P=hs_wordToWord64(1660403598),_1Q=_1P;return [0,_1O,_1Q,[0,_1O,_1Q,_1K,_1J,_1L],_9];}),_1R=[0,0],_1S=false,_1T=2,_1U=[1],_1V=new T(function(){return B(unCStr("Dynamic"));}),_1W=new T(function(){return B(unCStr("Data.Dynamic"));}),_1X=new T(function(){return B(unCStr("base"));}),_1Y=new T(function(){var _1Z=hs_wordToWord64(628307645),_20=_1Z,_21=hs_wordToWord64(949574464),_22=_21;return [0,_20,_22,[0,_20,_22,_1X,_1W,_1V],_9];}),_23=[0],_24=new T(function(){return B(unCStr("OnLoad"));}),_25=[0,_24,_23],_26=[0,_1M,_25],_27=[0,_1Y,_26],_28=[0],_29=function(_){return _28;},_2a=function(_2b,_){return _28;},_2c=[0,_29,_2a],_2d=[0,_9,_1R,_1T,_2c,_1S,_27,_1U],_2e=function(_){var _=0,_2f=newMVar(),_2g=_2f,_=putMVar(_2g,_2d);return [0,_2g];},_2h=function(_2i){var _2j=B(A(_2i,[_])),_2k=_2j;return E(_2k);},_2l=new T(function(){return B(_2h(_2e));}),_2m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2n=new T(function(){return B(unCStr("base"));}),_2o=new T(function(){return B(unCStr("PatternMatchFail"));}),_2p=new T(function(){var _2q=hs_wordToWord64(18445595),_2r=_2q,_2s=hs_wordToWord64(52003073),_2t=_2s;return [0,_2r,_2t,[0,_2r,_2t,_2n,_2m,_2o],_9];}),_2u=function(_2v){return E(_2p);},_2w=function(_2x){return E(E(_2x)[1]);},_2y=function(_2z,_2A,_2B){var _2C=B(A(_2z,[_])),_2D=B(A(_2A,[_])),_2E=hs_eqWord64(_2C[1],_2D[1]),_2F=_2E;if(!E(_2F)){return [0];}else{var _2G=hs_eqWord64(_2C[2],_2D[2]),_2H=_2G;return E(_2H)==0?[0]:[1,_2B];}},_2I=function(_2J){var _2K=E(_2J);return new F(function(){return _2y(B(_2w(_2K[1])),_2u,_2K[2]);});},_2L=function(_2M){return E(E(_2M)[1]);},_2N=function(_2O,_2P){return new F(function(){return _e(E(_2O)[1],_2P);});},_2Q=[0,44],_2R=[0,93],_2S=[0,91],_2T=function(_2U,_2V,_2W){var _2X=E(_2V);return _2X[0]==0?B(unAppCStr("[]",_2W)):[1,_2S,new T(function(){return B(A(_2U,[_2X[1],new T(function(){var _2Y=function(_2Z){var _30=E(_2Z);return _30[0]==0?E([1,_2R,_2W]):[1,_2Q,new T(function(){return B(A(_2U,[_30[1],new T(function(){return B(_2Y(_30[2]));})]));})];};return B(_2Y(_2X[2]));})]));})];},_31=function(_32,_33){return new F(function(){return _2T(_2N,_32,_33);});},_34=function(_35,_36,_37){return new F(function(){return _e(E(_36)[1],_37);});},_38=[0,_34,_2L,_31],_39=new T(function(){return [0,_2u,_38,_3a,_2I];}),_3a=function(_3b){return [0,_39,_3b];},_3c=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3d=function(_3e,_3f){return new F(function(){return die(new T(function(){return B(A(_3f,[_3e]));}));});},_3g=function(_3h,_3i){var _3j=E(_3i);if(!_3j[0]){return [0,_9,_9];}else{var _3k=_3j[1];if(!B(A(_3h,[_3k]))){return [0,_9,_3j];}else{var _3l=new T(function(){var _3m=B(_3g(_3h,_3j[2]));return [0,_3m[1],_3m[2]];});return [0,[1,_3k,new T(function(){return E(E(_3l)[1]);})],new T(function(){return E(E(_3l)[2]);})];}}},_3n=[0,32],_3o=[0,10],_3p=[1,_3o,_9],_3q=function(_3r){return E(E(_3r)[1])==124?false:true;},_3s=function(_3t,_3u){var _3v=B(_3g(_3q,B(unCStr(_3t)))),_3w=_3v[1],_3x=function(_3y,_3z){return new F(function(){return _e(_3y,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_3u,new T(function(){return B(_e(_3z,_3p));},1)));})));},1));});},_3A=E(_3v[2]);if(!_3A[0]){return new F(function(){return _3x(_3w,_9);});}else{return E(E(_3A[1])[1])==124?B(_3x(_3w,[1,_3n,_3A[2]])):B(_3x(_3w,_9));}},_3B=function(_3C){return new F(function(){return _3d([0,new T(function(){return B(_3s(_3C,_3c));})],_3a);});},_3D=new T(function(){return B(_3B("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_3E=[0,_1y,_23],_3F=[0,_1M,_3E],_3G=[0,_1x,_23],_3H=[0,_1M,_3G],_3I=[0,_1w,_23],_3J=[0,_1M,_3I],_3K=[0,_1v,_23],_3L=[0,_1M,_3K],_3M=[0,_1u,_23],_3N=[0,_1M,_3M],_3O=[3],_3P=[0,_1r,_3O],_3Q=[0,_1M,_3P],_3R=function(_3S,_3T){switch(E(_3S)[0]){case 0:return function(_){var _3U=E(_2l)[1],_3V=takeMVar(_3U),_3W=_3V,_=putMVar(_3U,new T(function(){var _3X=E(_3W);return [0,_3X[1],_3X[2],_3X[3],_3X[4],_3X[5],_3F,_3X[7]];}));return new F(function(){return A(_3T,[_]);});};case 1:return function(_){var _3Y=E(_2l)[1],_3Z=takeMVar(_3Y),_40=_3Z,_=putMVar(_3Y,new T(function(){var _41=E(_40);return [0,_41[1],_41[2],_41[3],_41[4],_41[5],_3H,_41[7]];}));return new F(function(){return A(_3T,[_]);});};case 2:return function(_){var _42=E(_2l)[1],_43=takeMVar(_42),_44=_43,_=putMVar(_42,new T(function(){var _45=E(_44);return [0,_45[1],_45[2],_45[3],_45[4],_45[5],_3J,_45[7]];}));return new F(function(){return A(_3T,[_]);});};case 3:return function(_){var _46=E(_2l)[1],_47=takeMVar(_46),_48=_47,_=putMVar(_46,new T(function(){var _49=E(_48);return [0,_49[1],_49[2],_49[3],_49[4],_49[5],_3L,_49[7]];}));return new F(function(){return A(_3T,[_]);});};case 4:return function(_){var _4a=E(_2l)[1],_4b=takeMVar(_4a),_4c=_4b,_=putMVar(_4a,new T(function(){var _4d=E(_4c);return [0,_4d[1],_4d[2],_4d[3],_4d[4],_4d[5],_3N,_4d[7]];}));return new F(function(){return A(_3T,[_]);});};case 5:return function(_4e){return function(_){var _4f=E(_2l)[1],_4g=takeMVar(_4f),_4h=_4g,_=putMVar(_4f,new T(function(){var _4i=E(_4h);return [0,_4i[1],_4i[2],_4i[3],_4i[4],_4i[5],[0,_1M,[0,_1t,[2,E(_4e)]]],_4i[7]];}));return new F(function(){return A(_3T,[_]);});};};case 6:return function(_4j){return function(_){var _4k=E(_2l)[1],_4l=takeMVar(_4k),_4m=_4l,_=putMVar(_4k,new T(function(){var _4n=E(_4m);return [0,_4n[1],_4n[2],_4n[3],_4n[4],_4n[5],[0,_1M,[0,_1s,[2,E(_4j)]]],_4n[7]];}));return new F(function(){return A(_3T,[_]);});};};case 7:return function(_){var _4o=E(_2l)[1],_4p=takeMVar(_4o),_4q=_4p,_=putMVar(_4o,new T(function(){var _4r=E(_4q);return [0,_4r[1],_4r[2],_4r[3],_4r[4],_4r[5],_3Q,_4r[7]];}));return new F(function(){return A(_3T,[_]);});};case 8:return function(_4s,_4t){return function(_){var _4u=E(_2l)[1],_4v=takeMVar(_4u),_4w=_4v,_=putMVar(_4u,new T(function(){var _4x=E(_4w);return [0,_4x[1],_4x[2],_4x[3],_4x[4],_4x[5],[0,_1M,[0,_1G,[1,_4s,E(_4t)]]],_4x[7]];}));return new F(function(){return A(_3T,[_]);});};};case 9:return function(_4y,_4z){return function(_){var _4A=E(_2l)[1],_4B=takeMVar(_4A),_4C=_4B,_=putMVar(_4A,new T(function(){var _4D=E(_4C);return [0,_4D[1],_4D[2],_4D[3],_4D[4],_4D[5],[0,_1M,[0,_1F,[1,_4y,E(_4z)]]],_4D[7]];}));return new F(function(){return A(_3T,[_]);});};};case 10:return function(_4E,_4F){return function(_){var _4G=E(_2l)[1],_4H=takeMVar(_4G),_4I=_4H,_=putMVar(_4G,new T(function(){var _4J=E(_4I);return [0,_4J[1],_4J[2],_4J[3],_4J[4],_4J[5],[0,_1M,[0,_1E,[1,_4E,E(_4F)]]],_4J[7]];}));return new F(function(){return A(_3T,[_]);});};};case 11:return function(_4K,_4L){return function(_){var _4M=E(_2l)[1],_4N=takeMVar(_4M),_4O=_4N,_=putMVar(_4M,new T(function(){var _4P=E(_4O);return [0,_4P[1],_4P[2],_4P[3],_4P[4],_4P[5],[0,_1M,[0,_1D,[1,_4K,E(_4L)]]],_4P[7]];}));return new F(function(){return A(_3T,[_]);});};};case 12:return function(_4Q,_){var _4R=E(_2l)[1],_4S=takeMVar(_4R),_4T=_4S,_=putMVar(_4R,new T(function(){var _4U=E(_4T);return [0,_4U[1],_4U[2],_4U[3],_4U[4],_4U[5],[0,_1M,[0,_1C,[4,_4Q]]],_4U[7]];}));return new F(function(){return A(_3T,[_]);});};case 13:return function(_4V,_){var _4W=E(_2l)[1],_4X=takeMVar(_4W),_4Y=_4X,_=putMVar(_4W,new T(function(){var _4Z=E(_4Y);return [0,_4Z[1],_4Z[2],_4Z[3],_4Z[4],_4Z[5],[0,_1M,[0,_1B,[4,_4V]]],_4Z[7]];}));return new F(function(){return A(_3T,[_]);});};case 14:return function(_50,_){var _51=E(_2l)[1],_52=takeMVar(_51),_53=_52,_=putMVar(_51,new T(function(){var _54=E(_53);return [0,_54[1],_54[2],_54[3],_54[4],_54[5],[0,_1M,[0,_1A,[4,_50]]],_54[7]];}));return new F(function(){return A(_3T,[_]);});};default:return E(_3D);}},_55=[0,_1H,_3R],_56=function(_57,_58,_){var _59=jsCreateTextNode(toJSStr(E(_57))),_5a=_59,_5b=jsAppendChild(_5a,E(_58)[1]);return [0,_5a];},_5c=0,_5d=function(_5e,_5f,_5g,_5h){return new F(function(){return A(_5e,[function(_){var _5i=jsSetAttr(E(_5f)[1],toJSStr(E(_5g)),toJSStr(E(_5h)));return _5c;}]);});},_5j=[0,112],_5k=function(_5l){var _5m=new T(function(){return E(E(_5l)[2]);});return function(_5n,_){return [0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_5m)[1],_9)),new T(function(){return E(E(_5l)[1]);},1)));})],new T(function(){var _5o=E(_5l);return [0,_5o[1],new T(function(){return [0,E(_5m)[1]+1|0];}),_5o[3],_5o[4],_5o[5],_5o[6],_5o[7]];})];};},_5p=new T(function(){return B(unCStr("id"));}),_5q=function(_5r){return E(_5r);},_5s=new T(function(){return B(unCStr("noid"));}),_5t=function(_5u,_){return _5u;},_5v=function(_5w,_5x,_){var _5y=jsFind(toJSStr(E(_5x))),_5z=_5y,_5A=E(_5z);if(!_5A[0]){var _5B=E(_2l)[1],_5C=takeMVar(_5B),_5D=_5C,_5E=B(A(_5w,[_5D,_])),_5F=_5E,_5G=E(_5F),_=putMVar(_5B,_5G[2]);return E(_5G[1])[2];}else{var _5H=E(_5A[1]),_5I=jsClearChildren(_5H[1]),_5J=E(_2l)[1],_5K=takeMVar(_5J),_5L=_5K,_5M=B(A(_5w,[_5L,_])),_5N=_5M,_5O=E(_5N),_5P=E(_5O[1]),_=putMVar(_5J,_5O[2]),_5Q=B(A(_5P[1],[_5H,_])),_5R=_5Q;return _5P[2];}},_5S=new T(function(){return B(unCStr("span"));}),_5T=function(_5U,_5V,_5W,_){var _5X=jsCreateElem(toJSStr(E(_5S))),_5Y=_5X,_5Z=jsAppendChild(_5Y,E(_5W)[1]),_60=[0,_5Y],_61=B(A(_5U,[_5V,_60,_])),_62=_61;return _60;},_63=function(_64){return E(_64);},_65=function(_66,_67,_68,_){var _69=B(A(_5k,[_68,_68,_])),_6a=_69,_6b=E(_6a),_6c=_6b[1],_6d=E(_6b[2]),_6e=_6d[2],_6f=E(_6d[4]),_6g=B(A(_66,[[0,_6d[1],_6e,_6d[3],[0,function(_){return new F(function(){return _5v(function(_6h,_){var _6i=B(A(_66,[new T(function(){var _6j=E(_6h);return [0,_6j[1],_6e,_6j[3],_6j[4],_6j[5],_6j[6],_6j[7]];}),_])),_6k=_6i;return [0,[0,_5t,E(E(_6k)[1])[2]],_6h];},_5s,_);});},function(_6l,_){var _6m=B(_5v(new T(function(){return B(A(_67,[_6l]));},1),_6c,_)),_6n=_6m,_6o=E(_6n);return _6o[0]==0?_28:B(A(_6f[2],[_6o[1],_]));}],_6d[5],_6d[6],_6d[7]],_])),_6p=_6g,_6q=E(_6p),_6r=_6q[2],_6s=E(_6q[1]),_6t=_6s[1],_6u=E(_6s[2]);if(!_6u[0]){return [0,[0,function(_6v,_){var _6w=B(A(_6t,[_6v,_])),_6x=_6w;if(!E(E(_68)[5])){var _6y=B(_5T(_63,_5t,_6v,_)),_6z=_6y,_6A=B(A(_5d,[_5q,_6z,_5p,_6c,_])),_6B=_6A;return _6v;}else{return _6v;}},_28],new T(function(){var _6C=E(_6r);return [0,_6C[1],_6C[2],_6C[3],_6f,_6C[5],_6C[6],_6C[7]];})];}else{var _6D=B(A(_67,[_6u[1],new T(function(){var _6E=E(_6r);return [0,_6E[1],_6E[2],_6E[3],_6f,_6E[5],_6E[6],_6E[7]];}),_])),_6F=_6D,_6G=E(_6F),_6H=E(_6G[1]),_6I=_6H[1];return [0,[0,function(_6J,_){var _6K=B(A(_6t,[_6J,_])),_6L=_6K;if(!E(E(_68)[5])){var _6M=B(_5T(_63,_6I,_6J,_)),_6N=_6M,_6O=B(A(_5d,[_5q,_6N,_5p,_6c,_])),_6P=_6O;return _6J;}else{var _6Q=B(A(_6I,[_6J,_])),_6R=_6Q;return _6J;}},_6H[2]],_6G[2]];}},_6S=function(_6T,_6U){switch(E(_6T)[0]){case 0:switch(E(_6U)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_6U)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_6U)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_6U)[0]==3?1:2;}},_6V=new T(function(){return B(unCStr("end of input"));}),_6W=new T(function(){return B(unCStr("unexpected"));}),_6X=new T(function(){return B(unCStr("expecting"));}),_6Y=new T(function(){return B(unCStr("unknown parse error"));}),_6Z=new T(function(){return B(unCStr("or"));}),_70=[0,58],_71=[0,34],_72=[0,41],_73=[1,_72,_9],_74=function(_75,_76,_77){var _78=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_76,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_77,_9)),_73));})));},1)));})));}),_79=E(_75);return _79[0]==0?E(_78):[1,_71,new T(function(){return B(_e(_79,new T(function(){return B(unAppCStr("\" ",_78));},1)));})];},_7a=function(_7b,_7c){while(1){var _7d=E(_7b);if(!_7d[0]){return E(_7c)[0]==0?true:false;}else{var _7e=E(_7c);if(!_7e[0]){return false;}else{if(E(_7d[1])[1]!=E(_7e[1])[1]){return false;}else{_7b=_7d[2];_7c=_7e[2];continue;}}}}},_7f=function(_7g,_7h){return !B(_7a(_7g,_7h))?true:false;},_7i=[0,_7a,_7f],_7j=function(_7k,_7l,_7m){var _7n=E(_7m);if(!_7n[0]){return E(_7l);}else{return new F(function(){return _e(_7l,new T(function(){return B(_e(_7k,new T(function(){return B(_7j(_7k,_7n[1],_7n[2]));},1)));},1));});}},_7o=function(_7p){return E(_7p)[0]==0?false:true;},_7q=new T(function(){return B(unCStr(", "));}),_7r=function(_7s){var _7t=E(_7s);if(!_7t[0]){return [0];}else{return new F(function(){return _e(_7t[1],new T(function(){return B(_7r(_7t[2]));},1));});}},_7u=function(_7v,_7w){while(1){var _7x=(function(_7y,_7z){var _7A=E(_7z);if(!_7A[0]){return [0];}else{var _7B=_7A[1],_7C=_7A[2];if(!B(A(_7y,[_7B]))){var _7D=_7y;_7w=_7C;_7v=_7D;return null;}else{return [1,_7B,new T(function(){return B(_7u(_7y,_7C));})];}}})(_7v,_7w);if(_7x!=null){return _7x;}}},_7E=function(_7F,_7G){var _7H=E(_7G);return _7H[0]==0?[0]:[1,_7F,new T(function(){return B(_7E(_7H[1],_7H[2]));})];},_7I=function(_7J,_7K){while(1){var _7L=E(_7K);if(!_7L[0]){return E(_7J);}else{_7J=_7L[1];_7K=_7L[2];continue;}}},_7M=function(_7N){switch(E(_7N)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_7O=function(_7P){return E(_7P)[0]==1?true:false;},_7Q=function(_7R){return E(_7R)[0]==2?true:false;},_7S=[0,10],_7T=[1,_7S,_9],_7U=function(_7V){return new F(function(){return _e(_7T,_7V);});},_7W=[0,32],_7X=function(_7Y,_7Z){var _80=E(_7Z);return _80[0]==0?[0]:[1,new T(function(){return B(A(_7Y,[_80[1]]));}),new T(function(){return B(_7X(_7Y,_80[2]));})];},_81=function(_82){var _83=E(_82);switch(_83[0]){case 0:return E(_83[1]);case 1:return E(_83[1]);case 2:return E(_83[1]);default:return E(_83[1]);}},_84=function(_85){return E(E(_85)[1]);},_86=function(_87,_88,_89){while(1){var _8a=E(_89);if(!_8a[0]){return false;}else{if(!B(A(_84,[_87,_88,_8a[1]]))){_89=_8a[2];continue;}else{return true;}}}},_8b=function(_8c,_8d){var _8e=function(_8f,_8g){while(1){var _8h=(function(_8i,_8j){var _8k=E(_8i);if(!_8k[0]){return [0];}else{var _8l=_8k[1],_8m=_8k[2];if(!B(_86(_8c,_8l,_8j))){return [1,_8l,new T(function(){return B(_8e(_8m,[1,_8l,_8j]));})];}else{_8f=_8m;var _8n=_8j;_8g=_8n;return null;}}})(_8f,_8g);if(_8h!=null){return _8h;}}};return new F(function(){return _8e(_8d,_9);});},_8o=function(_8p,_8q,_8r,_8s,_8t,_8u){var _8v=E(_8u);if(!_8v[0]){return E(_8q);}else{var _8w=new T(function(){var _8x=B(_3g(_7M,_8v));return [0,_8x[1],_8x[2]];}),_8y=new T(function(){var _8z=B(_3g(_7O,E(_8w)[2]));return [0,_8z[1],_8z[2]];}),_8A=new T(function(){return E(E(_8y)[1]);}),_8B=function(_8C,_8D){var _8E=E(_8D);if(!_8E[0]){return E(_8C);}else{var _8F=new T(function(){return B(_e(_8p,[1,_7W,new T(function(){return B(_7I(_8C,_8E));})]));}),_8G=B(_8b(_7i,B(_7u(_7o,B(_7E(_8C,_8E))))));if(!_8G[0]){return new F(function(){return _e(_9,[1,_7W,_8F]);});}else{var _8H=_8G[1],_8I=E(_8G[2]);if(!_8I[0]){return new F(function(){return _e(_8H,[1,_7W,_8F]);});}else{return new F(function(){return _e(B(_e(_8H,new T(function(){return B(_e(_7q,new T(function(){return B(_7j(_7q,_8I[1],_8I[2]));},1)));},1))),[1,_7W,_8F]);});}}}},_8J=function(_8K,_8L){var _8M=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_8L))))));if(!_8M[0]){return [0];}else{var _8N=_8M[1],_8O=_8M[2],_8P=E(_8K);return _8P[0]==0?B(_8B(_8N,_8O)):B(_e(_8P,[1,_7W,new T(function(){return B(_8B(_8N,_8O));})]));}},_8Q=new T(function(){var _8R=B(_3g(_7Q,E(_8y)[2]));return [0,_8R[1],_8R[2]];});return new F(function(){return _7r(B(_7X(_7U,B(_8b(_7i,B(_7u(_7o,[1,new T(function(){if(!E(_8A)[0]){var _8S=E(E(_8w)[1]);if(!_8S[0]){var _8T=[0];}else{var _8U=E(_8S[1]);switch(_8U[0]){case 0:var _8V=E(_8U[1]),_8W=_8V[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8V]));break;case 1:var _8X=E(_8U[1]),_8W=_8X[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8X]));break;case 2:var _8Y=E(_8U[1]),_8W=_8Y[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Y]));break;default:var _8Z=E(_8U[1]),_8W=_8Z[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Z]));}var _8T=_8W;}var _90=_8T,_91=_90;}else{var _91=[0];}return _91;}),[1,new T(function(){return B(_8J(_8s,_8A));}),[1,new T(function(){return B(_8J(_8r,E(_8Q)[1]));}),[1,new T(function(){return B((function(_92){var _93=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_92))))));return _93[0]==0?[0]:B(_8B(_93[1],_93[2]));})(E(_8Q)[2]));}),_9]]]])))))));});}},_94=[1,_9,_9],_95=function(_96,_97){var _98=function(_99,_9a){var _9b=E(_99);if(!_9b[0]){return E(_9a);}else{var _9c=_9b[1],_9d=E(_9a);if(!_9d[0]){return E(_9b);}else{var _9e=_9d[1];return B(A(_96,[_9c,_9e]))==2?[1,_9e,new T(function(){return B(_98(_9b,_9d[2]));})]:[1,_9c,new T(function(){return B(_98(_9b[2],_9d));})];}}},_9f=function(_9g){var _9h=E(_9g);if(!_9h[0]){return [0];}else{var _9i=E(_9h[2]);return _9i[0]==0?E(_9h):[1,new T(function(){return B(_98(_9h[1],_9i[1]));}),new T(function(){return B(_9f(_9i[2]));})];}},_9j=function(_9k){while(1){var _9l=E(_9k);if(!_9l[0]){return E(new T(function(){return B(_9j(B(_9f(_9))));}));}else{if(!E(_9l[2])[0]){return E(_9l[1]);}else{_9k=B(_9f(_9l));continue;}}}},_9m=new T(function(){return B(_9n(_9));}),_9n=function(_9o){var _9p=E(_9o);if(!_9p[0]){return E(_94);}else{var _9q=_9p[1],_9r=E(_9p[2]);if(!_9r[0]){return [1,_9p,_9];}else{var _9s=_9r[1],_9t=_9r[2];if(B(A(_96,[_9q,_9s]))==2){return new F(function(){return (function(_9u,_9v,_9w){while(1){var _9x=(function(_9y,_9z,_9A){var _9B=E(_9A);if(!_9B[0]){return [1,[1,_9y,_9z],_9m];}else{var _9C=_9B[1];if(B(A(_96,[_9y,_9C]))==2){_9u=_9C;var _9D=[1,_9y,_9z];_9w=_9B[2];_9v=_9D;return null;}else{return [1,[1,_9y,_9z],new T(function(){return B(_9n(_9B));})];}}})(_9u,_9v,_9w);if(_9x!=null){return _9x;}}})(_9s,[1,_9q,_9],_9t);});}else{return new F(function(){return (function(_9E,_9F,_9G){while(1){var _9H=(function(_9I,_9J,_9K){var _9L=E(_9K);if(!_9L[0]){return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),_9m];}else{var _9M=_9L[1],_9N=_9L[2];switch(B(A(_96,[_9I,_9M]))){case 0:_9E=_9M;_9F=function(_9O){return new F(function(){return A(_9J,[[1,_9I,_9O]]);});};_9G=_9N;return null;case 1:_9E=_9M;_9F=function(_9P){return new F(function(){return A(_9J,[[1,_9I,_9P]]);});};_9G=_9N;return null;default:return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),new T(function(){return B(_9n(_9L));})];}}})(_9E,_9F,_9G);if(_9H!=null){return _9H;}}})(_9s,function(_9Q){return [1,_9q,_9Q];},_9t);});}}}};return new F(function(){return _9j(B(_9n(_97)));});},_9R=function(_9S,_9T,_9U,_9V){return new F(function(){return _e(B(_74(_9S,_9T,_9U)),[1,_70,new T(function(){return B(_8o(_6Z,_6Y,_6X,_6W,_6V,B(_95(_6S,_9V))));})]);});},_9W=function(_9X){var _9Y=E(_9X),_9Z=E(_9Y[1]);return new F(function(){return _9R(_9Z[1],_9Z[2],_9Z[3],_9Y[2]);});},_a0=new T(function(){return B(unCStr(" . "));}),_a1=function(_a2){var _a3=E(_a2);switch(_a3[0]){case 0:return E(_a3[3]);case 1:return E(_a3[3]);case 2:return E(_a3[3]);case 3:return E(_a3[3]);case 4:return E(_a3[3]);case 5:return E(_a3[3]);case 6:return E(_a3[3]);case 7:return E(_a3[3]);case 8:return E(_a3[3]);default:return E(_a3[3]);}},_a4=[0,41],_a5=[1,_a4,_9],_a6=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_a7=[0,44],_a8=[0,40],_a9=function(_aa,_ab,_ac){var _ad=E(_ac);switch(_ad[0]){case 0:return E(_a6);case 1:return new F(function(){return A(_aa,[_ad[2],_9]);});break;case 2:return new F(function(){return _a1(_ad[2]);});break;case 3:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),[1,new T(function(){return B(_a9(_aa,_ab,_ad[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[4])),_a5));})]));})]);});}},_ae=[0],_af=function(_ag,_ah,_ai,_aj,_ak,_al,_am,_an){var _ao=E(_an);switch(_ao[0]){case 0:return [0];case 1:return new F(function(){return A(_aj,[_ao[2],_9]);});break;case 2:return new F(function(){return _a1(_ao[2]);});break;case 3:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),[1,new T(function(){return B(_a9(_aj,_ak,_ao[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[4])),_a5));})]));})]);});break;case 7:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_a1(_ao[2])),new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));},1));});break;case 9:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4]));}),_9]]]);});break;case 10:return [1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3])),new T(function(){return B(_e(B(_a1(_ao[2])),new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4])),_a5));},1)));},1)));})];case 11:var _ap=_ao[2],_aq=_ao[3];return new F(function(){return A(_ai,[_ap,[1,new T(function(){return B(A(_al,[new T(function(){return B(A(_aq,[_ae]));}),_ap]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_aq,[_ae]))));}),_9]]]);});break;default:var _ar=_ao[2],_as=_ao[3];return new F(function(){return _e(B(_a1(_ar)),new T(function(){return B(_e(B(A(_am,[new T(function(){return B(A(_as,[_ae]));}),_ar])),[1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_as,[_ae])))),_a5));})]));},1));});}},_at=function(_au){var _av=E(_au);if(!_av[0]){return [0];}else{return new F(function(){return _e(_av[1],new T(function(){return B(_at(_av[2]));},1));});}},_aw=function(_ax,_ay){var _az=E(_ay);return _az[0]==0?[0]:[1,_ax,[1,_az[1],new T(function(){return B(_aw(_ax,_az[2]));})]];},_aA=function(_aB,_aC,_aD,_aE,_aF,_aG,_aH,_aI){var _aJ=E(_aI);if(!_aJ[0]){return new F(function(){return _a1(_aJ[1]);});}else{var _aK=B(_7X(function(_aL){return new F(function(){return _af(_aB,_aC,_aD,_aF,_aE,_aG,_aH,_aL);});},_aJ[1]));return _aK[0]==0?[0]:B(_at([1,_aK[1],new T(function(){return B(_aw(_a0,_aK[2]));})]));}},_aM=function(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aU,_aV){return new F(function(){return _2T(function(_aW,_aX){return new F(function(){return _e(B(_aA(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aW)),_aX);});},_aU,_aV);});},_aY=function(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,_b8){return new F(function(){return _e(B(_aA(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b7)),_b8);});},_b9=function(_ba,_bb,_bc,_bd,_be,_bf,_bg){return [0,function(_bh,_bi,_bj){return new F(function(){return _aY(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bh,_bi,_bj);});},function(_bj){return new F(function(){return _aA(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bj);});},function(_bi,_bj){return new F(function(){return _aM(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bi,_bj);});}];},_bk=new T(function(){return B(unCStr(" . "));}),_bl=new T(function(){return B(unCStr(" \u2234 "));}),_bm=function(_bn){return E(E(_bn)[2]);},_bo=function(_bp,_bq,_br){var _bs=B(_7X(new T(function(){return B(_bm(_bp));}),_bq));if(!_bs[0]){return new F(function(){return _e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1));});}else{return new F(function(){return _e(B(_at([1,_bs[1],new T(function(){return B(_aw(_bk,_bs[2]));})])),new T(function(){return B(_e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1)));},1));});}},_bt=2,_bu=function(_bv,_){return [0,[0,_5t,[1,_bv]],_bv];},_bw=function(_bx){return function(_by,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bz=E(_bx);return B(_e(B(_F(0,E(_bz[2])[1],_9)),_bz[1]));})]]],_by];};},_bA=function(_bB,_){return new F(function(){return _65(_bu,_bw,_bB,_);});},_bC=function(_bD){return function(_bE,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bF=E(_bD);return B(_e(B(_F(0,E(_bF[2])[1],_9)),_bF[1]));})]]],_bE];};},_bG=function(_bB,_){return new F(function(){return _65(_bu,_bC,_bB,_);});},_bH=function(_bI){return function(_bJ,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bK=E(_bI);return B(_e(B(_F(0,E(_bK[2])[1],_9)),_bK[1]));})]]],_bJ];};},_bL=function(_bB,_){return new F(function(){return _65(_bu,_bH,_bB,_);});},_bM=new T(function(){return B(unCStr("rslt"));}),_bN=new T(function(){return B(unCStr("root"));}),_bO=new T(function(){return B(unCStr("analysis"));}),_bP=new T(function(){return B(unCStr("class"));}),_bQ=new T(function(){return B(unCStr("invalid"));}),_bR=function(_bB,_){return new F(function(){return _5T(_56,_bQ,_bB,_);});},_bS=[1,_5c],_bT=[0,_bR,_bS],_bU=function(_bV,_){return [0,_bT,_bV];},_bW=new T(function(){return B(unCStr("div"));}),_bX=function(_bY,_bZ,_c0,_){var _c1=jsCreateElem(toJSStr(E(_bW))),_c2=_c1,_c3=jsAppendChild(_c2,E(_c0)[1]),_c4=[0,_c2],_c5=B(A(_bY,[_bZ,_c4,_])),_c6=_c5;return _c4;},_c7=function(_c8,_c9,_){var _ca=E(_c8);if(!_ca[0]){return _c9;}else{var _cb=B(_bX(_56,_ca[1],_c9,_)),_cc=_cb,_cd=B(_c7(_ca[2],_c9,_)),_ce=_cd;return _c9;}},_cf=new T(function(){return B(unCStr("lined"));}),_cg=new T(function(){return B(unCStr("span"));}),_ch=function(_ci,_cj,_ck,_cl,_){var _cm=B(A(_ck,[_cl,_])),_cn=_cm,_co=E(_cn),_cp=E(_co[1]),_cq=_cp[1];return [0,[0,function(_cr,_){var _cs=jsFind(toJSStr(E(_ci))),_ct=_cs,_cu=E(_ct);if(!_cu[0]){return _cr;}else{var _cv=_cu[1];switch(E(_cj)){case 0:var _cw=B(A(_cq,[_cv,_])),_cx=_cw;return _cr;case 1:var _cy=E(_cv),_cz=_cy[1],_cA=jsGetChildren(_cz),_cB=_cA,_cC=E(_cB);if(!_cC[0]){var _cD=B(A(_cq,[_cy,_])),_cE=_cD;return _cr;}else{var _cF=jsCreateElem(toJSStr(E(_cg))),_cG=_cF,_cH=jsAddChildBefore(_cG,_cz,E(_cC[1])[1]),_cI=B(A(_cq,[[0,_cG],_])),_cJ=_cI;return _cr;}break;default:var _cK=E(_cv),_cL=jsClearChildren(_cK[1]),_cM=B(A(_cq,[_cK,_])),_cN=_cM;return _cr;}}},_cp[2]],_co[2]];},_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR[0]){return E(_cQ)[0]==0?1:0;}else{var _cS=E(_cQ);if(!_cS[0]){return 2;}else{var _cT=E(_cR[1])[1],_cU=E(_cS[1])[1];if(_cT!=_cU){return _cT>_cU?2:0;}else{_cP=_cR[2];_cQ=_cS[2];continue;}}}}},_cV=new T(function(){return B(_e(_9,_9));}),_cW=function(_cX,_cY,_cZ,_d0,_d1,_d2,_d3,_d4){var _d5=[0,_cX,_cY,_cZ],_d6=function(_d7){var _d8=E(_d0);if(!_d8[0]){var _d9=E(_d4);if(!_d9[0]){switch(B(_cO(_cX,_d1))){case 0:return [0,[0,_d1,_d2,_d3],_9];case 1:return _cY>=_d2?_cY!=_d2?[0,_d5,_9]:_cZ>=_d3?_cZ!=_d3?[0,_d5,_9]:[0,_d5,_cV]:[0,[0,_d1,_d2,_d3],_9]:[0,[0,_d1,_d2,_d3],_9];default:return [0,_d5,_9];}}else{return [0,[0,_d1,_d2,_d3],_d9];}}else{switch(B(_cO(_cX,_d1))){case 0:return [0,[0,_d1,_d2,_d3],_d4];case 1:return _cY>=_d2?_cY!=_d2?[0,_d5,_d8]:_cZ>=_d3?_cZ!=_d3?[0,_d5,_d8]:[0,_d5,new T(function(){return B(_e(_d8,_d4));})]:[0,[0,_d1,_d2,_d3],_d4]:[0,[0,_d1,_d2,_d3],_d4];default:return [0,_d5,_d8];}}};if(!E(_d4)[0]){var _da=E(_d0);return _da[0]==0?B(_d6(_)):[0,_d5,_da];}else{return new F(function(){return _d6(_);});}},_db=function(_dc,_dd){while(1){var _de=E(_dc);if(!_de[0]){return E(_dd);}else{_dc=_de[2];var _df=[1,_de[1],_dd];_dd=_df;continue;}}},_dg=new T(function(){return B(_db(_9,_9));}),_dh=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_di=new T(function(){return B(err(_dh));}),_dj=function(_dk,_dl,_dm,_dn,_do){var _dp=function(_dq,_dr,_ds){var _dt=[1,_dr,_dq];return new F(function(){return A(_dk,[_ds,new T(function(){var _du=E(_dq);return function(_dv,_dw,_dx){return new F(function(){return _dp(_dt,_dv,_dw);});};}),_dn,_di,function(_dy){return new F(function(){return A(_dm,[new T(function(){return B(_db(_dt,_9));}),_ds,new T(function(){var _dz=E(E(_ds)[2]),_dA=E(_dy),_dB=E(_dA[1]),_dC=B(_cW(_dB[1],_dB[2],_dB[3],_dA[2],_dz[1],_dz[2],_dz[3],_9));return [0,E(_dC[1]),_dC[2]];})]);});}]);});};return new F(function(){return A(_dk,[_dl,function(_dD,_dE,_dF){return new F(function(){return _dp(_9,_dD,_dE);});},_dn,_di,function(_dG){return new F(function(){return A(_do,[_dg,_dl,new T(function(){var _dH=E(E(_dl)[2]),_dI=E(_dG),_dJ=E(_dI[1]),_dK=B(_cW(_dJ[1],_dJ[2],_dJ[3],_dI[2],_dH[1],_dH[2],_dH[3],_9));return [0,E(_dK[1]),_dK[2]];})]);});}]);});},_dL=function(_dM,_dN){var _dO=E(_dM),_dP=E(_dO[1]),_dQ=E(_dN),_dR=E(_dQ[1]),_dS=B(_cW(_dP[1],_dP[2],_dP[3],_dO[2],_dR[1],_dR[2],_dR[3],_dQ[2]));return [0,E(_dS[1]),_dS[2]];},_dT=function(_dU,_dV,_dW,_dX,_dY,_dZ){var _e0=function(_e1,_e2,_e3,_e4,_e5){return new F(function(){return _dj(_dU,_e2,function(_e6,_e7,_e8){return new F(function(){return A(_e3,[[1,_e1,_e6],_e7,new T(function(){var _e9=E(E(_e7)[2]),_ea=E(_e8),_eb=E(_ea[1]),_ec=B(_cW(_eb[1],_eb[2],_eb[3],_ea[2],_e9[1],_e9[2],_e9[3],_9));return [0,E(_ec[1]),_ec[2]];})]);});},_e4,function(_ed,_ee,_ef){return new F(function(){return A(_e5,[[1,_e1,_ed],_ee,new T(function(){var _eg=E(E(_ee)[2]),_eh=E(_ef),_ei=E(_eh[1]),_ej=B(_cW(_ei[1],_ei[2],_ei[3],_eh[2],_eg[1],_eg[2],_eg[3],_9));return [0,E(_ej[1]),_ej[2]];})]);});});});};return new F(function(){return A(_dU,[_dV,function(_ek,_el,_em){return new F(function(){return _e0(_ek,_el,_dW,_dX,function(_en,_eo,_ep){return new F(function(){return A(_dW,[_en,_eo,new T(function(){return B(_dL(_em,_ep));})]);});});});},_dX,function(_eq,_er,_es){return new F(function(){return _e0(_eq,_er,_dW,_dX,function(_et,_eu,_ev){return new F(function(){return A(_dY,[_et,_eu,new T(function(){return B(_dL(_es,_ev));})]);});});});},_dZ]);});},_ew=function(_ex,_ey,_ez,_eA,_eB){var _eC=function(_eD,_eE){return new F(function(){return A(_ex,[_eE,new T(function(){var _eF=E(_eD);return function(_eG,_eH,_eI){return new F(function(){return _eC(_9,_eH);});};}),_eA,_di,function(_eJ){return new F(function(){return A(_ez,[_5c,_eE,new T(function(){var _eK=E(E(_eE)[2]),_eL=E(_eJ),_eM=E(_eL[1]),_eN=B(_cW(_eM[1],_eM[2],_eM[3],_eL[2],_eK[1],_eK[2],_eK[3],_9));return [0,E(_eN[1]),_eN[2]];})]);});}]);});};return new F(function(){return A(_ex,[_ey,function(_eO,_eP,_eQ){return new F(function(){return _eC(_9,_eP);});},_eA,_di,function(_eR){return new F(function(){return A(_eB,[_5c,_ey,new T(function(){var _eS=E(E(_ey)[2]),_eT=E(_eR),_eU=E(_eT[1]),_eV=B(_cW(_eU[1],_eU[2],_eU[3],_eT[2],_eS[1],_eS[2],_eS[3],_9));return [0,E(_eV[1]),_eV[2]];})]);});}]);});},_eW=function(_eX,_eY,_eZ,_f0,_f1,_f2,_f3){var _f4=function(_f5,_f6,_f7,_f8,_f9){var _fa=[1,_f5,_9],_fb=function(_fc,_fd,_fe,_ff){return new F(function(){return _eW(_eX,_eY,_fc,function(_fg,_fh,_fi){return new F(function(){return A(_fd,[[1,_f5,_fg],_fh,new T(function(){var _fj=E(E(_fh)[2]),_fk=E(_fi),_fl=E(_fk[1]),_fm=B(_cW(_fl[1],_fl[2],_fl[3],_fk[2],_fj[1],_fj[2],_fj[3],_9));return [0,E(_fm[1]),_fm[2]];})]);});},_fe,function(_fn,_fo,_fp){return new F(function(){return A(_ff,[[1,_f5,_fn],_fo,new T(function(){var _fq=E(E(_fo)[2]),_fr=E(_fp),_fs=E(_fr[1]),_ft=B(_cW(_fs[1],_fs[2],_fs[3],_fr[2],_fq[1],_fq[2],_fq[3],_9));return [0,E(_ft[1]),_ft[2]];})]);});},function(_fu){return new F(function(){return A(_ff,[_fa,_fc,new T(function(){var _fv=E(E(_fc)[2]),_fw=_fv[1],_fx=_fv[2],_fy=_fv[3],_fz=E(_fu),_fA=E(_fz[1]),_fB=B(_cW(_fA[1],_fA[2],_fA[3],_fz[2],_fw,_fx,_fy,_9)),_fC=E(_fB[1]),_fD=B(_cW(_fC[1],_fC[2],_fC[3],_fB[2],_fw,_fx,_fy,_9));return [0,E(_fD[1]),_fD[2]];})]);});});});};return new F(function(){return A(_eY,[_f6,function(_fE,_fF,_fG){return new F(function(){return _fb(_fF,_f7,_f8,function(_fH,_fI,_fJ){return new F(function(){return A(_f7,[_fH,_fI,new T(function(){return B(_dL(_fG,_fJ));})]);});});});},_f8,function(_fK,_fL,_fM){return new F(function(){return _fb(_fL,_f7,_f8,function(_fN,_fO,_fP){return new F(function(){return A(_f9,[_fN,_fO,new T(function(){return B(_dL(_fM,_fP));})]);});});});},function(_fQ){return new F(function(){return A(_f9,[_fa,_f6,new T(function(){var _fR=E(E(_f6)[2]),_fS=E(_fQ),_fT=E(_fS[1]),_fU=B(_cW(_fT[1],_fT[2],_fT[3],_fS[2],_fR[1],_fR[2],_fR[3],_9));return [0,E(_fU[1]),_fU[2]];})]);});}]);});};return new F(function(){return A(_eX,[_eZ,function(_fV,_fW,_fX){return new F(function(){return _f4(_fV,_fW,_f0,_f1,function(_fY,_fZ,_g0){return new F(function(){return A(_f0,[_fY,_fZ,new T(function(){return B(_dL(_fX,_g0));})]);});});});},_f1,function(_g1,_g2,_g3){return new F(function(){return _f4(_g1,_g2,_f0,_f1,function(_g4,_g5,_g6){return new F(function(){return A(_f2,[_g4,_g5,new T(function(){return B(_dL(_g3,_g6));})]);});});});},_f3]);});},_g7=function(_g8,_g9){return new F(function(){return A(_g9,[_g8]);});},_ga=[0,34],_gb=[1,_ga,_9],_gc=[0,E(_9)],_gd=[1,_gc,_9],_ge=function(_gf,_gg){var _gh=_gf%_gg;if(_gf<=0){if(_gf>=0){return E(_gh);}else{if(_gg<=0){return E(_gh);}else{var _gi=E(_gh);return _gi==0?0:_gi+_gg|0;}}}else{if(_gg>=0){if(_gf>=0){return E(_gh);}else{if(_gg<=0){return E(_gh);}else{var _gj=E(_gh);return _gj==0?0:_gj+_gg|0;}}}else{var _gk=E(_gh);return _gk==0?0:_gk+_gg|0;}}},_gl=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_gm=new T(function(){return B(err(_gl));}),_gn=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_go=new T(function(){return B(err(_gn));}),_gp=function(_gq,_gr){while(1){var _gs=E(_gq);if(!_gs[0]){return E(_go);}else{var _gt=E(_gr);if(!_gt){return E(_gs[1]);}else{_gq=_gs[2];_gr=_gt-1|0;continue;}}}},_gu=new T(function(){return B(unCStr("ACK"));}),_gv=new T(function(){return B(unCStr("BEL"));}),_gw=new T(function(){return B(unCStr("BS"));}),_gx=new T(function(){return B(unCStr("SP"));}),_gy=[1,_gx,_9],_gz=new T(function(){return B(unCStr("US"));}),_gA=[1,_gz,_gy],_gB=new T(function(){return B(unCStr("RS"));}),_gC=[1,_gB,_gA],_gD=new T(function(){return B(unCStr("GS"));}),_gE=[1,_gD,_gC],_gF=new T(function(){return B(unCStr("FS"));}),_gG=[1,_gF,_gE],_gH=new T(function(){return B(unCStr("ESC"));}),_gI=[1,_gH,_gG],_gJ=new T(function(){return B(unCStr("SUB"));}),_gK=[1,_gJ,_gI],_gL=new T(function(){return B(unCStr("EM"));}),_gM=[1,_gL,_gK],_gN=new T(function(){return B(unCStr("CAN"));}),_gO=[1,_gN,_gM],_gP=new T(function(){return B(unCStr("ETB"));}),_gQ=[1,_gP,_gO],_gR=new T(function(){return B(unCStr("SYN"));}),_gS=[1,_gR,_gQ],_gT=new T(function(){return B(unCStr("NAK"));}),_gU=[1,_gT,_gS],_gV=new T(function(){return B(unCStr("DC4"));}),_gW=[1,_gV,_gU],_gX=new T(function(){return B(unCStr("DC3"));}),_gY=[1,_gX,_gW],_gZ=new T(function(){return B(unCStr("DC2"));}),_h0=[1,_gZ,_gY],_h1=new T(function(){return B(unCStr("DC1"));}),_h2=[1,_h1,_h0],_h3=new T(function(){return B(unCStr("DLE"));}),_h4=[1,_h3,_h2],_h5=new T(function(){return B(unCStr("SI"));}),_h6=[1,_h5,_h4],_h7=new T(function(){return B(unCStr("SO"));}),_h8=[1,_h7,_h6],_h9=new T(function(){return B(unCStr("CR"));}),_ha=[1,_h9,_h8],_hb=new T(function(){return B(unCStr("FF"));}),_hc=[1,_hb,_ha],_hd=new T(function(){return B(unCStr("VT"));}),_he=[1,_hd,_hc],_hf=new T(function(){return B(unCStr("LF"));}),_hg=[1,_hf,_he],_hh=new T(function(){return B(unCStr("HT"));}),_hi=[1,_hh,_hg],_hj=[1,_gw,_hi],_hk=[1,_gv,_hj],_hl=[1,_gu,_hk],_hm=new T(function(){return B(unCStr("ENQ"));}),_hn=[1,_hm,_hl],_ho=new T(function(){return B(unCStr("EOT"));}),_hp=[1,_ho,_hn],_hq=new T(function(){return B(unCStr("ETX"));}),_hr=[1,_hq,_hp],_hs=new T(function(){return B(unCStr("STX"));}),_ht=[1,_hs,_hr],_hu=new T(function(){return B(unCStr("SOH"));}),_hv=[1,_hu,_ht],_hw=new T(function(){return B(unCStr("NUL"));}),_hx=[1,_hw,_hv],_hy=[0,92],_hz=new T(function(){return B(unCStr("\\DEL"));}),_hA=new T(function(){return B(unCStr("\\a"));}),_hB=new T(function(){return B(unCStr("\\\\"));}),_hC=new T(function(){return B(unCStr("\\SO"));}),_hD=new T(function(){return B(unCStr("\\r"));}),_hE=new T(function(){return B(unCStr("\\f"));}),_hF=new T(function(){return B(unCStr("\\v"));}),_hG=new T(function(){return B(unCStr("\\n"));}),_hH=new T(function(){return B(unCStr("\\t"));}),_hI=new T(function(){return B(unCStr("\\b"));}),_hJ=function(_hK,_hL){if(_hK<=127){var _hM=E(_hK);switch(_hM){case 92:return new F(function(){return _e(_hB,_hL);});break;case 127:return new F(function(){return _e(_hz,_hL);});break;default:if(_hM<32){var _hN=E(_hM);switch(_hN){case 7:return new F(function(){return _e(_hA,_hL);});break;case 8:return new F(function(){return _e(_hI,_hL);});break;case 9:return new F(function(){return _e(_hH,_hL);});break;case 10:return new F(function(){return _e(_hG,_hL);});break;case 11:return new F(function(){return _e(_hF,_hL);});break;case 12:return new F(function(){return _e(_hE,_hL);});break;case 13:return new F(function(){return _e(_hD,_hL);});break;case 14:return new F(function(){return _e(_hC,new T(function(){var _hO=E(_hL);if(!_hO[0]){var _hP=[0];}else{var _hP=E(E(_hO[1])[1])==72?B(unAppCStr("\\&",_hO)):E(_hO);}return _hP;},1));});break;default:return new F(function(){return _e([1,_hy,new T(function(){var _hQ=_hN;return _hQ>=0?B(_gp(_hx,_hQ)):E(_gm);})],_hL);});}}else{return [1,[0,_hM],_hL];}}}else{return [1,_hy,new T(function(){var _hR=jsShowI(_hK),_hS=_hR;return B(_e(fromJSStr(_hS),new T(function(){var _hT=E(_hL);if(!_hT[0]){var _hU=[0];}else{var _hV=E(_hT[1])[1];if(_hV<48){var _hW=E(_hT);}else{var _hW=_hV>57?E(_hT):B(unAppCStr("\\&",_hT));}var _hX=_hW,_hY=_hX,_hU=_hY;}return _hU;},1)));})];}},_hZ=new T(function(){return B(unCStr("\\\""));}),_i0=function(_i1,_i2){var _i3=E(_i1);if(!_i3[0]){return E(_i2);}else{var _i4=_i3[2],_i5=E(E(_i3[1])[1]);if(_i5==34){return new F(function(){return _e(_hZ,new T(function(){return B(_i0(_i4,_i2));},1));});}else{return new F(function(){return _hJ(_i5,new T(function(){return B(_i0(_i4,_i2));}));});}}},_i6=function(_i7,_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig){var _ih=[0,_ib,_ic,_id];return new F(function(){return A(_i7,[new T(function(){return B(A(_i8,[_ia]));}),function(_ii){var _ij=E(_ii);if(!_ij[0]){return E(new T(function(){return B(A(_ig,[[0,E(_ih),_gd]]));}));}else{var _ik=E(_ij[1]),_il=_ik[1],_im=_ik[2];if(!B(A(_i9,[_il]))){return new F(function(){return A(_ig,[[0,E(_ih),[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_il,_9],_gb));})])],_9]]]);});}else{var _in=E(_il);switch(E(_in[1])){case 9:var _io=[0,_ib,_ic,(_id+8|0)-B(_ge(_id-1|0,8))|0];break;case 10:var _io=E([0,_ib,_ic+1|0,1]);break;default:var _io=E([0,_ib,_ic,_id+1|0]);}var _ip=_io,_iq=[0,E(_ip),_9],_ir=[0,_im,E(_ip),E(_ie)];return new F(function(){return A(_if,[_in,_ir,_iq]);});}}}]);});},_is=function(_it,_iu){return E(_it)[1]!=E(_iu)[1];},_iv=function(_iw,_ix){return E(_iw)[1]==E(_ix)[1];},_iy=[0,_iv,_is],_iz=new T(function(){return B(unCStr(" 	"));}),_iA=function(_iB){return new F(function(){return _86(_iy,_iB,_iz);});},_iC=function(_iD,_iE){return E(_iE);},_iF=function(_iG){return new F(function(){return err(_iG);});},_iH=function(_iI){return E(_iI);},_iJ=[0,_g7,_iC,_iH,_iF],_iK=function(_iL){return E(E(_iL)[3]);},_iM=function(_iN,_iO){var _iP=E(_iO);return _iP[0]==0?B(A(_iK,[_iN,_28])):B(A(_iK,[_iN,[1,[0,_iP[1],_iP[2]]]]));},_iQ=function(_iR){return new F(function(){return _iM(_iJ,_iR);});},_iS=function(_iT,_iU,_iV,_iW,_iX){var _iY=E(_iT),_iZ=E(_iY[2]);return new F(function(){return _i6(_g7,_iQ,_iA,_iY[1],_iZ[1],_iZ[2],_iZ[3],_iY[3],_iU,_iX);});},_j0=function(_j1){return [0,_j1,function(_j2){return new F(function(){return _iM(_j1,_j2);});}];},_j3=new T(function(){return B(_j0(_iJ));}),_j4=function(_j5){return [2,E(E(_j5))];},_j6=function(_j7,_j8){switch(E(_j7)[0]){case 0:switch(E(_j8)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_j8)[0]==1?false:true;case 2:return E(_j8)[0]==2?false:true;default:return E(_j8)[0]==3?false:true;}},_j9=[2,E(_9)],_ja=function(_j2){return new F(function(){return _j6(_j9,_j2);});},_jb=function(_jc,_jd,_je){var _jf=E(_je);if(!_jf[0]){return [0,_jc,[1,_j9,new T(function(){return B(_7u(_ja,_jd));})]];}else{var _jg=_jf[1],_jh=E(_jf[2]);if(!_jh[0]){var _ji=new T(function(){return [2,E(E(_jg))];});return [0,_jc,[1,_ji,new T(function(){return B(_7u(function(_j2){return new F(function(){return _j6(_ji,_j2);});},_jd));})]];}else{var _jj=new T(function(){return [2,E(E(_jg))];}),_jk=function(_jl){var _jm=E(_jl);if(!_jm[0]){return [0,_jc,[1,_jj,new T(function(){return B(_7u(function(_j2){return new F(function(){return _j6(_jj,_j2);});},_jd));})]];}else{var _jn=B(_jk(_jm[2]));return [0,_jn[1],[1,new T(function(){return B(_j4(_jm[1]));}),_jn[2]]];}};return new F(function(){return (function(_jo,_jp){var _jq=B(_jk(_jp));return [0,_jq[1],[1,new T(function(){return B(_j4(_jo));}),_jq[2]]];})(_jh[1],_jh[2]);});}}},_jr=function(_js,_jt){var _ju=E(_js),_jv=B(_jb(_ju[1],_ju[2],_jt));return [0,E(_jv[1]),_jv[2]];},_jw=function(_jx,_jy,_jz,_jA,_jB,_jC,_jD){return new F(function(){return A(_jx,[_jz,_jA,_jB,function(_jE,_jF,_jG){return new F(function(){return A(_jC,[_jE,_jF,new T(function(){var _jH=E(_jG),_jI=E(_jH[2]);if(!_jI[0]){var _jJ=E(_jH);}else{var _jK=B(_jb(_jH[1],_jI,_jy)),_jJ=[0,E(_jK[1]),_jK[2]];}var _jL=_jJ;return _jL;})]);});},function(_jM){return new F(function(){return A(_jD,[new T(function(){return B(_jr(_jM,_jy));})]);});}]);});},_jN=function(_jO,_jP){return function(_jQ,_jR,_jS,_jT,_jU){return new F(function(){return _jw(function(_jV,_jW,_jX,_jY,_jZ){var _k0=E(_jO),_k1=E(_jV),_k2=E(_k1[2]);return new F(function(){return _i6(E(_k0[1])[1],_k0[2],function(_k3){return new F(function(){return _iv(_k3,_jP);});},_k1[1],_k2[1],_k2[2],_k2[3],_k1[3],_jW,_jZ);});},[1,[1,_ga,new T(function(){return B(_i0([1,_jP,_9],_gb));})],_9],_jQ,_jR,_jS,_jT,_jU);});};},_k4=[0,10],_k5=new T(function(){return B(unCStr("lf new-line"));}),_k6=[1,_k5,_9],_k7=function(_k8){return function(_k9,_ka,_kb,_kc,_kd){return new F(function(){return _jw(new T(function(){return B(_jN(_k8,_k4));}),_k6,_k9,_ka,_kb,_kc,_kd);});};},_ke=new T(function(){return B(_k7(_j3));}),_kf=new T(function(){return B(unCStr("digit"));}),_kg=[1,_kf,_9],_kh=function(_ki){return new F(function(){return _iM(_iJ,_ki);});},_kj=function(_kk){var _kl=E(_kk)[1];return _kl<48?false:_kl<=57;},_km=function(_kn,_ko,_kp,_kq,_kr){var _ks=E(_kn),_kt=E(_ks[2]);return new F(function(){return _i6(_g7,_kh,_kj,_ks[1],_kt[1],_kt[2],_kt[3],_ks[3],_ko,_kr);});},_ku=function(_kv,_kw,_kx,_ky,_kz){return new F(function(){return _jw(_km,_kg,_kv,_kw,_kx,_ky,_kz);});},_kA=function(_kB,_kC,_kD,_kE,_kF){return new F(function(){return _dT(_ku,_kB,_kC,_kD,_kE,_kF);});},_kG=new T(function(){return B(_j0(_iJ));}),_kH=[0,44],_kI=new T(function(){return B(_jN(_kG,_kH));}),_kJ=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_kK=new T(function(){return B(err(_kJ));}),_kL=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kM=new T(function(){return B(err(_kL));}),_kN=new T(function(){return B(_3B("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_kO=function(_kP,_kQ){while(1){var _kR=(function(_kS,_kT){var _kU=E(_kS);switch(_kU[0]){case 0:var _kV=E(_kT);if(!_kV[0]){return [0];}else{_kP=B(A(_kU[1],[_kV[1]]));_kQ=_kV[2];return null;}break;case 1:var _kW=B(A(_kU[1],[_kT])),_kX=_kT;_kP=_kW;_kQ=_kX;return null;case 2:return [0];case 3:return [1,[0,_kU[1],_kT],new T(function(){return B(_kO(_kU[2],_kT));})];default:return E(_kU[1]);}})(_kP,_kQ);if(_kR!=null){return _kR;}}},_kY=function(_kZ,_l0){var _l1=function(_l2){var _l3=E(_l0);if(_l3[0]==3){return [3,_l3[1],new T(function(){return B(_kY(_kZ,_l3[2]));})];}else{var _l4=E(_kZ);if(_l4[0]==2){return E(_l3);}else{var _l5=E(_l3);if(_l5[0]==2){return E(_l4);}else{var _l6=function(_l7){var _l8=E(_l5);if(_l8[0]==4){return [1,function(_l9){return [4,new T(function(){return B(_e(B(_kO(_l4,_l9)),_l8[1]));})];}];}else{var _la=E(_l4);if(_la[0]==1){var _lb=_la[1],_lc=E(_l8);return _lc[0]==0?[1,function(_ld){return new F(function(){return _kY(B(A(_lb,[_ld])),_lc);});}]:[1,function(_le){return new F(function(){return _kY(B(A(_lb,[_le])),new T(function(){return B(A(_lc[1],[_le]));}));});}];}else{var _lf=E(_l8);return _lf[0]==0?E(_kN):[1,function(_lg){return new F(function(){return _kY(_la,new T(function(){return B(A(_lf[1],[_lg]));}));});}];}}},_lh=E(_l4);switch(_lh[0]){case 1:var _li=E(_l5);if(_li[0]==4){return [1,function(_lj){return [4,new T(function(){return B(_e(B(_kO(B(A(_lh[1],[_lj])),_lj)),_li[1]));})];}];}else{return new F(function(){return _l6(_);});}break;case 4:var _lk=_lh[1],_ll=E(_l5);switch(_ll[0]){case 0:return [1,function(_lm){return [4,new T(function(){return B(_e(_lk,new T(function(){return B(_kO(_ll,_lm));},1)));})];}];case 1:return [1,function(_ln){return [4,new T(function(){return B(_e(_lk,new T(function(){return B(_kO(B(A(_ll[1],[_ln])),_ln));},1)));})];}];default:return [4,new T(function(){return B(_e(_lk,_ll[1]));})];}break;default:return new F(function(){return _l6(_);});}}}}},_lo=E(_kZ);switch(_lo[0]){case 0:var _lp=E(_l0);if(!_lp[0]){return [0,function(_lq){return new F(function(){return _kY(B(A(_lo[1],[_lq])),new T(function(){return B(A(_lp[1],[_lq]));}));});}];}else{return new F(function(){return _l1(_);});}break;case 3:return [3,_lo[1],new T(function(){return B(_kY(_lo[2],_l0));})];default:return new F(function(){return _l1(_);});}},_lr=[0,41],_ls=[1,_lr,_9],_lt=[0,40],_lu=[1,_lt,_9],_lv=function(_lw,_lx){while(1){var _ly=E(_lw);if(!_ly[0]){return E(_lx)[0]==0?true:false;}else{var _lz=E(_lx);if(!_lz[0]){return false;}else{if(E(_ly[1])[1]!=E(_lz[1])[1]){return false;}else{_lw=_ly[2];_lx=_lz[2];continue;}}}}},_lA=function(_lB,_lC){var _lD=E(_lB);switch(_lD[0]){case 0:return [0,function(_lE){return new F(function(){return _lA(B(A(_lD[1],[_lE])),_lC);});}];case 1:return [1,function(_lF){return new F(function(){return _lA(B(A(_lD[1],[_lF])),_lC);});}];case 2:return [2];case 3:return new F(function(){return _kY(B(A(_lC,[_lD[1]])),new T(function(){return B(_lA(_lD[2],_lC));}));});break;default:var _lG=function(_lH){var _lI=E(_lH);if(!_lI[0]){return [0];}else{var _lJ=E(_lI[1]);return new F(function(){return _e(B(_kO(B(A(_lC,[_lJ[1]])),_lJ[2])),new T(function(){return B(_lG(_lI[2]));},1));});}},_lK=B(_lG(_lD[1]));return _lK[0]==0?[2]:[4,_lK];}},_lL=[2],_lM=function(_lN){return [3,_lN,_lL];},_lO=function(_lP,_lQ){var _lR=E(_lP);if(!_lR){return new F(function(){return A(_lQ,[_5c]);});}else{return [0,function(_lS){return E(new T(function(){return B(_lO(_lR-1|0,_lQ));}));}];}},_lT=function(_lU,_lV,_lW){return function(_lX){return new F(function(){return A(function(_lY,_lZ,_m0){while(1){var _m1=(function(_m2,_m3,_m4){var _m5=E(_m2);switch(_m5[0]){case 0:var _m6=E(_m3);if(!_m6[0]){return E(_lV);}else{_lY=B(A(_m5[1],[_m6[1]]));_lZ=_m6[2];var _m7=_m4+1|0;_m0=_m7;return null;}break;case 1:var _m8=B(A(_m5[1],[_m3])),_m9=_m3,_m7=_m4;_lY=_m8;_lZ=_m9;_m0=_m7;return null;case 2:return E(_lV);case 3:return function(_ma){return new F(function(){return _lO(_m4,function(_mb){return E(new T(function(){return B(_lA(_m5,_ma));}));});});};default:return function(_mc){return new F(function(){return _lA(_m5,_mc);});};}})(_lY,_lZ,_m0);if(_m1!=null){return _m1;}}},[new T(function(){return B(A(_lU,[_lM]));}),_lX,0,_lW]);});};},_md=function(_me){return new F(function(){return A(_me,[_9]);});},_mf=function(_mg,_mh){var _mi=function(_mj){var _mk=E(_mj);if(!_mk[0]){return E(_md);}else{var _ml=_mk[1];return !B(A(_mg,[_ml]))?E(_md):function(_mm){return [0,function(_mn){return E(new T(function(){return B(A(new T(function(){return B(_mi(_mk[2]));}),[function(_mo){return new F(function(){return A(_mm,[[1,_ml,_mo]]);});}]));}));}];};}};return function(_mp){return new F(function(){return A(_mi,[_mp,_mh]);});};},_mq=[6],_mr=new T(function(){return B(unCStr("valDig: Bad base"));}),_ms=new T(function(){return B(err(_mr));}),_mt=function(_mu,_mv){var _mw=function(_mx,_my){var _mz=E(_mx);if(!_mz[0]){return function(_mA){return new F(function(){return A(_mA,[new T(function(){return B(A(_my,[_9]));})]);});};}else{var _mB=E(_mz[1])[1],_mC=function(_mD){return function(_mE){return [0,function(_mF){return E(new T(function(){return B(A(new T(function(){return B(_mw(_mz[2],function(_mG){return new F(function(){return A(_my,[[1,_mD,_mG]]);});}));}),[_mE]));}));}];};};switch(E(E(_mu)[1])){case 8:if(48>_mB){return function(_mH){return new F(function(){return A(_mH,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>55){return function(_mI){return new F(function(){return A(_mI,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,_mB-48|0]);});}}break;case 10:if(48>_mB){return function(_mJ){return new F(function(){return A(_mJ,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>57){return function(_mK){return new F(function(){return A(_mK,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,_mB-48|0]);});}}break;case 16:if(48>_mB){if(97>_mB){if(65>_mB){return function(_mL){return new F(function(){return A(_mL,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mM){return new F(function(){return A(_mM,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{if(_mB>102){if(65>_mB){return function(_mN){return new F(function(){return A(_mN,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mO){return new F(function(){return A(_mO,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{return new F(function(){return _mC([0,(_mB-97|0)+10|0]);});}}}else{if(_mB>57){if(97>_mB){if(65>_mB){return function(_mP){return new F(function(){return A(_mP,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mQ){return new F(function(){return A(_mQ,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{if(_mB>102){if(65>_mB){return function(_mR){return new F(function(){return A(_mR,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mS){return new F(function(){return A(_mS,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{return new F(function(){return _mC([0,(_mB-97|0)+10|0]);});}}}else{return new F(function(){return _mC([0,_mB-48|0]);});}}break;default:return E(_ms);}}};return function(_mT){return new F(function(){return A(_mw,[_mT,_5q,function(_mU){var _mV=E(_mU);return _mV[0]==0?[2]:B(A(_mv,[_mV]));}]);});};},_mW=[0,10],_mX=[0,1],_mY=[0,2147483647],_mZ=function(_n0,_n1){while(1){var _n2=E(_n0);if(!_n2[0]){var _n3=_n2[1],_n4=E(_n1);if(!_n4[0]){var _n5=_n4[1],_n6=addC(_n3,_n5);if(!E(_n6[2])){return [0,_n6[1]];}else{_n0=[1,I_fromInt(_n3)];_n1=[1,I_fromInt(_n5)];continue;}}else{_n0=[1,I_fromInt(_n3)];_n1=_n4;continue;}}else{var _n7=E(_n1);if(!_n7[0]){_n0=_n2;_n1=[1,I_fromInt(_n7[1])];continue;}else{return [1,I_add(_n2[1],_n7[1])];}}}},_n8=new T(function(){return B(_mZ(_mY,_mX));}),_n9=function(_na){var _nb=E(_na);if(!_nb[0]){var _nc=E(_nb[1]);return _nc==(-2147483648)?E(_n8):[0, -_nc];}else{return [1,I_negate(_nb[1])];}},_nd=[0,10],_ne=[0,0],_nf=function(_ng){return [0,_ng];},_nh=function(_ni,_nj){while(1){var _nk=E(_ni);if(!_nk[0]){var _nl=_nk[1],_nm=E(_nj);if(!_nm[0]){var _nn=_nm[1];if(!(imul(_nl,_nn)|0)){return [0,imul(_nl,_nn)|0];}else{_ni=[1,I_fromInt(_nl)];_nj=[1,I_fromInt(_nn)];continue;}}else{_ni=[1,I_fromInt(_nl)];_nj=_nm;continue;}}else{var _no=E(_nj);if(!_no[0]){_ni=_nk;_nj=[1,I_fromInt(_no[1])];continue;}else{return [1,I_mul(_nk[1],_no[1])];}}}},_np=function(_nq,_nr,_ns){while(1){var _nt=E(_ns);if(!_nt[0]){return E(_nr);}else{var _nu=B(_mZ(B(_nh(_nr,_nq)),B(_nf(E(_nt[1])[1]))));_ns=_nt[2];_nr=_nu;continue;}}},_nv=function(_nw){var _nx=new T(function(){return B(_kY(B(_kY([0,function(_ny){return E(E(_ny)[1])==45?[1,B(_mt(_mW,function(_nz){return new F(function(){return A(_nw,[[1,new T(function(){return B(_n9(B(_np(_nd,_ne,_nz))));})]]);});}))]:[2];}],[0,function(_nA){return E(E(_nA)[1])==43?[1,B(_mt(_mW,function(_nB){return new F(function(){return A(_nw,[[1,new T(function(){return B(_np(_nd,_ne,_nB));})]]);});}))]:[2];}])),new T(function(){return [1,B(_mt(_mW,function(_nC){return new F(function(){return A(_nw,[[1,new T(function(){return B(_np(_nd,_ne,_nC));})]]);});}))];})));});return new F(function(){return _kY([0,function(_nD){return E(E(_nD)[1])==101?E(_nx):[2];}],[0,function(_nE){return E(E(_nE)[1])==69?E(_nx):[2];}]);});},_nF=function(_nG){return new F(function(){return A(_nG,[_28]);});},_nH=function(_nI){return new F(function(){return A(_nI,[_28]);});},_nJ=function(_nK){return function(_nL){return E(E(_nL)[1])==46?[1,B(_mt(_mW,function(_nM){return new F(function(){return A(_nK,[[1,_nM]]);});}))]:[2];};},_nN=function(_nO){return [0,B(_nJ(_nO))];},_nP=function(_nQ){return new F(function(){return _mt(_mW,function(_nR){return [1,B(_lT(_nN,_nF,function(_nS){return [1,B(_lT(_nv,_nH,function(_nT){return new F(function(){return A(_nQ,[[5,[1,_nR,_nS,_nT]]]);});}))];}))];});});},_nU=function(_nV){return [1,B(_nP(_nV))];},_nW=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_nX=function(_nY){return new F(function(){return _86(_iy,_nY,_nW);});},_nZ=[0,8],_o0=[0,16],_o1=function(_o2){var _o3=function(_o4){return new F(function(){return A(_o2,[[5,[0,_nZ,_o4]]]);});},_o5=function(_o6){return new F(function(){return A(_o2,[[5,[0,_o0,_o6]]]);});};return function(_o7){return E(E(_o7)[1])==48?E([0,function(_o8){switch(E(E(_o8)[1])){case 79:return [1,B(_mt(_nZ,_o3))];case 88:return [1,B(_mt(_o0,_o5))];case 111:return [1,B(_mt(_nZ,_o3))];case 120:return [1,B(_mt(_o0,_o5))];default:return [2];}}]):[2];};},_o9=function(_oa){return [0,B(_o1(_oa))];},_ob=true,_oc=function(_od){var _oe=new T(function(){return B(A(_od,[_nZ]));}),_of=new T(function(){return B(A(_od,[_o0]));});return function(_og){switch(E(E(_og)[1])){case 79:return E(_oe);case 88:return E(_of);case 111:return E(_oe);case 120:return E(_of);default:return [2];}};},_oh=function(_oi){return [0,B(_oc(_oi))];},_oj=[0,92],_ok=function(_ol){return new F(function(){return A(_ol,[_mW]);});},_om=function(_on){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_on,_9));}))));});},_oo=function(_op){var _oq=E(_op);return _oq[0]==0?E(_oq[1]):I_toInt(_oq[1]);},_or=function(_os,_ot){var _ou=E(_os);if(!_ou[0]){var _ov=_ou[1],_ow=E(_ot);return _ow[0]==0?_ov<=_ow[1]:I_compareInt(_ow[1],_ov)>=0;}else{var _ox=_ou[1],_oy=E(_ot);return _oy[0]==0?I_compareInt(_ox,_oy[1])<=0:I_compare(_ox,_oy[1])<=0;}},_oz=function(_oA){return [2];},_oB=function(_oC){var _oD=E(_oC);if(!_oD[0]){return E(_oz);}else{var _oE=_oD[1],_oF=E(_oD[2]);return _oF[0]==0?E(_oE):function(_oG){return new F(function(){return _kY(B(A(_oE,[_oG])),new T(function(){return B(A(new T(function(){return B(_oB(_oF));}),[_oG]));}));});};}},_oH=function(_oI){return [2];},_oJ=function(_oK,_oL){var _oM=function(_oN,_oO){var _oP=E(_oN);if(!_oP[0]){return function(_oQ){return new F(function(){return A(_oQ,[_oK]);});};}else{var _oR=E(_oO);return _oR[0]==0?E(_oH):E(_oP[1])[1]!=E(_oR[1])[1]?E(_oH):function(_oS){return [0,function(_oT){return E(new T(function(){return B(A(new T(function(){return B(_oM(_oP[2],_oR[2]));}),[_oS]));}));}];};}};return function(_oU){return new F(function(){return A(_oM,[_oK,_oU,_oL]);});};},_oV=new T(function(){return B(unCStr("SOH"));}),_oW=[0,1],_oX=function(_oY){return [1,B(_oJ(_oV,function(_oZ){return E(new T(function(){return B(A(_oY,[_oW]));}));}))];},_p0=new T(function(){return B(unCStr("SO"));}),_p1=[0,14],_p2=function(_p3){return [1,B(_oJ(_p0,function(_p4){return E(new T(function(){return B(A(_p3,[_p1]));}));}))];},_p5=function(_p6){return [1,B(_lT(_oX,_p2,_p6))];},_p7=new T(function(){return B(unCStr("NUL"));}),_p8=[0,0],_p9=function(_pa){return [1,B(_oJ(_p7,function(_pb){return E(new T(function(){return B(A(_pa,[_p8]));}));}))];},_pc=new T(function(){return B(unCStr("STX"));}),_pd=[0,2],_pe=function(_pf){return [1,B(_oJ(_pc,function(_pg){return E(new T(function(){return B(A(_pf,[_pd]));}));}))];},_ph=new T(function(){return B(unCStr("ETX"));}),_pi=[0,3],_pj=function(_pk){return [1,B(_oJ(_ph,function(_pl){return E(new T(function(){return B(A(_pk,[_pi]));}));}))];},_pm=new T(function(){return B(unCStr("EOT"));}),_pn=[0,4],_po=function(_pp){return [1,B(_oJ(_pm,function(_pq){return E(new T(function(){return B(A(_pp,[_pn]));}));}))];},_pr=new T(function(){return B(unCStr("ENQ"));}),_ps=[0,5],_pt=function(_pu){return [1,B(_oJ(_pr,function(_pv){return E(new T(function(){return B(A(_pu,[_ps]));}));}))];},_pw=new T(function(){return B(unCStr("ACK"));}),_px=[0,6],_py=function(_pz){return [1,B(_oJ(_pw,function(_pA){return E(new T(function(){return B(A(_pz,[_px]));}));}))];},_pB=new T(function(){return B(unCStr("BEL"));}),_pC=[0,7],_pD=function(_pE){return [1,B(_oJ(_pB,function(_pF){return E(new T(function(){return B(A(_pE,[_pC]));}));}))];},_pG=new T(function(){return B(unCStr("BS"));}),_pH=[0,8],_pI=function(_pJ){return [1,B(_oJ(_pG,function(_pK){return E(new T(function(){return B(A(_pJ,[_pH]));}));}))];},_pL=new T(function(){return B(unCStr("HT"));}),_pM=[0,9],_pN=function(_pO){return [1,B(_oJ(_pL,function(_pP){return E(new T(function(){return B(A(_pO,[_pM]));}));}))];},_pQ=new T(function(){return B(unCStr("LF"));}),_pR=[0,10],_pS=function(_pT){return [1,B(_oJ(_pQ,function(_pU){return E(new T(function(){return B(A(_pT,[_pR]));}));}))];},_pV=new T(function(){return B(unCStr("VT"));}),_pW=[0,11],_pX=function(_pY){return [1,B(_oJ(_pV,function(_pZ){return E(new T(function(){return B(A(_pY,[_pW]));}));}))];},_q0=new T(function(){return B(unCStr("FF"));}),_q1=[0,12],_q2=function(_q3){return [1,B(_oJ(_q0,function(_q4){return E(new T(function(){return B(A(_q3,[_q1]));}));}))];},_q5=new T(function(){return B(unCStr("CR"));}),_q6=[0,13],_q7=function(_q8){return [1,B(_oJ(_q5,function(_q9){return E(new T(function(){return B(A(_q8,[_q6]));}));}))];},_qa=new T(function(){return B(unCStr("SI"));}),_qb=[0,15],_qc=function(_qd){return [1,B(_oJ(_qa,function(_qe){return E(new T(function(){return B(A(_qd,[_qb]));}));}))];},_qf=new T(function(){return B(unCStr("DLE"));}),_qg=[0,16],_qh=function(_qi){return [1,B(_oJ(_qf,function(_qj){return E(new T(function(){return B(A(_qi,[_qg]));}));}))];},_qk=new T(function(){return B(unCStr("DC1"));}),_ql=[0,17],_qm=function(_qn){return [1,B(_oJ(_qk,function(_qo){return E(new T(function(){return B(A(_qn,[_ql]));}));}))];},_qp=new T(function(){return B(unCStr("DC2"));}),_qq=[0,18],_qr=function(_qs){return [1,B(_oJ(_qp,function(_qt){return E(new T(function(){return B(A(_qs,[_qq]));}));}))];},_qu=new T(function(){return B(unCStr("DC3"));}),_qv=[0,19],_qw=function(_qx){return [1,B(_oJ(_qu,function(_qy){return E(new T(function(){return B(A(_qx,[_qv]));}));}))];},_qz=new T(function(){return B(unCStr("DC4"));}),_qA=[0,20],_qB=function(_qC){return [1,B(_oJ(_qz,function(_qD){return E(new T(function(){return B(A(_qC,[_qA]));}));}))];},_qE=new T(function(){return B(unCStr("NAK"));}),_qF=[0,21],_qG=function(_qH){return [1,B(_oJ(_qE,function(_qI){return E(new T(function(){return B(A(_qH,[_qF]));}));}))];},_qJ=new T(function(){return B(unCStr("SYN"));}),_qK=[0,22],_qL=function(_qM){return [1,B(_oJ(_qJ,function(_qN){return E(new T(function(){return B(A(_qM,[_qK]));}));}))];},_qO=new T(function(){return B(unCStr("ETB"));}),_qP=[0,23],_qQ=function(_qR){return [1,B(_oJ(_qO,function(_qS){return E(new T(function(){return B(A(_qR,[_qP]));}));}))];},_qT=new T(function(){return B(unCStr("CAN"));}),_qU=[0,24],_qV=function(_qW){return [1,B(_oJ(_qT,function(_qX){return E(new T(function(){return B(A(_qW,[_qU]));}));}))];},_qY=new T(function(){return B(unCStr("EM"));}),_qZ=[0,25],_r0=function(_r1){return [1,B(_oJ(_qY,function(_r2){return E(new T(function(){return B(A(_r1,[_qZ]));}));}))];},_r3=new T(function(){return B(unCStr("SUB"));}),_r4=[0,26],_r5=function(_r6){return [1,B(_oJ(_r3,function(_r7){return E(new T(function(){return B(A(_r6,[_r4]));}));}))];},_r8=new T(function(){return B(unCStr("ESC"));}),_r9=[0,27],_ra=function(_rb){return [1,B(_oJ(_r8,function(_rc){return E(new T(function(){return B(A(_rb,[_r9]));}));}))];},_rd=new T(function(){return B(unCStr("FS"));}),_re=[0,28],_rf=function(_rg){return [1,B(_oJ(_rd,function(_rh){return E(new T(function(){return B(A(_rg,[_re]));}));}))];},_ri=new T(function(){return B(unCStr("GS"));}),_rj=[0,29],_rk=function(_rl){return [1,B(_oJ(_ri,function(_rm){return E(new T(function(){return B(A(_rl,[_rj]));}));}))];},_rn=new T(function(){return B(unCStr("RS"));}),_ro=[0,30],_rp=function(_rq){return [1,B(_oJ(_rn,function(_rr){return E(new T(function(){return B(A(_rq,[_ro]));}));}))];},_rs=new T(function(){return B(unCStr("US"));}),_rt=[0,31],_ru=function(_rv){return [1,B(_oJ(_rs,function(_rw){return E(new T(function(){return B(A(_rv,[_rt]));}));}))];},_rx=new T(function(){return B(unCStr("SP"));}),_ry=[0,32],_rz=function(_rA){return [1,B(_oJ(_rx,function(_rB){return E(new T(function(){return B(A(_rA,[_ry]));}));}))];},_rC=new T(function(){return B(unCStr("DEL"));}),_rD=[0,127],_rE=function(_rF){return [1,B(_oJ(_rC,function(_rG){return E(new T(function(){return B(A(_rF,[_rD]));}));}))];},_rH=[1,_rE,_9],_rI=[1,_rz,_rH],_rJ=[1,_ru,_rI],_rK=[1,_rp,_rJ],_rL=[1,_rk,_rK],_rM=[1,_rf,_rL],_rN=[1,_ra,_rM],_rO=[1,_r5,_rN],_rP=[1,_r0,_rO],_rQ=[1,_qV,_rP],_rR=[1,_qQ,_rQ],_rS=[1,_qL,_rR],_rT=[1,_qG,_rS],_rU=[1,_qB,_rT],_rV=[1,_qw,_rU],_rW=[1,_qr,_rV],_rX=[1,_qm,_rW],_rY=[1,_qh,_rX],_rZ=[1,_qc,_rY],_s0=[1,_q7,_rZ],_s1=[1,_q2,_s0],_s2=[1,_pX,_s1],_s3=[1,_pS,_s2],_s4=[1,_pN,_s3],_s5=[1,_pI,_s4],_s6=[1,_pD,_s5],_s7=[1,_py,_s6],_s8=[1,_pt,_s7],_s9=[1,_po,_s8],_sa=[1,_pj,_s9],_sb=[1,_pe,_sa],_sc=[1,_p9,_sb],_sd=[1,_p5,_sc],_se=new T(function(){return B(_oB(_sd));}),_sf=[0,1114111],_sg=[0,34],_sh=[0,39],_si=function(_sj){var _sk=new T(function(){return B(A(_sj,[_pC]));}),_sl=new T(function(){return B(A(_sj,[_pH]));}),_sm=new T(function(){return B(A(_sj,[_pM]));}),_sn=new T(function(){return B(A(_sj,[_pR]));}),_so=new T(function(){return B(A(_sj,[_pW]));}),_sp=new T(function(){return B(A(_sj,[_q1]));}),_sq=new T(function(){return B(A(_sj,[_q6]));});return new F(function(){return _kY([0,function(_sr){switch(E(E(_sr)[1])){case 34:return E(new T(function(){return B(A(_sj,[_sg]));}));case 39:return E(new T(function(){return B(A(_sj,[_sh]));}));case 92:return E(new T(function(){return B(A(_sj,[_oj]));}));case 97:return E(_sk);case 98:return E(_sl);case 102:return E(_sp);case 110:return E(_sn);case 114:return E(_sq);case 116:return E(_sm);case 118:return E(_so);default:return [2];}}],new T(function(){return B(_kY([1,B(_lT(_oh,_ok,function(_ss){return [1,B(_mt(_ss,function(_st){var _su=B(_np(new T(function(){return B(_nf(E(_ss)[1]));}),_ne,_st));return !B(_or(_su,_sf))?[2]:B(A(_sj,[new T(function(){var _sv=B(_oo(_su));if(_sv>>>0>1114111){var _sw=B(_om(_sv));}else{var _sw=[0,_sv];}var _sx=_sw,_sy=_sx,_sz=_sy;return _sz;})]));}))];}))],new T(function(){return B(_kY([0,function(_sA){return E(E(_sA)[1])==94?E([0,function(_sB){switch(E(E(_sB)[1])){case 64:return E(new T(function(){return B(A(_sj,[_p8]));}));case 65:return E(new T(function(){return B(A(_sj,[_oW]));}));case 66:return E(new T(function(){return B(A(_sj,[_pd]));}));case 67:return E(new T(function(){return B(A(_sj,[_pi]));}));case 68:return E(new T(function(){return B(A(_sj,[_pn]));}));case 69:return E(new T(function(){return B(A(_sj,[_ps]));}));case 70:return E(new T(function(){return B(A(_sj,[_px]));}));case 71:return E(_sk);case 72:return E(_sl);case 73:return E(_sm);case 74:return E(_sn);case 75:return E(_so);case 76:return E(_sp);case 77:return E(_sq);case 78:return E(new T(function(){return B(A(_sj,[_p1]));}));case 79:return E(new T(function(){return B(A(_sj,[_qb]));}));case 80:return E(new T(function(){return B(A(_sj,[_qg]));}));case 81:return E(new T(function(){return B(A(_sj,[_ql]));}));case 82:return E(new T(function(){return B(A(_sj,[_qq]));}));case 83:return E(new T(function(){return B(A(_sj,[_qv]));}));case 84:return E(new T(function(){return B(A(_sj,[_qA]));}));case 85:return E(new T(function(){return B(A(_sj,[_qF]));}));case 86:return E(new T(function(){return B(A(_sj,[_qK]));}));case 87:return E(new T(function(){return B(A(_sj,[_qP]));}));case 88:return E(new T(function(){return B(A(_sj,[_qU]));}));case 89:return E(new T(function(){return B(A(_sj,[_qZ]));}));case 90:return E(new T(function(){return B(A(_sj,[_r4]));}));case 91:return E(new T(function(){return B(A(_sj,[_r9]));}));case 92:return E(new T(function(){return B(A(_sj,[_re]));}));case 93:return E(new T(function(){return B(A(_sj,[_rj]));}));case 94:return E(new T(function(){return B(A(_sj,[_ro]));}));case 95:return E(new T(function(){return B(A(_sj,[_rt]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_se,[_sj]));})));})));}));});},_sC=function(_sD){return new F(function(){return A(_sD,[_5c]);});},_sE=function(_sF){var _sG=E(_sF);if(!_sG[0]){return E(_sC);}else{var _sH=_sG[2],_sI=E(E(_sG[1])[1]);switch(_sI){case 9:return function(_sJ){return [0,function(_sK){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sJ]));}));}];};case 10:return function(_sL){return [0,function(_sM){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sL]));}));}];};case 11:return function(_sN){return [0,function(_sO){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sN]));}));}];};case 12:return function(_sP){return [0,function(_sQ){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sP]));}));}];};case 13:return function(_sR){return [0,function(_sS){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sR]));}));}];};case 32:return function(_sT){return [0,function(_sU){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sT]));}));}];};case 160:return function(_sV){return [0,function(_sW){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sV]));}));}];};default:var _sX=u_iswspace(_sI),_sY=_sX;return E(_sY)==0?E(_sC):function(_sZ){return [0,function(_t0){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sZ]));}));}];};}}},_t1=function(_t2){var _t3=new T(function(){return B(_t1(_t2));}),_t4=[1,function(_t5){return new F(function(){return A(_sE,[_t5,function(_t6){return E([0,function(_t7){return E(E(_t7)[1])==92?E(_t3):[2];}]);}]);});}];return new F(function(){return _kY([0,function(_t8){return E(E(_t8)[1])==92?E([0,function(_t9){var _ta=E(E(_t9)[1]);switch(_ta){case 9:return E(_t4);case 10:return E(_t4);case 11:return E(_t4);case 12:return E(_t4);case 13:return E(_t4);case 32:return E(_t4);case 38:return E(_t3);case 160:return E(_t4);default:var _tb=u_iswspace(_ta),_tc=_tb;return E(_tc)==0?[2]:E(_t4);}}]):[2];}],[0,function(_td){var _te=E(_td);return E(_te[1])==92?E(new T(function(){return B(_si(function(_tf){return new F(function(){return A(_t2,[[0,_tf,_ob]]);});}));})):B(A(_t2,[[0,_te,_1S]]));}]);});},_tg=function(_th,_ti){return new F(function(){return _t1(function(_tj){var _tk=E(_tj),_tl=E(_tk[1]);if(E(_tl[1])==34){if(!E(_tk[2])){return E(new T(function(){return B(A(_ti,[[1,new T(function(){return B(A(_th,[_9]));})]]));}));}else{return new F(function(){return _tg(function(_tm){return new F(function(){return A(_th,[[1,_tl,_tm]]);});},_ti);});}}else{return new F(function(){return _tg(function(_tn){return new F(function(){return A(_th,[[1,_tl,_tn]]);});},_ti);});}});});},_to=new T(function(){return B(unCStr("_\'"));}),_tp=function(_tq){var _tr=u_iswalnum(_tq),_ts=_tr;return E(_ts)==0?B(_86(_iy,[0,_tq],_to)):true;},_tt=function(_tu){return new F(function(){return _tp(E(_tu)[1]);});},_tv=new T(function(){return B(unCStr(",;()[]{}`"));}),_tw=new T(function(){return B(unCStr(".."));}),_tx=new T(function(){return B(unCStr("::"));}),_ty=new T(function(){return B(unCStr("->"));}),_tz=[0,64],_tA=[1,_tz,_9],_tB=[0,126],_tC=[1,_tB,_9],_tD=new T(function(){return B(unCStr("=>"));}),_tE=[1,_tD,_9],_tF=[1,_tC,_tE],_tG=[1,_tA,_tF],_tH=[1,_ty,_tG],_tI=new T(function(){return B(unCStr("<-"));}),_tJ=[1,_tI,_tH],_tK=[0,124],_tL=[1,_tK,_9],_tM=[1,_tL,_tJ],_tN=[1,_oj,_9],_tO=[1,_tN,_tM],_tP=[0,61],_tQ=[1,_tP,_9],_tR=[1,_tQ,_tO],_tS=[1,_tx,_tR],_tT=[1,_tw,_tS],_tU=function(_tV){return new F(function(){return _kY([1,function(_tW){return E(_tW)[0]==0?E(new T(function(){return B(A(_tV,[_mq]));})):[2];}],new T(function(){return B(_kY([0,function(_tX){return E(E(_tX)[1])==39?E([0,function(_tY){var _tZ=E(_tY);switch(E(_tZ[1])){case 39:return [2];case 92:return E(new T(function(){return B(_si(function(_u0){return [0,function(_u1){return E(E(_u1)[1])==39?E(new T(function(){return B(A(_tV,[[0,_u0]]));})):[2];}];}));}));default:return [0,function(_u2){return E(E(_u2)[1])==39?E(new T(function(){return B(A(_tV,[[0,_tZ]]));})):[2];}];}}]):[2];}],new T(function(){return B(_kY([0,function(_u3){return E(E(_u3)[1])==34?E(new T(function(){return B(_tg(_5q,_tV));})):[2];}],new T(function(){return B(_kY([0,function(_u4){return !B(_86(_iy,_u4,_tv))?[2]:B(A(_tV,[[2,[1,_u4,_9]]]));}],new T(function(){return B(_kY([0,function(_u5){return !B(_86(_iy,_u5,_nW))?[2]:[1,B(_mf(_nX,function(_u6){var _u7=[1,_u5,_u6];return !B(_86(_7i,_u7,_tT))?B(A(_tV,[[4,_u7]])):B(A(_tV,[[2,_u7]]));}))];}],new T(function(){return B(_kY([0,function(_u8){var _u9=E(_u8),_ua=_u9[1],_ub=u_iswalpha(_ua),_uc=_ub;return E(_uc)==0?E(_ua)==95?[1,B(_mf(_tt,function(_ud){return new F(function(){return A(_tV,[[3,[1,_u9,_ud]]]);});}))]:[2]:[1,B(_mf(_tt,function(_ue){return new F(function(){return A(_tV,[[3,[1,_u9,_ue]]]);});}))];}],new T(function(){return [1,B(_lT(_o9,_nU,_tV))];})));})));})));})));})));}));});},_uf=[0,0],_ug=function(_uh,_ui){return function(_uj){return new F(function(){return A(_sE,[_uj,function(_uk){return E(new T(function(){return B(_tU(function(_ul){var _um=E(_ul);return _um[0]==2?!B(_lv(_um[1],_lu))?[2]:E(new T(function(){return B(A(_uh,[_uf,function(_un){return [1,function(_uo){return new F(function(){return A(_sE,[_uo,function(_up){return E(new T(function(){return B(_tU(function(_uq){var _ur=E(_uq);return _ur[0]==2?!B(_lv(_ur[1],_ls))?[2]:E(new T(function(){return B(A(_ui,[_un]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_us=function(_ut,_uu,_uv){var _uw=function(_ux,_uy){return new F(function(){return _kY([1,function(_uz){return new F(function(){return A(_sE,[_uz,function(_uA){return E(new T(function(){return B(_tU(function(_uB){var _uC=E(_uB);if(_uC[0]==4){var _uD=E(_uC[1]);if(!_uD[0]){return new F(function(){return A(_ut,[_uC,_ux,_uy]);});}else{return E(E(_uD[1])[1])==45?E(_uD[2])[0]==0?E([1,function(_uE){return new F(function(){return A(_sE,[_uE,function(_uF){return E(new T(function(){return B(_tU(function(_uG){return new F(function(){return A(_ut,[_uG,_ux,function(_uH){return new F(function(){return A(_uy,[new T(function(){return [0, -E(_uH)[1]];})]);});}]);});}));}));}]);});}]):B(A(_ut,[_uC,_ux,_uy])):B(A(_ut,[_uC,_ux,_uy]));}}else{return new F(function(){return A(_ut,[_uC,_ux,_uy]);});}}));}));}]);});}],new T(function(){return [1,B(_ug(_uw,_uy))];}));});};return new F(function(){return _uw(_uu,_uv);});},_uI=function(_uJ,_uK){return [2];},_uL=function(_uM){var _uN=E(_uM);return _uN[0]==0?[1,new T(function(){return B(_np(new T(function(){return B(_nf(E(_uN[1])[1]));}),_ne,_uN[2]));})]:E(_uN[2])[0]==0?E(_uN[3])[0]==0?[1,new T(function(){return B(_np(_nd,_ne,_uN[1]));})]:[0]:[0];},_uO=function(_uP){var _uQ=E(_uP);if(_uQ[0]==5){var _uR=B(_uL(_uQ[1]));return _uR[0]==0?E(_uI):function(_uS,_uT){return new F(function(){return A(_uT,[new T(function(){return [0,B(_oo(_uR[1]))];})]);});};}else{return E(_uI);}},_uU=function(_uV){return [1,function(_uW){return new F(function(){return A(_sE,[_uW,function(_uX){return E([3,_uV,_lL]);}]);});}];},_uY=new T(function(){return B(_us(_uO,_uf,_uU));}),_uZ=function(_v0){while(1){var _v1=(function(_v2){var _v3=E(_v2);if(!_v3[0]){return [0];}else{var _v4=_v3[2],_v5=E(_v3[1]);if(!E(_v5[2])[0]){return [1,_v5[1],new T(function(){return B(_uZ(_v4));})];}else{_v0=_v4;return null;}}})(_v0);if(_v1!=null){return _v1;}}},_v6=function(_v7){var _v8=B(_uZ(B(_kO(_uY,_v7))));return _v8[0]==0?E(_kK):E(_v8[2])[0]==0?E(_v8[1]):E(_kM);},_v9=function(_va,_vb,_vc,_vd,_ve,_vf){var _vg=function(_vh){var _vi=[0,_va,new T(function(){return B(_7X(_v6,_vh));})];return function(_vj,_vk,_vl,_vm,_vn){return new F(function(){return A(_ke,[_vj,function(_vo,_vp,_vq){return new F(function(){return A(_vk,[_vi,_vp,new T(function(){var _vr=E(E(_vp)[2]),_vs=E(_vq),_vt=E(_vs[1]),_vu=B(_cW(_vt[1],_vt[2],_vt[3],_vs[2],_vr[1],_vr[2],_vr[3],_9));return [0,E(_vu[1]),_vu[2]];})]);});},_vn,function(_vv,_vw,_vx){return new F(function(){return A(_vm,[_vi,_vw,new T(function(){var _vy=E(E(_vw)[2]),_vz=E(_vx),_vA=E(_vz[1]),_vB=B(_cW(_vA[1],_vA[2],_vA[3],_vz[2],_vy[1],_vy[2],_vy[3],_9));return [0,E(_vB[1]),_vB[2]];})]);});},_vn]);});};},_vC=function(_vD,_vE,_vF,_vG,_vH){var _vI=function(_vJ,_vK,_vL){return new F(function(){return A(_vg,[_vJ,_vK,_vE,_vF,function(_vM,_vN,_vO){return new F(function(){return A(_vG,[_vM,_vN,new T(function(){return B(_dL(_vL,_vO));})]);});},function(_vP){return new F(function(){return A(_vH,[new T(function(){return B(_dL(_vL,_vP));})]);});}]);});},_vQ=function(_vR){return new F(function(){return _vI(_9,_vD,new T(function(){var _vS=E(E(_vD)[2]),_vT=E(_vR),_vU=E(_vT[1]),_vV=B(_cW(_vU[1],_vU[2],_vU[3],_vT[2],_vS[1],_vS[2],_vS[3],_9));return [0,E(_vV[1]),_vV[2]];}));});};return new F(function(){return _eW(_kA,_kI,_vD,function(_vW,_vX,_vY){return new F(function(){return A(_vg,[_vW,_vX,_vE,_vF,function(_vZ,_w0,_w1){return new F(function(){return A(_vE,[_vZ,_w0,new T(function(){return B(_dL(_vY,_w1));})]);});},function(_w2){return new F(function(){return A(_vF,[new T(function(){return B(_dL(_vY,_w2));})]);});}]);});},_vQ,_vI,_vQ);});};return new F(function(){return _ew(_iS,_vb,function(_w3,_w4,_w5){return new F(function(){return _vC(_w4,_vc,_vd,function(_w6,_w7,_w8){return new F(function(){return A(_vc,[_w6,_w7,new T(function(){return B(_dL(_w5,_w8));})]);});},function(_w9){return new F(function(){return A(_vd,[new T(function(){return B(_dL(_w5,_w9));})]);});});});},_vd,function(_wa,_wb,_wc){return new F(function(){return _vC(_wb,_vc,_vd,function(_wd,_we,_wf){return new F(function(){return A(_ve,[_wd,_we,new T(function(){return B(_dL(_wc,_wf));})]);});},function(_wg){return new F(function(){return A(_vf,[new T(function(){return B(_dL(_wc,_wg));})]);});});});});});},_wh=new T(function(){return B(unCStr("letter or digit"));}),_wi=[1,_wh,_9],_wj=function(_wk){var _wl=u_iswalnum(E(_wk)[1]),_wm=_wl;return E(_wm)==0?false:true;},_wn=function(_wo,_wp,_wq,_wr,_ws){var _wt=E(_wo),_wu=E(_wt[2]);return new F(function(){return _i6(_g7,_kh,_wj,_wt[1],_wu[1],_wu[2],_wu[3],_wt[3],_wp,_ws);});},_wv=function(_ww,_wx,_wy,_wz,_wA){return new F(function(){return _jw(_wn,_wi,_ww,_wx,_wy,_wz,_wA);});},_wB=function(_wC,_wD,_wE,_wF,_wG){return new F(function(){return _dT(_wv,_wC,function(_wH,_wI,_wJ){return new F(function(){return _v9(_wH,_wI,_wD,_wE,function(_wK,_wL,_wM){return new F(function(){return A(_wD,[_wK,_wL,new T(function(){return B(_dL(_wJ,_wM));})]);});},function(_wN){return new F(function(){return A(_wE,[new T(function(){return B(_dL(_wJ,_wN));})]);});});});},_wG,function(_wO,_wP,_wQ){return new F(function(){return _v9(_wO,_wP,_wD,_wE,function(_wR,_wS,_wT){return new F(function(){return A(_wF,[_wR,_wS,new T(function(){return B(_dL(_wQ,_wT));})]);});},function(_wU){return new F(function(){return A(_wG,[new T(function(){return B(_dL(_wQ,_wU));})]);});});});},_wG);});},_wV=new T(function(){return B(unCStr("SHOW"));}),_wW=[0,_wV,_9],_wX=function(_wY,_wZ,_x0,_x1){var _x2=function(_x3){return new F(function(){return A(_x1,[[0,_wY,_wW],_wZ,new T(function(){var _x4=E(E(_wZ)[2]),_x5=_x4[1],_x6=_x4[2],_x7=_x4[3],_x8=E(_x3),_x9=E(_x8[1]),_xa=B(_cW(_x9[1],_x9[2],_x9[3],_x8[2],_x5,_x6,_x7,_9)),_xb=E(_xa[1]),_xc=B(_cW(_xb[1],_xb[2],_xb[3],_xa[2],_x5,_x6,_x7,_9));return [0,E(_xc[1]),_xc[2]];})]);});};return new F(function(){return _wB(_wZ,function(_xd,_xe,_xf){return new F(function(){return A(_x0,[[0,_wY,_xd],_xe,new T(function(){var _xg=E(E(_xe)[2]),_xh=E(_xf),_xi=E(_xh[1]),_xj=B(_cW(_xi[1],_xi[2],_xi[3],_xh[2],_xg[1],_xg[2],_xg[3],_9));return [0,E(_xj[1]),_xj[2]];})]);});},_x2,function(_xk,_xl,_xm){return new F(function(){return A(_x1,[[0,_wY,_xk],_xl,new T(function(){var _xn=E(E(_xl)[2]),_xo=E(_xm),_xp=E(_xo[1]),_xq=B(_cW(_xp[1],_xp[2],_xp[3],_xo[2],_xn[1],_xn[2],_xn[3],_9));return [0,E(_xq[1]),_xq[2]];})]);});},_x2);});},_xr=new T(function(){return B(unCStr("sS"));}),_xs=[0,58],_xt=new T(function(){return B(_jN(_j3,_xs));}),_xu=[1,_wh,_9],_xv=function(_xw,_xx,_xy,_xz,_xA,_xB,_xC,_xD,_xE){var _xF=function(_xG,_xH){var _xI=new T(function(){var _xJ=B(_jb(_xG,_xH,_xu));return [0,E(_xJ[1]),_xJ[2]];});return new F(function(){return A(_xt,[[0,_xw,E([0,_xx,_xy,_xz]),E(_xA)],_xB,_xC,function(_xK,_xL,_xM){return new F(function(){return A(_xD,[_xK,_xL,new T(function(){return B(_dL(_xI,_xM));})]);});},function(_xN){return new F(function(){return A(_xE,[new T(function(){return B(_dL(_xI,_xN));})]);});}]);});},_xO=E(_xw);if(!_xO[0]){return new F(function(){return _xF([0,_xx,_xy,_xz],_gd);});}else{var _xP=_xO[2],_xQ=E(_xO[1]),_xR=_xQ[1],_xS=u_iswalnum(_xR),_xT=_xS;if(!E(_xT)){return new F(function(){return _xF([0,_xx,_xy,_xz],[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_xQ,_9],_gb));})])],_9]);});}else{switch(E(_xR)){case 9:var _xU=[0,_xx,_xy,(_xz+8|0)-B(_ge(_xz-1|0,8))|0];break;case 10:var _xU=[0,_xx,_xy+1|0,1];break;default:var _xU=[0,_xx,_xy,_xz+1|0];}var _xV=_xU,_xW=[0,E(_xV),_9],_xX=[0,_xP,E(_xV),E(_xA)];return new F(function(){return A(_xB,[_xQ,_xX,_xW]);});}}},_xY=function(_xZ,_y0,_y1,_y2,_y3){var _y4=E(_xZ),_y5=E(_y4[2]);return new F(function(){return _xv(_y4[1],_y5[1],_y5[2],_y5[3],_y4[3],_y0,_y1,_y2,_y3);});},_y6=function(_y7,_y8,_y9,_ya,_yb,_yc,_yd){var _ye=function(_yf,_yg,_yh,_yi,_yj,_yk){return new F(function(){return _yl(_yg,function(_ym,_yn,_yo){return new F(function(){return A(_yh,[[1,_yf,_ym],_yn,new T(function(){var _yp=E(E(_yn)[2]),_yq=E(_yo),_yr=E(_yq[1]),_ys=B(_cW(_yr[1],_yr[2],_yr[3],_yq[2],_yp[1],_yp[2],_yp[3],_9));return [0,E(_ys[1]),_ys[2]];})]);});},_yi,function(_yt,_yu,_yv){return new F(function(){return A(_yj,[[1,_yf,_yt],_yu,new T(function(){var _yw=E(E(_yu)[2]),_yx=E(_yv),_yy=E(_yx[1]),_yz=B(_cW(_yy[1],_yy[2],_yy[3],_yx[2],_yw[1],_yw[2],_yw[3],_9));return [0,E(_yz[1]),_yz[2]];})]);});},_yk);});},_yl=function(_yA,_yB,_yC,_yD,_yE){return new F(function(){return A(_y8,[_yA,function(_yF,_yG,_yH){return new F(function(){return A(_yB,[_9,_yG,new T(function(){var _yI=E(E(_yG)[2]),_yJ=E(_yH),_yK=E(_yJ[1]),_yL=B(_cW(_yK[1],_yK[2],_yK[3],_yJ[2],_yI[1],_yI[2],_yI[3],_9));return [0,E(_yL[1]),_yL[2]];})]);});},_yC,function(_yM,_yN,_yO){return new F(function(){return A(_yD,[_9,_yN,new T(function(){var _yP=E(E(_yN)[2]),_yQ=E(_yO),_yR=E(_yQ[1]),_yS=B(_cW(_yR[1],_yR[2],_yR[3],_yQ[2],_yP[1],_yP[2],_yP[3],_9));return [0,E(_yS[1]),_yS[2]];})]);});},function(_yT){return new F(function(){return A(_y7,[_yA,function(_yU,_yV,_yW){return new F(function(){return _ye(_yU,_yV,_yB,_yC,function(_yX,_yY,_yZ){return new F(function(){return A(_yB,[_yX,_yY,new T(function(){return B(_dL(_yW,_yZ));})]);});},function(_z0){return new F(function(){return A(_yC,[new T(function(){return B(_dL(_yW,_z0));})]);});});});},_yC,function(_z1,_z2,_z3){return new F(function(){return _ye(_z1,_z2,_yB,_yC,function(_z4,_z5,_z6){return new F(function(){return A(_yD,[_z4,_z5,new T(function(){var _z7=E(_yT),_z8=E(_z7[1]),_z9=E(_z3),_za=E(_z9[1]),_zb=E(_z6),_zc=E(_zb[1]),_zd=B(_cW(_za[1],_za[2],_za[3],_z9[2],_zc[1],_zc[2],_zc[3],_zb[2])),_ze=E(_zd[1]),_zf=B(_cW(_z8[1],_z8[2],_z8[3],_z7[2],_ze[1],_ze[2],_ze[3],_zd[2]));return [0,E(_zf[1]),_zf[2]];})]);});},function(_zg){return new F(function(){return A(_yE,[new T(function(){var _zh=E(_yT),_zi=E(_zh[1]),_zj=E(_z3),_zk=E(_zj[1]),_zl=E(_zg),_zm=E(_zl[1]),_zn=B(_cW(_zk[1],_zk[2],_zk[3],_zj[2],_zm[1],_zm[2],_zm[3],_zl[2])),_zo=E(_zn[1]),_zp=B(_cW(_zi[1],_zi[2],_zi[3],_zh[2],_zo[1],_zo[2],_zo[3],_zn[2]));return [0,E(_zp[1]),_zp[2]];})]);});});});},function(_zq){return new F(function(){return A(_yE,[new T(function(){return B(_dL(_yT,_zq));})]);});}]);});}]);});};return new F(function(){return _yl(_y9,_ya,_yb,_yc,_yd);});},_zr=new T(function(){return B(unCStr("tab"));}),_zs=[1,_zr,_9],_zt=[0,9],_zu=function(_zv){return function(_zw,_zx,_zy,_zz,_zA){return new F(function(){return _jw(new T(function(){return B(_jN(_zv,_zt));}),_zs,_zw,_zx,_zy,_zz,_zA);});};},_zB=new T(function(){return B(_zu(_j3));}),_zC=[0,39],_zD=[1,_zC,_9],_zE=new T(function(){return B(unCStr("\'\\\'\'"));}),_zF=function(_zG){var _zH=E(E(_zG)[1]);return _zH==39?E(_zE):[1,_zC,new T(function(){return B(_hJ(_zH,_zD));})];},_zI=function(_zJ,_zK){return [1,_ga,new T(function(){return B(_i0(_zJ,[1,_ga,_zK]));})];},_zL=function(_zM){return new F(function(){return _e(_zE,_zM);});},_zN=function(_zO,_zP){var _zQ=E(E(_zP)[1]);return _zQ==39?E(_zL):function(_zR){return [1,_zC,new T(function(){return B(_hJ(_zQ,[1,_zC,_zR]));})];};},_zS=[0,_zN,_zF,_zI],_zT=function(_zU,_zV,_zW,_zX,_zY){var _zZ=new T(function(){return B(_bm(_zU));}),_A0=function(_A1){return new F(function(){return A(_zX,[_5c,_zW,new T(function(){var _A2=E(E(_zW)[2]),_A3=E(_A1),_A4=E(_A3[1]),_A5=B(_cW(_A4[1],_A4[2],_A4[3],_A3[2],_A2[1],_A2[2],_A2[3],_9));return [0,E(_A5[1]),_A5[2]];})]);});};return new F(function(){return A(_zV,[_zW,function(_A6,_A7,_A8){return new F(function(){return A(_zY,[new T(function(){var _A9=E(E(_A7)[2]),_Aa=E(_A8),_Ab=E(_Aa[1]),_Ac=B(_cW(_Ab[1],_Ab[2],_Ab[3],_Aa[2],_A9[1],_A9[2],_A9[3],[1,new T(function(){return [1,E(B(A(_zZ,[_A6])))];}),_9]));return [0,E(_Ac[1]),_Ac[2]];})]);});},_A0,function(_Ad,_Ae,_Af){return new F(function(){return A(_zX,[_5c,_zW,new T(function(){var _Ag=E(E(_zW)[2]),_Ah=E(E(_Ae)[2]),_Ai=E(_Af),_Aj=E(_Ai[1]),_Ak=B(_cW(_Aj[1],_Aj[2],_Aj[3],_Ai[2],_Ah[1],_Ah[2],_Ah[3],[1,new T(function(){return [1,E(B(A(_zZ,[_Ad])))];}),_9])),_Al=E(_Ak[1]),_Am=B(_cW(_Al[1],_Al[2],_Al[3],_Ak[2],_Ag[1],_Ag[2],_Ag[3],_9));return [0,E(_Am[1]),_Am[2]];})]);});},_A0]);});},_An=function(_Ao,_Ap,_Aq,_Ar){return new F(function(){return _zT(_zS,_zB,_Ap,function(_As,_At,_Au){return new F(function(){return A(_Aq,[_Ao,_At,new T(function(){var _Av=E(E(_At)[2]),_Aw=E(_Au),_Ax=E(_Aw[1]),_Ay=B(_cW(_Ax[1],_Ax[2],_Ax[3],_Aw[2],_Av[1],_Av[2],_Av[3],_9));return [0,E(_Ay[1]),_Ay[2]];})]);});},_Ar);});},_Az=function(_AA,_AB,_AC,_AD,_AE){return new F(function(){return A(_ke,[_AA,function(_AF,_AG,_AH){return new F(function(){return _An(_AF,_AG,function(_AI,_AJ,_AK){return new F(function(){return A(_AB,[_AI,_AJ,new T(function(){return B(_dL(_AH,_AK));})]);});},function(_AL){return new F(function(){return A(_AC,[new T(function(){return B(_dL(_AH,_AL));})]);});});});},_AC,function(_AM,_AN,_AO){return new F(function(){return _An(_AM,_AN,function(_AP,_AQ,_AR){return new F(function(){return A(_AD,[_AP,_AQ,new T(function(){return B(_dL(_AO,_AR));})]);});},function(_AS){return new F(function(){return A(_AE,[new T(function(){return B(_dL(_AO,_AS));})]);});});});},_AE]);});},_AT=[0,E(_9)],_AU=[1,_AT,_9],_AV=function(_AW,_AX,_AY,_AZ,_B0,_B1,_B2){return new F(function(){return A(_AW,[new T(function(){return B(A(_AX,[_AY]));}),function(_B3){var _B4=E(_B3);if(!_B4[0]){return E(new T(function(){return B(A(_B2,[[0,E(_AZ),_AU]]));}));}else{var _B5=E(_B4[1]);return new F(function(){return A(_B1,[_B5[1],[0,_B5[2],E(_AZ),E(_B0)],[0,E(_AZ),_9]]);});}}]);});},_B6=new T(function(){return B(unCStr("end of input"));}),_B7=[1,_B6,_9],_B8=function(_B9,_Ba,_Bb,_Bc,_Bd,_Be,_Bf,_Bg){return new F(function(){return _jw(function(_Bh,_Bi,_Bj,_Bk,_Bl){return new F(function(){return _zT(_Bb,function(_Bm,_Bn,_Bo,_Bp,_Bq){var _Br=E(_Bm);return new F(function(){return _AV(_B9,_Ba,_Br[1],_Br[2],_Br[3],_Bn,_Bq);});},_Bh,_Bk,_Bl);});},_B7,_Bc,_Bd,_Be,_Bf,_Bg);});},_Bs=function(_Bt,_Bu,_Bv,_Bw,_Bx,_By){return new F(function(){return _B8(_g7,_iQ,_zS,_Bu,function(_Bz,_BA,_BB){return new F(function(){return A(_Bv,[_Bt,_BA,new T(function(){var _BC=E(E(_BA)[2]),_BD=E(_BB),_BE=E(_BD[1]),_BF=B(_cW(_BE[1],_BE[2],_BE[3],_BD[2],_BC[1],_BC[2],_BC[3],_9));return [0,E(_BF[1]),_BF[2]];})]);});},_Bw,function(_BG,_BH,_BI){return new F(function(){return A(_Bx,[_Bt,_BH,new T(function(){var _BJ=E(E(_BH)[2]),_BK=E(_BI),_BL=E(_BK[1]),_BM=B(_cW(_BL[1],_BL[2],_BL[3],_BK[2],_BJ[1],_BJ[2],_BJ[3],_9));return [0,E(_BM[1]),_BM[2]];})]);});},_By);});},_BN=function(_BO,_BP,_BQ,_BR,_BS){return new F(function(){return A(_ke,[_BO,function(_BT,_BU,_BV){return new F(function(){return _Bs(_BT,_BU,_BP,_BQ,function(_BW,_BX,_BY){return new F(function(){return A(_BP,[_BW,_BX,new T(function(){return B(_dL(_BV,_BY));})]);});},function(_BZ){return new F(function(){return A(_BQ,[new T(function(){return B(_dL(_BV,_BZ));})]);});});});},_BQ,function(_C0,_C1,_C2){return new F(function(){return _Bs(_C0,_C1,_BP,_BQ,function(_C3,_C4,_C5){return new F(function(){return A(_BR,[_C3,_C4,new T(function(){return B(_dL(_C2,_C5));})]);});},function(_C6){return new F(function(){return A(_BS,[new T(function(){return B(_dL(_C2,_C6));})]);});});});},_BS]);});},_C7=function(_C8,_C9,_Ca,_Cb){var _Cc=function(_Cd){var _Ce=function(_Cf){return new F(function(){return A(_Cb,[new T(function(){return B(_dL(_Cd,_Cf));})]);});};return new F(function(){return _Az(_C8,_C9,_Ce,function(_Cg,_Ch,_Ci){return new F(function(){return A(_Ca,[_Cg,_Ch,new T(function(){return B(_dL(_Cd,_Ci));})]);});},_Ce);});};return new F(function(){return _BN(_C8,_C9,_Cc,_Ca,_Cc);});},_Cj=function(_Ck,_Cl,_Cm,_Cn,_Co){return new F(function(){return _C7(_Ck,_Cl,_Cn,_Co);});},_Cp=function(_Cq){return true;},_Cr=function(_Cs,_Ct,_Cu,_Cv,_Cw){var _Cx=E(_Cs),_Cy=E(_Cx[2]);return new F(function(){return _i6(_g7,_iQ,_Cp,_Cx[1],_Cy[1],_Cy[2],_Cy[3],_Cx[3],_Ct,_Cw);});},_Cz=function(_CA,_CB,_CC,_CD,_CE){return new F(function(){return A(_zB,[_CA,function(_CF,_CG,_CH){return new F(function(){return _y6(_Cr,_Cj,_CG,_CB,_CC,function(_CI,_CJ,_CK){return new F(function(){return A(_CB,[_CI,_CJ,new T(function(){return B(_dL(_CH,_CK));})]);});},function(_CL){return new F(function(){return A(_CC,[new T(function(){return B(_dL(_CH,_CL));})]);});});});},_CC,function(_CM,_CN,_CO){return new F(function(){return _y6(_Cr,_Cj,_CN,_CB,_CC,function(_CP,_CQ,_CR){return new F(function(){return A(_CD,[_CP,_CQ,new T(function(){return B(_dL(_CO,_CR));})]);});},function(_CS){return new F(function(){return A(_CE,[new T(function(){return B(_dL(_CO,_CS));})]);});});});},_CE]);});},_CT=[0,_wV,_9],_CU=[0,_9,1,1],_CV=function(_CW){return E(_CW);},_CX=function(_CY){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_CY));}))));});},_CZ=new T(function(){return B(_CX("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_D0=new T(function(){return B(_CX("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_D1=[0,_g7,_D0,_CV,_CZ],_D2=[0,10],_D3=[1,_D2,_9],_D4=function(_D5){return new F(function(){return unAppCStr("string error",new T(function(){var _D6=E(_D5),_D7=E(_D6[1]);return B(_e(B(_9R(_D7[1],_D7[2],_D7[3],_D6[2])),_D3));}));});},_D8=function(_D9,_Da,_Db,_Dc,_Dd){return new F(function(){return A(_zB,[_Da,function(_De,_Df,_Dg){return new F(function(){return A(_Db,[_D9,_Df,new T(function(){var _Dh=E(E(_Df)[2]),_Di=E(_Dg),_Dj=E(_Di[1]),_Dk=B(_cW(_Dj[1],_Dj[2],_Dj[3],_Di[2],_Dh[1],_Dh[2],_Dh[3],_9));return [0,E(_Dk[1]),_Dk[2]];})]);});},_Dd,function(_Dl,_Dm,_Dn){return new F(function(){return A(_Dc,[_D9,_Dm,new T(function(){var _Do=E(E(_Dm)[2]),_Dp=E(_Dn),_Dq=E(_Dp[1]),_Dr=B(_cW(_Dq[1],_Dq[2],_Dq[3],_Dp[2],_Do[1],_Do[2],_Do[3],_9));return [0,E(_Dr[1]),_Dr[2]];})]);});},_Dd]);});},_Ds=function(_Dt,_Du,_Dv,_Dw,_Dx){return new F(function(){return A(_ke,[_Dt,function(_Dy,_Dz,_DA){return new F(function(){return _D8(_Dy,_Dz,_Du,function(_DB,_DC,_DD){return new F(function(){return A(_Du,[_DB,_DC,new T(function(){return B(_dL(_DA,_DD));})]);});},function(_DE){return new F(function(){return A(_Dv,[new T(function(){return B(_dL(_DA,_DE));})]);});});});},_Dv,function(_DF,_DG,_DH){return new F(function(){return _D8(_DF,_DG,_Du,function(_DI,_DJ,_DK){return new F(function(){return A(_Dw,[_DI,_DJ,new T(function(){return B(_dL(_DH,_DK));})]);});},function(_DL){return new F(function(){return A(_Dx,[new T(function(){return B(_dL(_DH,_DL));})]);});});});},_Dx]);});},_DM=function(_DN,_DO,_DP,_DQ,_DR){return new F(function(){return _Ds(_DN,_DO,_DP,_DQ,function(_DS){var _DT=E(_DN),_DU=E(_DT[2]),_DV=E(_DT[1]);return _DV[0]==0?B(A(_DR,[new T(function(){var _DW=E(_DS),_DX=E(_DW[1]),_DY=B(_cW(_DX[1],_DX[2],_DX[3],_DW[2],_DU[1],_DU[2],_DU[3],_AU));return [0,E(_DY[1]),_DY[2]];})])):B(A(_DO,[_DV[1],[0,_DV[2],E(_DU),E(_DT[3])],[0,E(_DU),_9]]));});});},_DZ=function(_E0,_E1,_E2,_E3,_E4){return new F(function(){return _dj(_DM,_E0,_E1,_E2,_E3);});},_E5=function(_E6,_E7,_E8){return [0,_E6,E(E(_E7)),_E8];},_E9=function(_Ea,_Eb,_Ec){var _Ed=new T(function(){return B(_iK(_Ea));}),_Ee=new T(function(){return B(_iK(_Ea));});return new F(function(){return A(_Eb,[_Ec,function(_Ef,_Eg,_Eh){return new F(function(){return A(_Ed,[[0,new T(function(){return B(A(_Ee,[new T(function(){return B(_E5(_Ef,_Eg,_Eh));})]));})]]);});},function(_Ei){return new F(function(){return A(_Ed,[[0,new T(function(){return B(A(_Ee,[[1,_Ei]]));})]]);});},function(_Ej,_Ek,_El){return new F(function(){return A(_Ed,[new T(function(){return [1,E(B(A(_Ee,[new T(function(){return B(_E5(_Ej,_Ek,_El));})])))];})]);});},function(_Em){return new F(function(){return A(_Ed,[new T(function(){return [1,E(B(A(_Ee,[[1,_Em]])))];})]);});}]);});},_En=function(_Eo){return function(_Ep,_Eq,_Er,_Es,_Et){return new F(function(){return A(_Es,[new T(function(){var _Eu=B(_E9(_D1,_Ev,[0,new T(function(){var _Ew=B(_E9(_D1,_DZ,[0,_Eo,E(_CU),E(_5c)]));if(!_Ew[0]){var _Ex=E(_Ew[1]),_Ey=_Ex[0]==0?B(_e(_Ex[1],_D3)):B(_D4(_Ex[1]));}else{var _Ez=E(_Ew[1]),_Ey=_Ez[0]==0?B(_e(_Ez[1],_D3)):B(_D4(_Ez[1]));}return _Ey;}),E(_CU),E(_5c)]));if(!_Eu[0]){var _EA=E(_Eu[1]),_EB=_EA[0]==0?E(_EA[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_EA[1]));})));})],_9],_9],_CT];}else{var _EC=E(_Eu[1]),_EB=_EC[0]==0?E(_EC[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_EC[1]));})));})],_9],_9],_CT];}return _EB;}),_Ep,new T(function(){return [0,E(E(_Ep)[2]),_9];})]);});};},_ED=function(_EE,_EF,_EG,_EH,_EI){return new F(function(){return _Cz(_EE,function(_EJ,_EK,_EL){return new F(function(){return A(_En,[_EJ,_EK,_EF,_EG,function(_EM,_EN,_EO){return new F(function(){return A(_EF,[_EM,_EN,new T(function(){return B(_dL(_EL,_EO));})]);});},function(_EP){return new F(function(){return A(_EG,[new T(function(){return B(_dL(_EL,_EP));})]);});}]);});},_EG,function(_EQ,_ER,_ES){return new F(function(){return A(_En,[_EQ,_ER,_EF,_EG,function(_ET,_EU,_EV){return new F(function(){return A(_EH,[_ET,_EU,new T(function(){return B(_dL(_ES,_EV));})]);});},function(_EW){return new F(function(){return A(_EI,[new T(function(){return B(_dL(_ES,_EW));})]);});}]);});},_EI);});},_EX=function(_EY,_EZ,_F0,_F1,_F2,_F3){var _F4=function(_F5,_F6,_F7,_F8,_F9){var _Fa=function(_Fb,_Fc,_Fd,_Fe,_Ff){return new F(function(){return A(_F8,[[0,[1,[0,_EY,_Fc,_Fd]],_Fb],_Fe,new T(function(){var _Fg=E(_Ff),_Fh=E(_Fg[1]),_Fi=E(E(_Fe)[2]),_Fj=B(_cW(_Fh[1],_Fh[2],_Fh[3],_Fg[2],_Fi[1],_Fi[2],_Fi[3],_9));return [0,E(_Fj[1]),_Fj[2]];})]);});},_Fk=function(_Fl){return new F(function(){return _Fa(_9,_wV,_9,_F5,new T(function(){var _Fm=E(E(_F5)[2]),_Fn=E(_Fl),_Fo=E(_Fn[1]),_Fp=B(_cW(_Fo[1],_Fo[2],_Fo[3],_Fn[2],_Fm[1],_Fm[2],_Fm[3],_9));return [0,E(_Fp[1]),_Fp[2]];}));});};return new F(function(){return _ED(_F5,function(_Fq,_Fr,_Fs){var _Ft=E(_Fq),_Fu=E(_Ft[2]);return new F(function(){return A(_F6,[[0,[1,[0,_EY,_Fu[1],_Fu[2]]],_Ft[1]],_Fr,new T(function(){var _Fv=E(_Fs),_Fw=E(_Fv[1]),_Fx=E(E(_Fr)[2]),_Fy=B(_cW(_Fw[1],_Fw[2],_Fw[3],_Fv[2],_Fx[1],_Fx[2],_Fx[3],_9));return [0,E(_Fy[1]),_Fy[2]];})]);});},_Fk,function(_Fz,_FA,_FB){var _FC=E(_Fz),_FD=E(_FC[2]);return new F(function(){return _Fa(_FC[1],_FD[1],_FD[2],_FA,_FB);});},_Fk);});};return new F(function(){return A(_ke,[_EZ,function(_FE,_FF,_FG){return new F(function(){return _F4(_FF,_F0,_F1,function(_FH,_FI,_FJ){return new F(function(){return A(_F0,[_FH,_FI,new T(function(){return B(_dL(_FG,_FJ));})]);});},function(_FK){return new F(function(){return A(_F1,[new T(function(){return B(_dL(_FG,_FK));})]);});});});},_F3,function(_FL,_FM,_FN){return new F(function(){return _F4(_FM,_F0,_F1,function(_FO,_FP,_FQ){return new F(function(){return A(_F2,[_FO,_FP,new T(function(){return B(_dL(_FN,_FQ));})]);});},function(_FR){return new F(function(){return A(_F3,[new T(function(){return B(_dL(_FN,_FR));})]);});});});},_F3]);});},_FS=new T(function(){return B(unCStr(" associative operator"));}),_FT=function(_FU,_FV){var _FW=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_FU,_FS));}))))];}),_9];return function(_FX,_FY,_FZ,_G0,_G1){return new F(function(){return A(_FV,[_FX,function(_G2,_G3,_G4){return new F(function(){return A(_G1,[new T(function(){var _G5=E(E(_G3)[2]),_G6=E(_G4),_G7=E(_G6[1]),_G8=B(_cW(_G7[1],_G7[2],_G7[3],_G6[2],_G5[1],_G5[2],_G5[3],_FW));return [0,E(_G8[1]),_G8[2]];})]);});},_G1,function(_G9,_Ga,_Gb){return new F(function(){return A(_G1,[new T(function(){var _Gc=E(E(_Ga)[2]),_Gd=E(_Gb),_Ge=E(_Gd[1]),_Gf=B(_cW(_Ge[1],_Ge[2],_Ge[3],_Gd[2],_Gc[1],_Gc[2],_Gc[3],_FW));return [0,E(_Gf[1]),_Gf[2]];})]);});},_G1]);});};},_Gg=function(_Gh,_Gi,_Gj,_Gk,_Gl,_Gm){var _Gn=E(_Gh);if(!_Gn[0]){return new F(function(){return A(_Gm,[new T(function(){return [0,E(E(_Gi)[2]),_9];})]);});}else{return new F(function(){return A(_Gn[1],[_Gi,_Gj,_Gk,_Gl,function(_Go){return new F(function(){return _Gg(_Gn[2],_Gi,_Gj,_Gk,function(_Gp,_Gq,_Gr){return new F(function(){return A(_Gl,[_Gp,_Gq,new T(function(){return B(_dL(_Go,_Gr));})]);});},function(_Gs){return new F(function(){return A(_Gm,[new T(function(){return B(_dL(_Go,_Gs));})]);});});});}]);});}},_Gt=new T(function(){return B(unCStr("right"));}),_Gu=new T(function(){return B(unCStr("left"));}),_Gv=new T(function(){return B(unCStr("non"));}),_Gw=new T(function(){return B(unCStr("operator"));}),_Gx=[1,_Gw,_9],_Gy=[1,_9,_9],_Gz=function(_GA){var _GB=E(_GA);if(!_GB[0]){return [0,_9,_9,_9,_9,_9];}else{var _GC=_GB[2],_GD=E(_GB[1]);switch(_GD[0]){case 0:var _GE=_GD[1],_GF=B(_Gz(_GC)),_GG=_GF[1],_GH=_GF[2],_GI=_GF[3],_GJ=_GF[4],_GK=_GF[5];switch(E(_GD[2])){case 0:return [0,_GG,_GH,[1,_GE,_GI],_GJ,_GK];case 1:return [0,_GG,[1,_GE,_GH],_GI,_GJ,_GK];default:return [0,[1,_GE,_GG],_GH,_GI,_GJ,_GK];}break;case 1:var _GL=B(_Gz(_GC));return [0,_GL[1],_GL[2],_GL[3],[1,_GD[1],_GL[4]],_GL[5]];default:var _GM=B(_Gz(_GC));return [0,_GM[1],_GM[2],_GM[3],_GM[4],[1,_GD[1],_GM[5]]];}}},_GN=function(_GO,_GP){while(1){var _GQ=(function(_GR,_GS){var _GT=E(_GS);if(!_GT[0]){return E(_GR);}else{var _GU=new T(function(){var _GV=B(_Gz(_GT[1]));return [0,_GV[1],_GV[2],_GV[3],_GV[4],_GV[5]];}),_GW=new T(function(){return E(E(_GU)[2]);}),_GX=new T(function(){return B(_FT(_Gu,function(_GY,_GZ,_H0,_H1,_H2){return new F(function(){return _Gg(_GW,_GY,_GZ,_H0,_H1,_H2);});}));}),_H3=new T(function(){return E(E(_GU)[1]);}),_H4=new T(function(){return E(E(_GU)[3]);}),_H5=new T(function(){return B(_FT(_Gv,function(_H6,_H7,_H8,_H9,_Ha){return new F(function(){return _Gg(_H4,_H6,_H7,_H8,_H9,_Ha);});}));}),_Hb=function(_Hc,_Hd,_He,_Hf,_Hg,_Hh){var _Hi=function(_Hj,_Hk,_Hl,_Hm,_Hn){var _Ho=new T(function(){return B(A(_Hc,[_Hj]));});return new F(function(){return _Gg(new T(function(){return E(E(_GU)[5]);}),_Hk,function(_Hp,_Hq,_Hr){return new F(function(){return A(_Hl,[new T(function(){return B(A(_Hp,[_Ho]));}),_Hq,new T(function(){var _Hs=E(E(_Hq)[2]),_Ht=E(_Hr),_Hu=E(_Ht[1]),_Hv=B(_cW(_Hu[1],_Hu[2],_Hu[3],_Ht[2],_Hs[1],_Hs[2],_Hs[3],_9));return [0,E(_Hv[1]),_Hv[2]];})]);});},_Hm,function(_Hw,_Hx,_Hy){return new F(function(){return A(_Hn,[new T(function(){return B(A(_Hw,[_Ho]));}),_Hx,new T(function(){var _Hz=E(E(_Hx)[2]),_HA=_Hz[1],_HB=_Hz[2],_HC=_Hz[3],_HD=E(_Hy),_HE=E(_HD[1]),_HF=_HE[2],_HG=_HE[3],_HH=E(_HD[2]);if(!_HH[0]){switch(B(_cO(_HE[1],_HA))){case 0:var _HI=[0,E(_Hz),_9];break;case 1:if(_HF>=_HB){if(_HF!=_HB){var _HJ=[0,E(_HE),_9];}else{if(_HG>=_HC){var _HK=_HG!=_HC?[0,E(_HE),_9]:[0,E(_HE),_cV];}else{var _HK=[0,E(_Hz),_9];}var _HL=_HK,_HJ=_HL;}var _HM=_HJ,_HN=_HM;}else{var _HN=[0,E(_Hz),_9];}var _HO=_HN,_HI=_HO;break;default:var _HI=[0,E(_HE),_9];}var _HP=_HI;}else{var _HQ=B(_jb(_HE,_HH,_Gy)),_HR=E(_HQ[1]),_HS=B(_cW(_HR[1],_HR[2],_HR[3],_HQ[2],_HA,_HB,_HC,_9)),_HP=[0,E(_HS[1]),_HS[2]];}var _HT=_HP,_HU=_HT,_HV=_HU,_HW=_HV;return _HW;})]);});},function(_HX){return new F(function(){return A(_Hn,[_Ho,_Hk,new T(function(){var _HY=E(E(_Hk)[2]),_HZ=_HY[1],_I0=_HY[2],_I1=_HY[3],_I2=E(_HX),_I3=B(_jb(_I2[1],_I2[2],_Gy)),_I4=E(_I3[1]),_I5=B(_cW(_I4[1],_I4[2],_I4[3],_I3[2],_HZ,_I0,_I1,_9)),_I6=E(_I5[1]),_I7=B(_cW(_I6[1],_I6[2],_I6[3],_I5[2],_HZ,_I0,_I1,_9));return [0,E(_I7[1]),_I7[2]];})]);});});});};return new F(function(){return A(_GR,[_Hd,function(_I8,_I9,_Ia){return new F(function(){return _Hi(_I8,_I9,_He,_Hf,function(_Ib,_Ic,_Id){return new F(function(){return A(_He,[_Ib,_Ic,new T(function(){return B(_dL(_Ia,_Id));})]);});});});},_Hf,function(_Ie,_If,_Ig){return new F(function(){return _Hi(_Ie,_If,_He,_Hf,function(_Ih,_Ii,_Ij){return new F(function(){return A(_Hg,[_Ih,_Ii,new T(function(){return B(_dL(_Ig,_Ij));})]);});});});},_Hh]);});},_Ik=function(_Il,_Im,_In,_Io,_Ip){var _Iq=function(_Ir,_Is,_It){return new F(function(){return _Hb(_Ir,_Is,_Im,_In,function(_Iu,_Iv,_Iw){return new F(function(){return A(_Io,[_Iu,_Iv,new T(function(){return B(_dL(_It,_Iw));})]);});},function(_Ix){return new F(function(){return A(_Ip,[new T(function(){return B(_dL(_It,_Ix));})]);});});});};return new F(function(){return _Gg(new T(function(){return E(E(_GU)[4]);}),_Il,function(_Iy,_Iz,_IA){return new F(function(){return _Hb(_Iy,_Iz,_Im,_In,function(_IB,_IC,_ID){return new F(function(){return A(_Im,[_IB,_IC,new T(function(){return B(_dL(_IA,_ID));})]);});},function(_IE){return new F(function(){return A(_In,[new T(function(){return B(_dL(_IA,_IE));})]);});});});},_In,function(_IF,_IG,_IH){return new F(function(){return _Iq(_IF,_IG,new T(function(){var _II=E(_IH),_IJ=E(_II[2]);if(!_IJ[0]){var _IK=E(_II);}else{var _IL=B(_jb(_II[1],_IJ,_Gy)),_IK=[0,E(_IL[1]),_IL[2]];}var _IM=_IK;return _IM;}));});},function(_IN){return new F(function(){return _Iq(_5q,_Il,new T(function(){var _IO=E(E(_Il)[2]),_IP=E(_IN),_IQ=B(_jb(_IP[1],_IP[2],_Gy)),_IR=E(_IQ[1]),_IS=B(_cW(_IR[1],_IR[2],_IR[3],_IQ[2],_IO[1],_IO[2],_IO[3],_9));return [0,E(_IS[1]),_IS[2]];}));});});});},_IT=function(_IU,_IV,_IW,_IX,_IY,_IZ){var _J0=function(_J1){return new F(function(){return A(_GX,[_IV,_IW,_IX,function(_J2,_J3,_J4){return new F(function(){return A(_IY,[_J2,_J3,new T(function(){return B(_dL(_J1,_J4));})]);});},function(_J5){return new F(function(){return A(_H5,[_IV,_IW,_IX,function(_J6,_J7,_J8){return new F(function(){return A(_IY,[_J6,_J7,new T(function(){var _J9=E(_J1),_Ja=E(_J9[1]),_Jb=E(_J5),_Jc=E(_Jb[1]),_Jd=E(_J8),_Je=E(_Jd[1]),_Jf=B(_cW(_Jc[1],_Jc[2],_Jc[3],_Jb[2],_Je[1],_Je[2],_Je[3],_Jd[2])),_Jg=E(_Jf[1]),_Jh=B(_cW(_Ja[1],_Ja[2],_Ja[3],_J9[2],_Jg[1],_Jg[2],_Jg[3],_Jf[2]));return [0,E(_Jh[1]),_Jh[2]];})]);});},function(_Ji){return new F(function(){return A(_IZ,[new T(function(){var _Jj=E(_J1),_Jk=E(_Jj[1]),_Jl=E(_J5),_Jm=E(_Jl[1]),_Jn=E(_Ji),_Jo=E(_Jn[1]),_Jp=B(_cW(_Jm[1],_Jm[2],_Jm[3],_Jl[2],_Jo[1],_Jo[2],_Jo[3],_Jn[2])),_Jq=E(_Jp[1]),_Jr=B(_cW(_Jk[1],_Jk[2],_Jk[3],_Jj[2],_Jq[1],_Jq[2],_Jq[3],_Jp[2]));return [0,E(_Jr[1]),_Jr[2]];})]);});}]);});}]);});},_Js=function(_Jt,_Ju,_Jv,_Jw,_Jx,_Jy){var _Jz=function(_JA,_JB,_JC){return new F(function(){return A(_Jv,[new T(function(){return B(A(_Jt,[_IU,_JA]));}),_JB,new T(function(){var _JD=E(E(_JB)[2]),_JE=E(_JC),_JF=E(_JE[1]),_JG=B(_cW(_JF[1],_JF[2],_JF[3],_JE[2],_JD[1],_JD[2],_JD[3],_9));return [0,E(_JG[1]),_JG[2]];})]);});};return new F(function(){return _Ik(_Ju,function(_JH,_JI,_JJ){return new F(function(){return _IT(_JH,_JI,_Jz,_Jw,function(_JK,_JL,_JM){return new F(function(){return _Jz(_JK,_JL,new T(function(){var _JN=E(_JJ),_JO=E(_JN[1]),_JP=E(_JM),_JQ=E(_JP[1]),_JR=B(_cW(_JO[1],_JO[2],_JO[3],_JN[2],_JQ[1],_JQ[2],_JQ[3],_JP[2]));return [0,E(_JR[1]),_JR[2]];},1));});},function(_JS){return new F(function(){return _Jz(_JH,_JI,new T(function(){var _JT=E(E(_JI)[2]),_JU=E(_JJ),_JV=E(_JU[1]),_JW=E(_JS),_JX=E(_JW[1]),_JY=B(_cW(_JX[1],_JX[2],_JX[3],_JW[2],_JT[1],_JT[2],_JT[3],_9)),_JZ=E(_JY[1]),_K0=B(_cW(_JV[1],_JV[2],_JV[3],_JU[2],_JZ[1],_JZ[2],_JZ[3],_JY[2]));return [0,E(_K0[1]),_K0[2]];},1));});});});},_Jw,function(_K1,_K2,_K3){var _K4=function(_K5,_K6,_K7){return new F(function(){return A(_Jx,[new T(function(){return B(A(_Jt,[_IU,_K5]));}),_K6,new T(function(){var _K8=E(E(_K6)[2]),_K9=E(_K3),_Ka=E(_K9[1]),_Kb=E(_K7),_Kc=E(_Kb[1]),_Kd=B(_cW(_Ka[1],_Ka[2],_Ka[3],_K9[2],_Kc[1],_Kc[2],_Kc[3],_Kb[2])),_Ke=E(_Kd[1]),_Kf=B(_cW(_Ke[1],_Ke[2],_Ke[3],_Kd[2],_K8[1],_K8[2],_K8[3],_9));return [0,E(_Kf[1]),_Kf[2]];})]);});};return new F(function(){return _IT(_K1,_K2,_Jz,_Jw,_K4,function(_Kg){return new F(function(){return _K4(_K1,_K2,new T(function(){var _Kh=E(E(_K2)[2]),_Ki=E(_Kg),_Kj=E(_Ki[1]),_Kk=B(_cW(_Kj[1],_Kj[2],_Kj[3],_Ki[2],_Kh[1],_Kh[2],_Kh[3],_9));return [0,E(_Kk[1]),_Kk[2]];},1));});});});},_Jy);});};return new F(function(){return _Gg(_H3,_IV,function(_Kl,_Km,_Kn){return new F(function(){return _Js(_Kl,_Km,_IW,_IX,function(_Ko,_Kp,_Kq){return new F(function(){return A(_IW,[_Ko,_Kp,new T(function(){return B(_dL(_Kn,_Kq));})]);});},function(_Kr){return new F(function(){return A(_IX,[new T(function(){return B(_dL(_Kn,_Kr));})]);});});});},_IX,function(_Ks,_Kt,_Ku){return new F(function(){return _Js(_Ks,_Kt,_IW,_IX,function(_Kv,_Kw,_Kx){return new F(function(){return A(_IY,[_Kv,_Kw,new T(function(){return B(_dL(_Ku,_Kx));})]);});},function(_Ky){return new F(function(){return _J0(new T(function(){return B(_dL(_Ku,_Ky));}));});});});},_J0);});},_Kz=new T(function(){return B(_FT(_Gt,function(_KA,_KB,_KC,_KD,_KE){return new F(function(){return _Gg(_H3,_KA,_KB,_KC,_KD,_KE);});}));}),_KF=function(_KG,_KH,_KI,_KJ,_KK,_KL){var _KM=function(_KN){return new F(function(){return A(_Kz,[_KH,_KI,_KJ,function(_KO,_KP,_KQ){return new F(function(){return A(_KK,[_KO,_KP,new T(function(){return B(_dL(_KN,_KQ));})]);});},function(_KR){return new F(function(){return A(_H5,[_KH,_KI,_KJ,function(_KS,_KT,_KU){return new F(function(){return A(_KK,[_KS,_KT,new T(function(){var _KV=E(_KN),_KW=E(_KV[1]),_KX=E(_KR),_KY=E(_KX[1]),_KZ=E(_KU),_L0=E(_KZ[1]),_L1=B(_cW(_KY[1],_KY[2],_KY[3],_KX[2],_L0[1],_L0[2],_L0[3],_KZ[2])),_L2=E(_L1[1]),_L3=B(_cW(_KW[1],_KW[2],_KW[3],_KV[2],_L2[1],_L2[2],_L2[3],_L1[2]));return [0,E(_L3[1]),_L3[2]];})]);});},function(_L4){return new F(function(){return A(_KL,[new T(function(){var _L5=E(_KN),_L6=E(_L5[1]),_L7=E(_KR),_L8=E(_L7[1]),_L9=E(_L4),_La=E(_L9[1]),_Lb=B(_cW(_L8[1],_L8[2],_L8[3],_L7[2],_La[1],_La[2],_La[3],_L9[2])),_Lc=E(_Lb[1]),_Ld=B(_cW(_L6[1],_L6[2],_L6[3],_L5[2],_Lc[1],_Lc[2],_Lc[3],_Lb[2]));return [0,E(_Ld[1]),_Ld[2]];})]);});}]);});}]);});},_Le=function(_Lf,_Lg,_Lh,_Li,_Lj,_Lk){var _Ll=function(_Lm){var _Ln=new T(function(){return B(A(_Lf,[_KG,_Lm]));});return function(_Lo,_Lp,_Lq,_Lr,_Ls){return new F(function(){return _KF(_Ln,_Lo,_Lp,_Lq,_Lr,function(_Lt){return new F(function(){return A(_Lr,[_Ln,_Lo,new T(function(){var _Lu=E(E(_Lo)[2]),_Lv=E(_Lt),_Lw=E(_Lv[1]),_Lx=B(_cW(_Lw[1],_Lw[2],_Lw[3],_Lv[2],_Lu[1],_Lu[2],_Lu[3],_9));return [0,E(_Lx[1]),_Lx[2]];})]);});});});};};return new F(function(){return _Ik(_Lg,function(_Ly,_Lz,_LA){return new F(function(){return A(_Ll,[_Ly,_Lz,_Lh,_Li,function(_LB,_LC,_LD){return new F(function(){return A(_Lh,[_LB,_LC,new T(function(){return B(_dL(_LA,_LD));})]);});},function(_LE){return new F(function(){return A(_Li,[new T(function(){return B(_dL(_LA,_LE));})]);});}]);});},_Li,function(_LF,_LG,_LH){return new F(function(){return A(_Ll,[_LF,_LG,_Lh,_Li,function(_LI,_LJ,_LK){return new F(function(){return A(_Lj,[_LI,_LJ,new T(function(){return B(_dL(_LH,_LK));})]);});},function(_LL){return new F(function(){return A(_Lk,[new T(function(){return B(_dL(_LH,_LL));})]);});}]);});},_Lk);});};return new F(function(){return _Gg(_GW,_KH,function(_LM,_LN,_LO){return new F(function(){return _Le(_LM,_LN,_KI,_KJ,function(_LP,_LQ,_LR){return new F(function(){return A(_KI,[_LP,_LQ,new T(function(){return B(_dL(_LO,_LR));})]);});},function(_LS){return new F(function(){return A(_KJ,[new T(function(){return B(_dL(_LO,_LS));})]);});});});},_KJ,function(_LT,_LU,_LV){return new F(function(){return _Le(_LT,_LU,_KI,_KJ,function(_LW,_LX,_LY){return new F(function(){return A(_KK,[_LW,_LX,new T(function(){return B(_dL(_LV,_LY));})]);});},function(_LZ){return new F(function(){return _KM(new T(function(){return B(_dL(_LV,_LZ));}));});});});},_KM);});},_M0=function(_M1,_M2,_M3,_M4,_M5,_M6){var _M7=function(_M8,_M9,_Ma,_Mb,_Mc,_Md){var _Me=function(_Mf){return function(_Mg,_Mh,_Mi,_Mj,_Mk){return new F(function(){return A(_Kz,[_Mg,_Mh,_Mi,_Mj,function(_Ml){return new F(function(){return A(_GX,[_Mg,_Mh,_Mi,function(_Mm,_Mn,_Mo){return new F(function(){return A(_Mj,[_Mm,_Mn,new T(function(){return B(_dL(_Ml,_Mo));})]);});},function(_Mp){return new F(function(){return A(_H5,[_Mg,_Mh,_Mi,function(_Mq,_Mr,_Ms){return new F(function(){return A(_Mj,[_Mq,_Mr,new T(function(){var _Mt=E(_Ml),_Mu=E(_Mt[1]),_Mv=E(_Mp),_Mw=E(_Mv[1]),_Mx=E(_Ms),_My=E(_Mx[1]),_Mz=B(_cW(_Mw[1],_Mw[2],_Mw[3],_Mv[2],_My[1],_My[2],_My[3],_Mx[2])),_MA=E(_Mz[1]),_MB=B(_cW(_Mu[1],_Mu[2],_Mu[3],_Mt[2],_MA[1],_MA[2],_MA[3],_Mz[2]));return [0,E(_MB[1]),_MB[2]];})]);});},function(_MC){return new F(function(){return A(_Mj,[new T(function(){return B(A(_M8,[_M1,_Mf]));}),_Mg,new T(function(){var _MD=E(E(_Mg)[2]),_ME=E(_Ml),_MF=E(_ME[1]),_MG=E(_Mp),_MH=E(_MG[1]),_MI=E(_MC),_MJ=E(_MI[1]),_MK=B(_cW(_MJ[1],_MJ[2],_MJ[3],_MI[2],_MD[1],_MD[2],_MD[3],_9)),_ML=E(_MK[1]),_MM=B(_cW(_MH[1],_MH[2],_MH[3],_MG[2],_ML[1],_ML[2],_ML[3],_MK[2])),_MN=E(_MM[1]),_MO=B(_cW(_MF[1],_MF[2],_MF[3],_ME[2],_MN[1],_MN[2],_MN[3],_MM[2]));return [0,E(_MO[1]),_MO[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _Ik(_M9,function(_MP,_MQ,_MR){return new F(function(){return A(_Me,[_MP,_MQ,_Ma,_Mb,function(_MS,_MT,_MU){return new F(function(){return A(_Ma,[_MS,_MT,new T(function(){return B(_dL(_MR,_MU));})]);});},function(_MV){return new F(function(){return A(_Mb,[new T(function(){return B(_dL(_MR,_MV));})]);});}]);});},_Mb,function(_MW,_MX,_MY){return new F(function(){return A(_Me,[_MW,_MX,_Ma,_Mb,function(_MZ,_N0,_N1){return new F(function(){return A(_Mc,[_MZ,_N0,new T(function(){return B(_dL(_MY,_N1));})]);});},function(_N2){return new F(function(){return A(_Md,[new T(function(){return B(_dL(_MY,_N2));})]);});}]);});},_Md);});};return new F(function(){return _jw(function(_N3,_N4,_N5,_N6,_N7){return new F(function(){return _IT(_M1,_N3,_N4,_N5,_N6,function(_N8){return new F(function(){return _KF(_M1,_N3,_N4,_N5,function(_N9,_Na,_Nb){return new F(function(){return A(_N6,[_N9,_Na,new T(function(){return B(_dL(_N8,_Nb));})]);});},function(_Nc){var _Nd=function(_Ne){return new F(function(){return A(_N6,[_M1,_N3,new T(function(){var _Nf=E(E(_N3)[2]),_Ng=E(_N8),_Nh=E(_Ng[1]),_Ni=E(_Nc),_Nj=E(_Ni[1]),_Nk=E(_Ne),_Nl=E(_Nk[1]),_Nm=B(_cW(_Nl[1],_Nl[2],_Nl[3],_Nk[2],_Nf[1],_Nf[2],_Nf[3],_9)),_Nn=E(_Nm[1]),_No=B(_cW(_Nj[1],_Nj[2],_Nj[3],_Ni[2],_Nn[1],_Nn[2],_Nn[3],_Nm[2])),_Np=E(_No[1]),_Nq=B(_cW(_Nh[1],_Nh[2],_Nh[3],_Ng[2],_Np[1],_Np[2],_Np[3],_No[2]));return [0,E(_Nq[1]),_Nq[2]];})]);});};return new F(function(){return _Gg(_H4,_N3,function(_Nr,_Ns,_Nt){return new F(function(){return _M7(_Nr,_Ns,_N4,_N5,function(_Nu,_Nv,_Nw){return new F(function(){return A(_N4,[_Nu,_Nv,new T(function(){return B(_dL(_Nt,_Nw));})]);});},function(_Nx){return new F(function(){return A(_N5,[new T(function(){return B(_dL(_Nt,_Nx));})]);});});});},_N5,function(_Ny,_Nz,_NA){return new F(function(){return _M7(_Ny,_Nz,_N4,_N5,function(_NB,_NC,_ND){return new F(function(){return A(_N6,[_NB,_NC,new T(function(){var _NE=E(_N8),_NF=E(_NE[1]),_NG=E(_Nc),_NH=E(_NG[1]),_NI=E(_NA),_NJ=E(_NI[1]),_NK=E(_ND),_NL=E(_NK[1]),_NM=B(_cW(_NJ[1],_NJ[2],_NJ[3],_NI[2],_NL[1],_NL[2],_NL[3],_NK[2])),_NN=E(_NM[1]),_NO=B(_cW(_NH[1],_NH[2],_NH[3],_NG[2],_NN[1],_NN[2],_NN[3],_NM[2])),_NP=E(_NO[1]),_NQ=B(_cW(_NF[1],_NF[2],_NF[3],_NE[2],_NP[1],_NP[2],_NP[3],_NO[2]));return [0,E(_NQ[1]),_NQ[2]];})]);});},function(_NR){return new F(function(){return _Nd(new T(function(){var _NS=E(_NA),_NT=E(_NS[1]),_NU=E(_NR),_NV=E(_NU[1]),_NW=B(_cW(_NT[1],_NT[2],_NT[3],_NS[2],_NV[1],_NV[2],_NV[3],_NU[2]));return [0,E(_NW[1]),_NW[2]];},1));});});});},_Nd);});});});});});},_Gx,_M2,_M3,_M4,_M5,_M6);});};_GO=function(_NX,_NY,_NZ,_O0,_O1){return new F(function(){return _Ik(_NX,function(_O2,_O3,_O4){return new F(function(){return _M0(_O2,_O3,_NY,_NZ,function(_O5,_O6,_O7){return new F(function(){return A(_NY,[_O5,_O6,new T(function(){return B(_dL(_O4,_O7));})]);});},function(_O8){return new F(function(){return A(_NZ,[new T(function(){return B(_dL(_O4,_O8));})]);});});});},_NZ,function(_O9,_Oa,_Ob){return new F(function(){return _M0(_O9,_Oa,_NY,_NZ,function(_Oc,_Od,_Oe){return new F(function(){return A(_O0,[_Oc,_Od,new T(function(){return B(_dL(_Ob,_Oe));})]);});},function(_Of){return new F(function(){return A(_O1,[new T(function(){return B(_dL(_Ob,_Of));})]);});});});},_O1);});};_GP=_GT[2];return null;}})(_GO,_GP);if(_GQ!=null){return _GQ;}}},_Og=0,_Oh=[3,_],_Oi=function(_Oj,_Ok){return [5,_Oh,_Oj,_Ok];},_Ol=new T(function(){return B(unCStr("=>"));}),_Om=function(_On){return E(E(_On)[1]);},_Oo=function(_Op,_Oq,_Or,_Os){while(1){var _Ot=E(_Os);if(!_Ot[0]){return [0,_Op,_Oq,_Or];}else{var _Ou=_Ot[2];switch(E(E(_Ot[1])[1])){case 9:var _Ov=(_Or+8|0)-B(_ge(_Or-1|0,8))|0;_Os=_Ou;_Or=_Ov;continue;case 10:var _Ow=_Oq+1|0;_Or=1;_Os=_Ou;_Oq=_Ow;continue;default:var _Ov=_Or+1|0;_Os=_Ou;_Or=_Ov;continue;}}}},_Ox=function(_Oy){return E(E(_Oy)[1]);},_Oz=function(_OA){return E(E(_OA)[2]);},_OB=function(_OC){return [0,E(E(_OC)[2]),_9];},_OD=function(_OE,_OF,_OG,_OH,_OI,_OJ,_OK){var _OL=E(_OF);if(!_OL[0]){return new F(function(){return A(_OJ,[_9,_OG,new T(function(){return B(_OB(_OG));})]);});}else{var _OM=E(_OG),_ON=E(_OM[2]),_OO=new T(function(){return B(_Om(_OE));}),_OP=[0,E(_ON),[1,[2,E([1,_ga,new T(function(){return B(_i0(_OL,_gb));})])],_gd]],_OQ=[2,E([1,_ga,new T(function(){return B(_i0(_OL,_gb));})])],_OR=new T(function(){var _OS=B(_Oo(_ON[1],_ON[2],_ON[3],_OL));return [0,_OS[1],_OS[2],_OS[3]];}),_OT=function(_OU,_OV){var _OW=E(_OU);if(!_OW[0]){return new F(function(){return A(_OH,[_OL,new T(function(){return [0,_OV,E(E(_OR)),E(_OM[3])];}),new T(function(){return [0,E(E(_OR)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_Ox(_OO));}),[new T(function(){return B(A(new T(function(){return B(_Oz(_OE));}),[_OV]));}),function(_OX){var _OY=E(_OX);if(!_OY[0]){return E(new T(function(){return B(A(_OI,[_OP]));}));}else{var _OZ=E(_OY[1]),_P0=E(_OZ[1]);return E(_OW[1])[1]!=_P0[1]?B(A(_OI,[[0,E(_ON),[1,_OQ,[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_P0,_9],_gb));})])],_9]]]])):B(_OT(_OW[2],_OZ[2]));}}]);});}};return new F(function(){return A(_Ox,[_OO,new T(function(){return B(A(_Oz,[_OE,_OM[1]]));}),function(_P1){var _P2=E(_P1);if(!_P2[0]){return E(new T(function(){return B(A(_OK,[_OP]));}));}else{var _P3=E(_P2[1]),_P4=E(_P3[1]);return E(_OL[1])[1]!=_P4[1]?B(A(_OK,[[0,E(_ON),[1,_OQ,[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_P4,_9],_gb));})])],_9]]]])):B(_OT(_OL[2],_P3[2]));}}]);});}},_P5=function(_P6,_P7,_P8,_P9,_Pa){return new F(function(){return _OD(_kG,_Ol,_P6,function(_Pb,_Pc,_Pd){return new F(function(){return A(_P7,[_Oi,_Pc,new T(function(){var _Pe=E(E(_Pc)[2]),_Pf=E(_Pd),_Pg=E(_Pf[1]),_Ph=B(_cW(_Pg[1],_Pg[2],_Pg[3],_Pf[2],_Pe[1],_Pe[2],_Pe[3],_9));return [0,E(_Ph[1]),_Ph[2]];})]);});},_P8,function(_Pi,_Pj,_Pk){return new F(function(){return A(_P9,[_Oi,_Pj,new T(function(){var _Pl=E(E(_Pj)[2]),_Pm=E(_Pk),_Pn=E(_Pm[1]),_Po=B(_cW(_Pn[1],_Pn[2],_Pn[3],_Pm[2],_Pl[1],_Pl[2],_Pl[3],_9));return [0,E(_Po[1]),_Po[2]];})]);});},_Pa);});},_Pp=[0,_P5,_Og],_Pq=[1,_Pp,_9],_Pr=[1,_Pq,_9],_Ps=1,_Pt=[2,_],_Pu=function(_Oj,_Ok){return [5,_Pt,_Oj,_Ok];},_Pv=new T(function(){return B(unCStr("\\/"));}),_Pw=function(_Px,_Py,_Pz,_PA,_PB){return new F(function(){return _OD(_kG,_Pv,_Px,function(_PC,_PD,_PE){return new F(function(){return A(_Py,[_Pu,_PD,new T(function(){var _PF=E(E(_PD)[2]),_PG=E(_PE),_PH=E(_PG[1]),_PI=B(_cW(_PH[1],_PH[2],_PH[3],_PG[2],_PF[1],_PF[2],_PF[3],_9));return [0,E(_PI[1]),_PI[2]];})]);});},_Pz,function(_PJ,_PK,_PL){return new F(function(){return A(_PA,[_Pu,_PK,new T(function(){var _PM=E(E(_PK)[2]),_PN=E(_PL),_PO=E(_PN[1]),_PP=B(_cW(_PO[1],_PO[2],_PO[3],_PN[2],_PM[1],_PM[2],_PM[3],_9));return [0,E(_PP[1]),_PP[2]];})]);});},_PB);});},_PQ=[0,_Pw,_Ps],_PR=[1,_],_PS=function(_Oj,_Ok){return [5,_PR,_Oj,_Ok];},_PT=new T(function(){return B(unCStr("/\\"));}),_PU=function(_PV,_PW,_PX,_PY,_PZ){return new F(function(){return _OD(_kG,_PT,_PV,function(_Q0,_Q1,_Q2){return new F(function(){return A(_PW,[_PS,_Q1,new T(function(){var _Q3=E(E(_Q1)[2]),_Q4=E(_Q2),_Q5=E(_Q4[1]),_Q6=B(_cW(_Q5[1],_Q5[2],_Q5[3],_Q4[2],_Q3[1],_Q3[2],_Q3[3],_9));return [0,E(_Q6[1]),_Q6[2]];})]);});},_PX,function(_Q7,_Q8,_Q9){return new F(function(){return A(_PY,[_PS,_Q8,new T(function(){var _Qa=E(E(_Q8)[2]),_Qb=E(_Q9),_Qc=E(_Qb[1]),_Qd=B(_cW(_Qc[1],_Qc[2],_Qc[3],_Qb[2],_Qa[1],_Qa[2],_Qa[3],_9));return [0,E(_Qd[1]),_Qd[2]];})]);});},_PZ);});},_Qe=[0,_PU,_Ps],_Qf=[1,_Qe,_9],_Qg=[1,_PQ,_Qf],_Qh=[1,_Qg,_Pr],_Qi=[0,_],_Qj=function(_Ok){return [4,_Qi,_Ok];},_Qk=[0,45],_Ql=[1,_Qk,_9],_Qm=function(_Qn,_Qo,_Qp,_Qq,_Qr){return new F(function(){return _OD(_kG,_Ql,_Qn,function(_Qs,_Qt,_Qu){return new F(function(){return A(_Qo,[_Qj,_Qt,new T(function(){var _Qv=E(E(_Qt)[2]),_Qw=E(_Qu),_Qx=E(_Qw[1]),_Qy=B(_cW(_Qx[1],_Qx[2],_Qx[3],_Qw[2],_Qv[1],_Qv[2],_Qv[3],_9));return [0,E(_Qy[1]),_Qy[2]];})]);});},_Qp,function(_Qz,_QA,_QB){return new F(function(){return A(_Qq,[_Qj,_QA,new T(function(){var _QC=E(E(_QA)[2]),_QD=E(_QB),_QE=E(_QD[1]),_QF=B(_cW(_QE[1],_QE[2],_QE[3],_QD[2],_QC[1],_QC[2],_QC[3],_9));return [0,E(_QF[1]),_QF[2]];})]);});},_Qr);});},_QG=[1,_Qm],_QH=[1,_QG,_9],_QI=[1,_QH,_Qh],_QJ=new T(function(){return B(unCStr("number"));}),_QK=[1,_QJ,_9],_QL=new T(function(){return B(err(_kL));}),_QM=new T(function(){return B(err(_kJ));}),_QN=new T(function(){return B(_us(_uO,_uf,_uU));}),_QO=function(_QP){return function(_QQ,_QR,_QS,_QT,_QU){return new F(function(){return A(_QT,[new T(function(){var _QV=B(_uZ(B(_kO(_QN,_QP))));return _QV[0]==0?E(_QM):E(_QV[2])[0]==0?E(_QV[1]):E(_QL);}),_QQ,new T(function(){return [0,E(E(_QQ)[2]),_9];})]);});};},_QW=function(_QX,_QY,_QZ,_R0,_R1){return new F(function(){return _dT(_ku,_QX,function(_R2,_R3,_R4){return new F(function(){return A(_QO,[_R2,_R3,_QY,_QZ,function(_R5,_R6,_R7){return new F(function(){return A(_QY,[_R5,_R6,new T(function(){return B(_dL(_R4,_R7));})]);});},function(_R8){return new F(function(){return A(_QZ,[new T(function(){return B(_dL(_R4,_R8));})]);});}]);});},_QZ,function(_R9,_Ra,_Rb){return new F(function(){return A(_QO,[_R9,_Ra,_QY,_QZ,function(_Rc,_Rd,_Re){return new F(function(){return A(_R0,[_Rc,_Rd,new T(function(){return B(_dL(_Rb,_Re));})]);});},function(_Rf){return new F(function(){return A(_R1,[new T(function(){return B(_dL(_Rb,_Rf));})]);});}]);});},_R1);});},_Rg=function(_Rh,_Ri,_Rj,_Rk,_Rl){return new F(function(){return _QW(_Rh,function(_Rm,_Rn,_Ro){return new F(function(){return A(_Ri,[[1,[0,_,_Rm]],_Rn,new T(function(){var _Rp=E(E(_Rn)[2]),_Rq=E(_Ro),_Rr=E(_Rq[1]),_Rs=B(_cW(_Rr[1],_Rr[2],_Rr[3],_Rq[2],_Rp[1],_Rp[2],_Rp[3],_9));return [0,E(_Rs[1]),_Rs[2]];})]);});},_Rj,function(_Rt,_Ru,_Rv){return new F(function(){return A(_Rk,[[1,[0,_,_Rt]],_Ru,new T(function(){var _Rw=E(E(_Ru)[2]),_Rx=_Rw[1],_Ry=_Rw[2],_Rz=_Rw[3],_RA=E(_Rv),_RB=E(_RA[1]),_RC=_RB[2],_RD=_RB[3],_RE=E(_RA[2]);if(!_RE[0]){switch(B(_cO(_RB[1],_Rx))){case 0:var _RF=[0,E(_Rw),_9];break;case 1:if(_RC>=_Ry){if(_RC!=_Ry){var _RG=[0,E(_RB),_9];}else{if(_RD>=_Rz){var _RH=_RD!=_Rz?[0,E(_RB),_9]:[0,E(_RB),_cV];}else{var _RH=[0,E(_Rw),_9];}var _RI=_RH,_RG=_RI;}var _RJ=_RG,_RK=_RJ;}else{var _RK=[0,E(_Rw),_9];}var _RL=_RK,_RF=_RL;break;default:var _RF=[0,E(_RB),_9];}var _RM=_RF;}else{var _RN=B(_jb(_RB,_RE,_QK)),_RO=E(_RN[1]),_RP=B(_cW(_RO[1],_RO[2],_RO[3],_RN[2],_Rx,_Ry,_Rz,_9)),_RM=[0,E(_RP[1]),_RP[2]];}var _RQ=_RM,_RR=_RQ,_RS=_RR,_RT=_RS;return _RT;})]);});},function(_RU){return new F(function(){return A(_Rl,[new T(function(){var _RV=E(_RU),_RW=B(_jb(_RV[1],_RV[2],_QK));return [0,E(_RW[1]),_RW[2]];})]);});});});},_RX=new T(function(){return B(unCStr("P_"));}),_RY=function(_RZ,_S0,_S1,_S2,_S3){return new F(function(){return _OD(_kG,_RX,_RZ,function(_S4,_S5,_S6){return new F(function(){return _Rg(_S5,_S0,_S1,function(_S7,_S8,_S9){return new F(function(){return A(_S0,[_S7,_S8,new T(function(){return B(_dL(_S6,_S9));})]);});},function(_Sa){return new F(function(){return A(_S1,[new T(function(){return B(_dL(_S6,_Sa));})]);});});});},_S1,function(_Sb,_Sc,_Sd){return new F(function(){return _Rg(_Sc,_S0,_S1,function(_Se,_Sf,_Sg){return new F(function(){return A(_S2,[_Se,_Sf,new T(function(){return B(_dL(_Sd,_Sg));})]);});},function(_Sh){return new F(function(){return A(_S3,[new T(function(){return B(_dL(_Sd,_Sh));})]);});});});},_S3);});},_Si=[0,41],_Sj=new T(function(){return B(_jN(_kG,_Si));}),_Sk=function(_Sl,_Sm,_Sn,_So,_Sp,_Sq){return new F(function(){return A(_Sj,[_Sm,function(_Sr,_Ss,_St){return new F(function(){return A(_Sn,[_Sl,_Ss,new T(function(){var _Su=E(E(_Ss)[2]),_Sv=E(_St),_Sw=E(_Sv[1]),_Sx=B(_cW(_Sw[1],_Sw[2],_Sw[3],_Sv[2],_Su[1],_Su[2],_Su[3],_9));return [0,E(_Sx[1]),_Sx[2]];})]);});},_So,function(_Sy,_Sz,_SA){return new F(function(){return A(_Sp,[_Sl,_Sz,new T(function(){var _SB=E(E(_Sz)[2]),_SC=E(_SA),_SD=E(_SC[1]),_SE=B(_cW(_SD[1],_SD[2],_SD[3],_SC[2],_SB[1],_SB[2],_SB[3],_9));return [0,E(_SE[1]),_SE[2]];})]);});},_Sq]);});},_SF=function(_SG,_SH,_SI,_SJ,_SK){return new F(function(){return A(_SL,[_SG,function(_SM,_SN,_SO){return new F(function(){return _Sk(_SM,_SN,_SH,_SI,function(_SP,_SQ,_SR){return new F(function(){return A(_SH,[_SP,_SQ,new T(function(){return B(_dL(_SO,_SR));})]);});},function(_SS){return new F(function(){return A(_SI,[new T(function(){return B(_dL(_SO,_SS));})]);});});});},_SI,function(_ST,_SU,_SV){return new F(function(){return _Sk(_ST,_SU,_SH,_SI,function(_SW,_SX,_SY){return new F(function(){return A(_SJ,[_SW,_SX,new T(function(){return B(_dL(_SV,_SY));})]);});},function(_SZ){return new F(function(){return A(_SK,[new T(function(){return B(_dL(_SV,_SZ));})]);});});});},_SK]);});},_T0=[0,40],_T1=new T(function(){return B(_jN(_kG,_T0));}),_T2=function(_T3,_T4,_T5,_T6,_T7){var _T8=function(_T9){return new F(function(){return _RY(_T3,_T4,_T5,function(_Ta,_Tb,_Tc){return new F(function(){return A(_T6,[_Ta,_Tb,new T(function(){return B(_dL(_T9,_Tc));})]);});},function(_Td){return new F(function(){return A(_T7,[new T(function(){return B(_dL(_T9,_Td));})]);});});});};return new F(function(){return A(_T1,[_T3,function(_Te,_Tf,_Tg){return new F(function(){return _SF(_Tf,_T4,_T5,function(_Th,_Ti,_Tj){return new F(function(){return A(_T4,[_Th,_Ti,new T(function(){return B(_dL(_Tg,_Tj));})]);});},function(_Tk){return new F(function(){return A(_T5,[new T(function(){return B(_dL(_Tg,_Tk));})]);});});});},_T5,function(_Tl,_Tm,_Tn){return new F(function(){return _SF(_Tm,_T4,_T5,function(_To,_Tp,_Tq){return new F(function(){return A(_T6,[_To,_Tp,new T(function(){return B(_dL(_Tn,_Tq));})]);});},function(_Tr){return new F(function(){return _T8(new T(function(){return B(_dL(_Tn,_Tr));}));});});});},_T8]);});},_SL=new T(function(){return B(_GN(_T2,_QI));}),_Ts=function(_Tt,_Tu,_Tv,_Tw,_Tx){return new F(function(){return A(_SL,[_Tt,function(_Ty,_Tz,_TA){return new F(function(){return _EX(_Ty,_Tz,_Tu,_Tv,function(_TB,_TC,_TD){return new F(function(){return A(_Tu,[_TB,_TC,new T(function(){return B(_dL(_TA,_TD));})]);});},function(_TE){return new F(function(){return A(_Tv,[new T(function(){return B(_dL(_TA,_TE));})]);});});});},_Tv,function(_TF,_TG,_TH){return new F(function(){return _EX(_TF,_TG,_Tu,_Tv,function(_TI,_TJ,_TK){return new F(function(){return A(_Tw,[_TI,_TJ,new T(function(){return B(_dL(_TH,_TK));})]);});},function(_TL){return new F(function(){return A(_Tx,[new T(function(){return B(_dL(_TH,_TL));})]);});});});},_Tx]);});},_TM=function(_TN,_TO,_TP,_TQ,_TR){return new F(function(){return _ew(_iS,_TN,function(_TS,_TT,_TU){return new F(function(){return _Ts(_TT,_TO,_TP,function(_TV,_TW,_TX){return new F(function(){return A(_TO,[_TV,_TW,new T(function(){return B(_dL(_TU,_TX));})]);});},function(_TY){return new F(function(){return A(_TP,[new T(function(){return B(_dL(_TU,_TY));})]);});});});},_TP,function(_TZ,_U0,_U1){return new F(function(){return _Ts(_U0,_TO,_TP,function(_U2,_U3,_U4){return new F(function(){return A(_TQ,[_U2,_U3,new T(function(){return B(_dL(_U1,_U4));})]);});},function(_U5){return new F(function(){return A(_TR,[new T(function(){return B(_dL(_U1,_U5));})]);});});});});});},_U6=function(_U7,_U8,_U9,_Ua,_Ub,_Uc,_Ud,_Ue){var _Uf=E(_U7);if(!_Uf[0]){return new F(function(){return A(_Ue,[[0,E([0,_U8,_U9,_Ua]),_gd]]);});}else{var _Ug=_Uf[1];if(!B(_86(_iy,_Ug,_xr))){return new F(function(){return A(_Ue,[[0,E([0,_U8,_U9,_Ua]),[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_Ug,_9],_gb));})])],_9]]]);});}else{var _Uh=function(_Ui,_Uj,_Uk,_Ul){var _Um=[0,E([0,_Ui,_Uj,_Uk]),_9],_Un=[0,E([0,_Ui,_Uj,_Uk]),_cV];return new F(function(){return _ew(_xY,[0,_Uf[2],E(_Ul),E(_Ub)],function(_Uo,_Up,_Uq){return new F(function(){return _TM(_Up,_Uc,_Ud,function(_Ur,_Us,_Ut){return new F(function(){return A(_Uc,[_Ur,_Us,new T(function(){return B(_dL(_Uq,_Ut));})]);});},function(_Uu){return new F(function(){return A(_Ud,[new T(function(){return B(_dL(_Uq,_Uu));})]);});});});},_Ud,function(_Uv,_Uw,_Ux){return new F(function(){return _TM(_Uw,_Uc,_Ud,function(_Uy,_Uz,_UA){return new F(function(){return A(_Uc,[_Uy,_Uz,new T(function(){var _UB=E(_Ux),_UC=E(_UB[1]),_UD=E(_UA),_UE=E(_UD[1]),_UF=B(_cW(_UC[1],_UC[2],_UC[3],_UB[2],_UE[1],_UE[2],_UE[3],_UD[2])),_UG=E(_UF[1]),_UH=_UG[2],_UI=_UG[3],_UJ=E(_UF[2]);if(!_UJ[0]){switch(B(_cO(_Ui,_UG[1]))){case 0:var _UK=[0,E(_UG),_9];break;case 1:if(_Uj>=_UH){if(_Uj!=_UH){var _UL=E(_Um);}else{if(_Uk>=_UI){var _UM=_Uk!=_UI?E(_Um):E(_Un);}else{var _UM=[0,E(_UG),_9];}var _UN=_UM,_UL=_UN;}var _UO=_UL,_UP=_UO;}else{var _UP=[0,E(_UG),_9];}var _UQ=_UP,_UK=_UQ;break;default:var _UK=E(_Um);}var _UR=_UK;}else{var _UR=[0,E(_UG),_UJ];}var _US=_UR,_UT=_US,_UU=_UT,_UV=_UU,_UW=_UV,_UX=_UW;return _UX;})]);});},function(_UY){return new F(function(){return A(_Ud,[new T(function(){var _UZ=E(_Ux),_V0=E(_UZ[1]),_V1=E(_UY),_V2=E(_V1[1]),_V3=B(_cW(_V0[1],_V0[2],_V0[3],_UZ[2],_V2[1],_V2[2],_V2[3],_V1[2])),_V4=E(_V3[1]),_V5=_V4[2],_V6=_V4[3],_V7=E(_V3[2]);if(!_V7[0]){switch(B(_cO(_Ui,_V4[1]))){case 0:var _V8=[0,E(_V4),_9];break;case 1:if(_Uj>=_V5){if(_Uj!=_V5){var _V9=E(_Um);}else{if(_Uk>=_V6){var _Va=_Uk!=_V6?E(_Um):E(_Un);}else{var _Va=[0,E(_V4),_9];}var _Vb=_Va,_V9=_Vb;}var _Vc=_V9,_Vd=_Vc;}else{var _Vd=[0,E(_V4),_9];}var _Ve=_Vd,_V8=_Ve;break;default:var _V8=E(_Um);}var _Vf=_V8;}else{var _Vf=[0,E(_V4),_V7];}var _Vg=_Vf,_Vh=_Vg,_Vi=_Vh,_Vj=_Vi,_Vk=_Vj,_Vl=_Vk;return _Vl;})]);});});});});});};switch(E(E(_Ug)[1])){case 9:var _Vm=(_Ua+8|0)-B(_ge(_Ua-1|0,8))|0;return new F(function(){return _Uh(_U8,_U9,_Vm,[0,_U8,_U9,_Vm]);});break;case 10:var _Vn=_U9+1|0;return new F(function(){return _Uh(_U8,_Vn,1,[0,_U8,_Vn,1]);});break;default:var _Vo=_Ua+1|0;return new F(function(){return _Uh(_U8,_U9,_Vo,[0,_U8,_U9,_Vo]);});}}}},_Vp=function(_Vq,_Vr,_Vs,_Vt,_Vu,_Vv){var _Vw=function(_Vx,_Vy,_Vz,_VA,_VB,_VC){var _VD=function(_VE){var _VF=[0,[1,[0,_Vq,_Vx,new T(function(){return B(_7X(_v6,_VE));})]],_9];return function(_VG,_VH,_VI,_VJ,_VK){return new F(function(){return A(_ke,[_VG,function(_VL,_VM,_VN){return new F(function(){return A(_VH,[_VF,_VM,new T(function(){var _VO=E(E(_VM)[2]),_VP=E(_VN),_VQ=E(_VP[1]),_VR=B(_cW(_VQ[1],_VQ[2],_VQ[3],_VP[2],_VO[1],_VO[2],_VO[3],_9));return [0,E(_VR[1]),_VR[2]];})]);});},_VK,function(_VS,_VT,_VU){return new F(function(){return A(_VJ,[_VF,_VT,new T(function(){var _VV=E(E(_VT)[2]),_VW=E(_VU),_VX=E(_VW[1]),_VY=B(_cW(_VX[1],_VX[2],_VX[3],_VW[2],_VV[1],_VV[2],_VV[3],_9));return [0,E(_VY[1]),_VY[2]];})]);});},_VK]);});};},_VZ=function(_W0,_W1,_W2,_W3,_W4){var _W5=function(_W6,_W7,_W8){return new F(function(){return A(_VD,[_W6,_W7,_W1,_W2,function(_W9,_Wa,_Wb){return new F(function(){return A(_W3,[_W9,_Wa,new T(function(){return B(_dL(_W8,_Wb));})]);});},function(_Wc){return new F(function(){return A(_W4,[new T(function(){return B(_dL(_W8,_Wc));})]);});}]);});},_Wd=function(_We){return new F(function(){return _W5(_9,_W0,new T(function(){var _Wf=E(E(_W0)[2]),_Wg=E(_We),_Wh=E(_Wg[1]),_Wi=B(_cW(_Wh[1],_Wh[2],_Wh[3],_Wg[2],_Wf[1],_Wf[2],_Wf[3],_9));return [0,E(_Wi[1]),_Wi[2]];}));});};return new F(function(){return _eW(_kA,_kI,_W0,function(_Wj,_Wk,_Wl){return new F(function(){return A(_VD,[_Wj,_Wk,_W1,_W2,function(_Wm,_Wn,_Wo){return new F(function(){return A(_W1,[_Wm,_Wn,new T(function(){return B(_dL(_Wl,_Wo));})]);});},function(_Wp){return new F(function(){return A(_W2,[new T(function(){return B(_dL(_Wl,_Wp));})]);});}]);});},_Wd,_W5,_Wd);});};return new F(function(){return _ew(_iS,_Vy,function(_Wq,_Wr,_Ws){return new F(function(){return _VZ(_Wr,_Vz,_VA,function(_Wt,_Wu,_Wv){return new F(function(){return A(_Vz,[_Wt,_Wu,new T(function(){return B(_dL(_Ws,_Wv));})]);});},function(_Ww){return new F(function(){return A(_VA,[new T(function(){return B(_dL(_Ws,_Ww));})]);});});});},_VA,function(_Wx,_Wy,_Wz){return new F(function(){return _VZ(_Wy,_Vz,_VA,function(_WA,_WB,_WC){return new F(function(){return A(_VB,[_WA,_WB,new T(function(){return B(_dL(_Wz,_WC));})]);});},function(_WD){return new F(function(){return A(_VC,[new T(function(){return B(_dL(_Wz,_WD));})]);});});});});});},_WE=function(_WF,_WG,_WH,_WI,_WJ){return new F(function(){return _dT(_wv,_WF,function(_WK,_WL,_WM){return new F(function(){return _Vw(_WK,_WL,_WG,_WH,function(_WN,_WO,_WP){return new F(function(){return A(_WG,[_WN,_WO,new T(function(){return B(_dL(_WM,_WP));})]);});},function(_WQ){return new F(function(){return A(_WH,[new T(function(){return B(_dL(_WM,_WQ));})]);});});});},_WJ,function(_WR,_WS,_WT){return new F(function(){return _Vw(_WR,_WS,_WG,_WH,function(_WU,_WV,_WW){return new F(function(){return A(_WI,[_WU,_WV,new T(function(){return B(_dL(_WT,_WW));})]);});},function(_WX){return new F(function(){return A(_WJ,[new T(function(){return B(_dL(_WT,_WX));})]);});});});},_WJ);});};return new F(function(){return _ew(_iS,_Vr,function(_WY,_WZ,_X0){return new F(function(){return _WE(_WZ,_Vs,_Vt,function(_X1,_X2,_X3){return new F(function(){return A(_Vs,[_X1,_X2,new T(function(){return B(_dL(_X0,_X3));})]);});},function(_X4){return new F(function(){return A(_Vt,[new T(function(){return B(_dL(_X0,_X4));})]);});});});},_Vt,function(_X5,_X6,_X7){return new F(function(){return _WE(_X6,_Vs,_Vt,function(_X8,_X9,_Xa){return new F(function(){return A(_Vu,[_X8,_X9,new T(function(){return B(_dL(_X7,_Xa));})]);});},function(_Xb){return new F(function(){return A(_Vv,[new T(function(){return B(_dL(_X7,_Xb));})]);});});});});});},_Xc=function(_Xd,_Xe,_Xf,_Xg,_Xh){return new F(function(){return A(_SL,[_Xd,function(_Xi,_Xj,_Xk){return new F(function(){return _Vp(_Xi,_Xj,_Xe,_Xf,function(_Xl,_Xm,_Xn){return new F(function(){return A(_Xe,[_Xl,_Xm,new T(function(){return B(_dL(_Xk,_Xn));})]);});},function(_Xo){return new F(function(){return A(_Xf,[new T(function(){return B(_dL(_Xk,_Xo));})]);});});});},_Xf,function(_Xp,_Xq,_Xr){return new F(function(){return _Vp(_Xp,_Xq,_Xe,_Xf,function(_Xs,_Xt,_Xu){return new F(function(){return A(_Xg,[_Xs,_Xt,new T(function(){return B(_dL(_Xr,_Xu));})]);});},function(_Xv){return new F(function(){return A(_Xh,[new T(function(){return B(_dL(_Xr,_Xv));})]);});});});},_Xh]);});},_Xw=function(_Xx,_Xy,_Xz,_XA,_XB){return new F(function(){return _Xc(_Xx,_Xy,_Xz,_XA,function(_XC){var _XD=E(_Xx),_XE=E(_XD[2]);return new F(function(){return _U6(_XD[1],_XE[1],_XE[2],_XE[3],_XD[3],_Xy,_Xz,function(_XF){return new F(function(){return A(_XB,[new T(function(){return B(_dL(_XC,_XF));})]);});});});});});},_Ev=function(_XG,_XH,_XI,_XJ,_XK){return new F(function(){return _dT(_Xw,_XG,function(_XL,_XM,_XN){return new F(function(){return _wX(_XL,_XM,_XH,function(_XO,_XP,_XQ){return new F(function(){return A(_XH,[_XO,_XP,new T(function(){return B(_dL(_XN,_XQ));})]);});});});},_XI,function(_XR,_XS,_XT){return new F(function(){return _wX(_XR,_XS,_XH,function(_XU,_XV,_XW){return new F(function(){return A(_XJ,[_XU,_XV,new T(function(){return B(_dL(_XT,_XW));})]);});});});},_XK);});},_XX=function(_XY,_XZ,_Y0){while(1){var _Y1=E(_XZ);if(!_Y1[0]){return E(_Y0)[0]==0?true:false;}else{var _Y2=E(_Y0);if(!_Y2[0]){return false;}else{if(!B(A(_84,[_XY,_Y1[1],_Y2[1]]))){return false;}else{_XZ=_Y1[2];_Y0=_Y2[2];continue;}}}}},_Y3=function(_Y4,_Y5,_Y6){var _Y7=E(_Y5),_Y8=E(_Y6);return !B(_XX(_Y4,_Y7[1],_Y8[1]))?true:!B(A(_84,[_Y4,_Y7[2],_Y8[2]]))?true:false;},_Y9=function(_Ya,_Yb,_Yc,_Yd,_Ye){return !B(_XX(_Ya,_Yb,_Yd))?false:B(A(_84,[_Ya,_Yc,_Ye]));},_Yf=function(_Yg,_Yh,_Yi){var _Yj=E(_Yh),_Yk=E(_Yi);return new F(function(){return _Y9(_Yg,_Yj[1],_Yj[2],_Yk[1],_Yk[2]);});},_Yl=function(_Ym){return [0,function(_Yn,_Yo){return new F(function(){return _Yf(_Ym,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _Y3(_Ym,_Yn,_Yo);});}];},_Yp=function(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy){return new F(function(){return _lv(B(_aA(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx)),B(_aA(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yy)));});},_Yz=function(_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI){return !B(_Yp(_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI))?true:false;},_YJ=function(_YK,_YL,_YM,_YN,_YO,_YP,_YQ){return [0,function(_bi,_bj){return new F(function(){return _Yp(_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _Yz(_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_bi,_bj);});}];},_YR=function(_YS,_YT,_YU){var _YV=E(_YT),_YW=E(_YU);return !B(_XX(_YS,_YV[1],_YW[1]))?true:!B(A(_84,[_YS,_YV[2],_YW[2]]))?true:false;},_YX=function(_YY,_YZ,_Z0){var _Z1=E(_YZ),_Z2=E(_Z0);return new F(function(){return _Y9(_YY,_Z1[1],_Z1[2],_Z2[1],_Z2[2]);});},_Z3=function(_Z4){return [0,function(_Yn,_Yo){return new F(function(){return _YX(_Z4,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _YR(_Z4,_Yn,_Yo);});}];},_Z5=function(_Z6,_Z7,_Z8){var _Z9=E(_Z6);switch(_Z9[0]){case 0:var _Za=E(_Z7);return _Za[0]==0?!B(_lv(_Z9[3],_Za[3]))?[0]:[1,_Z8]:[0];case 1:var _Zb=E(_Z7);return _Zb[0]==1?!B(_lv(_Z9[3],_Zb[3]))?[0]:[1,_Z8]:[0];case 2:var _Zc=E(_Z7);return _Zc[0]==2?!B(_lv(_Z9[3],_Zc[3]))?[0]:[1,_Z8]:[0];case 3:var _Zd=E(_Z7);return _Zd[0]==3?!B(_lv(_Z9[3],_Zd[3]))?[0]:[1,_Z8]:[0];case 4:var _Ze=E(_Z7);return _Ze[0]==4?!B(_lv(_Z9[3],_Ze[3]))?[0]:[1,_Z8]:[0];case 5:var _Zf=E(_Z7);return _Zf[0]==5?!B(_lv(_Z9[3],_Zf[3]))?[0]:[1,_Z8]:[0];case 6:var _Zg=E(_Z7);return _Zg[0]==6?!B(_lv(_Z9[3],_Zg[3]))?[0]:[1,_Z8]:[0];case 7:var _Zh=E(_Z7);return _Zh[0]==7?!B(_lv(_Z9[3],_Zh[3]))?[0]:[1,_Z8]:[0];case 8:var _Zi=E(_Z7);return _Zi[0]==8?!B(_lv(_Z9[3],_Zi[3]))?[0]:[1,_Z8]:[0];default:var _Zj=E(_Z7);return _Zj[0]==9?!B(_lv(_Z9[3],_Zj[3]))?[0]:[1,_Z8]:[0];}},_Zk=new T(function(){return B(_3B("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_Zl=function(_Zm,_Zn){return [3,_,_Zm,_Zn];},_Zo=function(_Zp,_Zq,_Zr){while(1){var _Zs=E(_Zr);if(!_Zs[0]){return [0];}else{var _Zt=E(_Zs[1]),_Zu=B(A(_Zp,[_Zq,_Zt[2],_Zt[3]]));if(!_Zu[0]){_Zr=_Zs[2];continue;}else{return E(_Zu);}}}},_Zv=function(_Zw,_Zx){while(1){var _Zy=(function(_Zz,_ZA){var _ZB=E(_ZA);switch(_ZB[0]){case 2:var _ZC=B(_Zo(_Z5,_ZB[2],_Zz));if(!_ZC[0]){return E(_ZB);}else{var _ZD=_Zz;_Zx=_ZC[1];_Zw=_ZD;return null;}break;case 4:var _ZE=_ZB[3],_ZF=B(_Zo(_Z5,_ZB[2],_Zz));if(!_ZF[0]){return E(_ZB);}else{var _ZG=E(_ZF[1]);switch(_ZG[0]){case 3:return E(_ZG[3])[0]==0?B(_Zl(_ZG[2],_ZE)):E(_ZB);case 4:if(!E(_ZG[3])[0]){var _ZD=_Zz;_Zx=[4,_,_ZG[2],_ZE];_Zw=_ZD;return null;}else{return E(_ZB);}break;default:return E(_ZB);}}break;case 6:var _ZH=_ZB[3],_ZI=_ZB[4],_ZJ=B(_Zo(_Z5,_ZB[2],_Zz));if(!_ZJ[0]){return E(_ZB);}else{var _ZK=E(_ZJ[1]);switch(_ZK[0]){case 5:if(!E(_ZK[3])[0]){if(!E(_ZK[4])[0]){var _ZD=_Zz;_Zx=[5,_,_ZK[2],_ZH,_ZI];_Zw=_ZD;return null;}else{return E(_ZB);}}else{return E(_ZB);}break;case 6:if(!E(_ZK[3])[0]){if(!E(_ZK[4])[0]){var _ZD=_Zz;_Zx=[6,_,_ZK[2],_ZH,_ZI];_Zw=_ZD;return null;}else{return E(_ZB);}}else{return E(_ZB);}break;default:return E(_ZB);}}break;case 7:return [7,_,_ZB[2],new T(function(){return B(_Zv(_Zz,_ZB[3]));})];case 8:var _ZL=_ZB[2],_ZM=_ZB[3],_ZN=B(_Zo(_Z5,_ZL,_Zz));if(!_ZN[0]){return [8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];}else{var _ZO=E(_ZN[1]);switch(_ZO[0]){case 7:return E(_ZO[3])[0]==0?[7,_,_ZO[2],new T(function(){return B(_Zv(_Zz,_ZM));})]:[8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];case 8:if(!E(_ZO[3])[0]){var _ZD=_Zz;_Zx=[8,_,_ZO[2],_ZM];_Zw=_ZD;return null;}else{return [8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];}break;default:return [8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];}}break;case 9:return [9,_,_ZB[2],new T(function(){return B(_Zv(_Zz,_ZB[3]));}),new T(function(){return B(_Zv(_Zz,_ZB[4]));})];case 10:var _ZP=_ZB[2],_ZQ=_ZB[3],_ZR=_ZB[4],_ZS=B(_Zo(_Z5,_ZP,_Zz));if(!_ZS[0]){return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}else{var _ZT=E(_ZS[1]);switch(_ZT[0]){case 9:return E(_ZT[3])[0]==0?E(_ZT[4])[0]==0?[9,_,_ZT[2],new T(function(){return B(_Zv(_Zz,B(_Zv(_Zz,_ZQ))));}),new T(function(){return B(_Zv(_Zz,B(_Zv(_Zz,_ZR))));})]:[10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})]:[10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];case 10:if(!E(_ZT[3])[0]){if(!E(_ZT[4])[0]){var _ZD=_Zz;_Zx=[10,_,_ZT[2],_ZQ,_ZR];_Zw=_ZD;return null;}else{return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}}else{return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}break;default:return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}}break;case 11:return [11,_,_ZB[2],function(_ZU){return new F(function(){return _Zv(_Zz,B(A(_ZB[3],[_ZU])));});}];case 12:var _ZV=_ZB[2],_ZW=_ZB[3],_ZX=B(_Zo(_Z5,_ZV,_Zz));if(!_ZX[0]){return [12,_,_ZV,function(_ZY){return new F(function(){return _Zv(_Zz,B(A(_ZW,[_ZY])));});}];}else{var _ZZ=E(_ZX[1]);switch(_ZZ[0]){case 11:return [11,_,_ZZ[2],function(_100){return new F(function(){return _Zv(_Zz,B(A(_ZW,[_100])));});}];case 12:var _ZD=_Zz;_Zx=[12,_,_ZZ[2],_ZW];_Zw=_ZD;return null;default:return [12,_,_ZV,function(_101){return new F(function(){return _Zv(_Zz,B(A(_ZW,[_101])));});}];}}break;default:return E(_ZB);}})(_Zw,_Zx);if(_Zy!=null){return _Zy;}}},_102=function(_103,_104){var _105=E(_104);if(!_105[0]){var _106=B(_Zo(_Z5,_105[1],_103));if(!_106[0]){return E(_105);}else{var _107=E(_106[1]);return _107[0]==0?E(_Zk):[1,new T(function(){return B(_7X(function(_108){return new F(function(){return _Zv(_103,_108);});},_107[1]));})];}}else{return [1,new T(function(){return B(_7X(function(_109){return new F(function(){return _Zv(_103,_109);});},_105[1]));})];}},_10a=function(_10b,_10c,_10d,_10e,_10f,_10g,_10h,_10i,_10j){var _10k=E(_10j);return [0,new T(function(){return B(_7X(function(_10l){return new F(function(){return _102(_10i,_10l);});},_10k[1]));}),new T(function(){return B(_102(_10i,_10k[2]));})];},_10m=function(_10n,_10o,_10p,_10q,_10r,_10s,_10t,_10u,_10v){var _10w=E(_10v);return [0,new T(function(){return B(_7X(function(_10x){return new F(function(){return _10a(_10n,_10o,_10p,_10q,_10r,_10s,_10t,_10u,_10x);});},_10w[1]));}),new T(function(){return B(_10a(_10n,_10o,_10p,_10q,_10r,_10s,_10t,_10u,_10w[2]));})];},_10y=function(_10z){return E(E(_10z)[1]);},_10A=function(_10B,_10C){var _10D=E(_10C);return new F(function(){return A(_10y,[_10D[1],E(_10B)[2],_10D[2]]);});},_10E=function(_10F,_10G,_10H){var _10I=E(_10H);if(!_10I[0]){return [0];}else{var _10J=_10I[1],_10K=_10I[2];return !B(A(_10F,[_10G,_10J]))?[1,_10J,new T(function(){return B(_10E(_10F,_10G,_10K));})]:E(_10K);}},_10L=function(_10M,_10N,_10O){while(1){var _10P=E(_10O);if(!_10P[0]){return false;}else{if(!B(A(_10M,[_10N,_10P[1]]))){_10O=_10P[2];continue;}else{return true;}}}},_10Q=function(_10R,_10S){var _10T=function(_10U,_10V){while(1){var _10W=(function(_10X,_10Y){var _10Z=E(_10X);if(!_10Z[0]){return [0];}else{var _110=_10Z[1],_111=_10Z[2];if(!B(_10L(_10R,_110,_10Y))){return [1,_110,new T(function(){return B(_10T(_111,[1,_110,_10Y]));})];}else{_10U=_111;var _112=_10Y;_10V=_112;return null;}}})(_10U,_10V);if(_10W!=null){return _10W;}}};return new F(function(){return _10T(_10S,_9);});},_113=function(_114,_115,_116){return new F(function(){return _e(_115,new T(function(){return B((function(_117,_118){while(1){var _119=E(_118);if(!_119[0]){return E(_117);}else{var _11a=B(_10E(_114,_119[1],_117));_118=_119[2];_117=_11a;continue;}}})(B(_10Q(_114,_116)),_115));},1));});},_11b=function(_11c,_11d){while(1){var _11e=(function(_11f,_11g){var _11h=E(_11g);switch(_11h[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_11f,_11h[2]],_9];case 3:var _11i=_11f;_11d=_11h[3];_11c=_11i;return null;case 4:return new F(function(){return _113(_10A,[1,[0,_11f,_11h[2]],_9],new T(function(){return B(_11b(_11f,_11h[3]));},1));});break;case 5:return new F(function(){return _113(_10A,B(_11b(_11f,_11h[3])),new T(function(){return B(_11b(_11f,_11h[4]));},1));});break;default:return new F(function(){return _113(_10A,B(_113(_10A,[1,[0,_11f,_11h[2]],_9],new T(function(){return B(_11b(_11f,_11h[3]));},1))),new T(function(){return B(_11b(_11f,_11h[4]));},1));});}})(_11c,_11d);if(_11e!=null){return _11e;}}},_11j=function(_11k,_11l,_11m,_11n){while(1){var _11o=(function(_11p,_11q,_11r,_11s){var _11t=E(_11s);switch(_11t[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_11p,_11t[2]],_9];case 3:return new F(function(){return _11b(_11p,_11t[3]);});break;case 4:return new F(function(){return _113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11b(_11p,_11t[3]));},1));});break;case 5:return new F(function(){return _113(_10A,B(_11b(_11p,_11t[3])),new T(function(){return B(_11b(_11p,_11t[4]));},1));});break;case 6:return new F(function(){return _113(_10A,B(_113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11b(_11p,_11t[3]));},1))),new T(function(){return B(_11b(_11p,_11t[4]));},1));});break;case 7:var _11u=_11p,_11v=_11q,_11w=_11r;_11n=_11t[3];_11k=_11u;_11l=_11v;_11m=_11w;return null;case 8:return new F(function(){return _113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11j(_11p,_11q,_11r,_11t[3]));},1));});break;case 9:return new F(function(){return _113(_10A,B(_11j(_11p,_11q,_11r,_11t[3])),new T(function(){return B(_11j(_11p,_11q,_11r,_11t[4]));},1));});break;case 10:return new F(function(){return _113(_10A,B(_113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11j(_11p,_11q,_11r,_11t[3]));},1))),new T(function(){return B(_11j(_11p,_11q,_11r,_11t[4]));},1));});break;case 11:var _11u=_11p,_11v=_11q,_11w=_11r;_11n=B(A(_11t[3],[_ae]));_11k=_11u;_11l=_11v;_11m=_11w;return null;default:return new F(function(){return _113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11j(_11p,_11q,_11r,B(A(_11t[3],[_ae]))));},1));});}})(_11k,_11l,_11m,_11n);if(_11o!=null){return _11o;}}},_11x=function(_11y,_11z,_11A,_11B,_11C){var _11D=function(_11E){return new F(function(){return _11j(_11y,_11z,_11A,_11E);});};return new F(function(){return _e(B(_7r(B(_7X(function(_11F){var _11G=E(_11F);if(!_11G[0]){return [1,[0,_11y,_11G[1]],_9];}else{return new F(function(){return _7r(B(_7X(_11D,_11G[1])));});}},_11B)))),new T(function(){var _11H=E(_11C);if(!_11H[0]){var _11I=[1,[0,_11y,_11H[1]],_9];}else{var _11I=B(_7r(B(_7X(_11D,_11H[1]))));}return _11I;},1));});},_11J=function(_11K,_11L,_11M,_11N,_11O,_11P,_11Q,_11R,_11S){var _11T=E(_11S);return new F(function(){return _e(B(_7r(B(_7X(function(_11U){var _11V=E(_11U);return new F(function(){return _11x(_11K,_11O,_11P,_11V[1],_11V[2]);});},_11T[1])))),new T(function(){var _11W=E(_11T[2]);return B(_11x(_11K,_11O,_11P,_11W[1],_11W[2]));},1));});},_11X=function(_11Y,_11Z,_120,_121,_122,_123,_124,_125,_126,_127,_128){return [0,_11Y,_11Z,_120,_121,function(_10x){return new F(function(){return _11J(_11Y,_122,_123,_124,_125,_126,_127,_128,_10x);});},function(_129,_10x){return new F(function(){return _10m(_122,_123,_124,_125,_126,_127,_128,_129,_10x);});}];},_12a=function(_12b){return E(E(_12b)[2]);},_12c=function(_12d){return E(E(_12d)[1]);},_12e=[0,_12c,_12a],_12f=[0,125],_12g=new T(function(){return B(unCStr("given = "));}),_12h=new T(function(){return B(unCStr(", "));}),_12i=new T(function(){return B(unCStr("needed = "));}),_12j=new T(function(){return B(unCStr("AbsRule {"));}),_12k=[0,0],_12l=function(_12m){return E(E(_12m)[3]);},_12n=function(_12o){return E(E(_12o)[1]);},_12p=function(_12q,_12r,_12s,_12t){var _12u=function(_12v){return new F(function(){return _e(_12j,new T(function(){return B(_e(_12i,new T(function(){return B(A(new T(function(){return B(A(_12l,[_12q,_12s]));}),[new T(function(){return B(_e(_12h,new T(function(){return B(_e(_12g,new T(function(){return B(A(new T(function(){return B(A(_12n,[_12q,_12k,_12t]));}),[[1,_12f,_12v]]));},1)));},1)));})]));},1)));},1));});};return _12r<11?E(_12u):function(_12w){return [1,_E,new T(function(){return B(_12u([1,_D,_12w]));})];};},_12x=function(_12y,_12z){var _12A=E(_12z);return new F(function(){return A(_12p,[_12y,0,_12A[1],_12A[2],_9]);});},_12B=function(_12C,_12D,_12E){return new F(function(){return _2T(function(_12F){var _12G=E(_12F);return new F(function(){return _12p(_12C,0,_12G[1],_12G[2]);});},_12D,_12E);});},_12H=function(_12I,_12J,_12K){var _12L=E(_12K);return new F(function(){return _12p(_12I,E(_12J)[1],_12L[1],_12L[2]);});},_12M=function(_12N){return [0,function(_Yn,_Yo){return new F(function(){return _12H(_12N,_Yn,_Yo);});},function(_Yo){return new F(function(){return _12x(_12N,_Yo);});},function(_Yn,_Yo){return new F(function(){return _12B(_12N,_Yn,_Yo);});}];},_12O=new T(function(){return B(unCStr("Sequent "));}),_12P=[0,11],_12Q=[0,32],_12R=function(_12S,_12T,_12U,_12V){var _12W=new T(function(){return B(A(_12n,[_12S,_12P,_12V]));}),_12X=new T(function(){return B(A(_12l,[_12S,_12U]));});return _12T<11?function(_12Y){return new F(function(){return _e(_12O,new T(function(){return B(A(_12X,[[1,_12Q,new T(function(){return B(A(_12W,[_12Y]));})]]));},1));});}:function(_12Z){return [1,_E,new T(function(){return B(_e(_12O,new T(function(){return B(A(_12X,[[1,_12Q,new T(function(){return B(A(_12W,[[1,_D,_12Z]]));})]]));},1)));})];};},_130=function(_131,_132){var _133=E(_132);return new F(function(){return A(_12R,[_131,0,_133[1],_133[2],_9]);});},_134=function(_135,_136,_137){return new F(function(){return _2T(function(_138){var _139=E(_138);return new F(function(){return _12R(_135,0,_139[1],_139[2]);});},_136,_137);});},_13a=function(_13b,_13c,_13d){var _13e=E(_13d);return new F(function(){return _12R(_13b,E(_13c)[1],_13e[1],_13e[2]);});},_13f=function(_13g){return [0,function(_Yn,_Yo){return new F(function(){return _13a(_13g,_Yn,_Yo);});},function(_Yo){return new F(function(){return _130(_13g,_Yo);});},function(_Yn,_Yo){return new F(function(){return _134(_13g,_Yn,_Yo);});}];},_13h=function(_13i,_13j){return new F(function(){return _e(B(_a1(_13i)),_13j);});},_13k=function(_13l,_13m){return new F(function(){return _2T(_13h,_13l,_13m);});},_13n=function(_13o,_13p,_13q){return new F(function(){return _e(B(_a1(_13p)),_13q);});},_13r=[0,_13n,_a1,_13k],_13s=function(_13t,_13u,_13v,_13w,_13x,_13y,_13z,_13A,_13B,_13C,_13D,_13E){var _13F=E(_13E);return new F(function(){return _11x(_13t,_13A,_13B,_13F[1],_13F[2]);});},_13G=function(_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_13R){return [0,_13H,_13I,_13J,_13K,function(_10x){return new F(function(){return _13s(_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_13R,_10x);});},function(_129,_10x){return new F(function(){return _10a(_13L,_13M,_13N,_13O,_13P,_13Q,_13R,_129,_10x);});}];},_13S=function(_13T,_13U){return [0];},_13V=function(_13W,_13X,_13Y,_13Z,_140,_141,_142,_143,_144,_145,_146,_147,_148,_149){return [0,_13W,_13X,_13S,_1];},_14a=function(_14b,_14c,_14d,_14e,_14f,_14g,_14h,_14i,_14j,_14k,_14l,_14m){var _14n=E(_14m);if(!_14n[0]){return [1,[0,_14b,_14n[1]],_9];}else{return new F(function(){return _7r(B(_7X(function(_14o){return new F(function(){return _11j(_14b,_14i,_14j,_14o);});},_14n[1])));});}},_14p=function(_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A){return [0,_14q,_14r,_14s,_14t,function(_10x){return new F(function(){return _14a(_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A,_10x);});},_102];},_14B=new T(function(){return B(_CX("w_szUi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv azyl} [tv] quant{tv azyj} [tv]"));}),_14C=new T(function(){return B(_CX("w_szUh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv azyj} [tv]"));}),_14D=new T(function(){return B(_CX("w_szUg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv azyi} [tv]"));}),_14E=new T(function(){return B(_CX("w_szUf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv azyl} [tv]"));}),_14F=new T(function(){return B(_CX("w_szUe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv azyh} [tv]"));}),_14G=new T(function(){return B(_CX("w_szUd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv azyk} [tv]"));}),_14H=new T(function(){return B(_CX("w_szUj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv azyl} [tv]"));}),_14I=new T(function(){return B(_CX("w_szUc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv azyj} [tv]"));}),_14J=new T(function(){return B(_CX("w_szUb{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv azyi} [tv]"));}),_14K=new T(function(){return B(_CX("w_szUa{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv azyl} [tv]"));}),_14L=new T(function(){return B(_CX("w_szU9{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv azyh} [tv]"));}),_14M=new T(function(){return B(_CX("w_szU8{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv azyk} [tv]"));}),_14N=function(_14O,_14P){return function(_14Q,_14R){var _14S=E(_14Q);return _14S[0]==0?[1,[0,new T(function(){return B(_14T(_14O,_14P,_14M,_14L,_14K,_14J,_14I,_14G,_14F,_14E,_14D,_14C,_14B,_14H));}),_14S[1],_14R]]:[0];};},_14U=function(_14V){return [0,E(_14V)];},_14T=function(_14W,_14X,_14Y,_14Z,_150,_151,_152,_153,_154,_155,_156,_157,_158,_159){return [0,_14W,_14X,new T(function(){return B(_14N(_14W,_14X));}),_14U];},_15a=[1,_9],_15b=function(_15c,_15d){while(1){var _15e=E(_15c);if(!_15e[0]){return E(_15d);}else{_15c=_15e[2];var _15f=_15d+1|0;_15d=_15f;continue;}}},_15g=[0,95],_15h=[1,_15g,_9],_15i=[1,_15h,_9],_15j=function(_15k,_15l,_15m){return !B(_lv(B(A(_15k,[_15l,_15i])),B(A(_15k,[_15m,_15i]))))?true:false;},_15n=function(_15o){return [0,function(_15p,_15q){return new F(function(){return _lv(B(A(_15o,[_15p,_15i])),B(A(_15o,[_15q,_15i])));});},function(_bi,_bj){return new F(function(){return _15j(_15o,_bi,_bj);});}];},_15r=function(_15s,_15t){return new F(function(){return _Zv(_15s,_15t);});},_15u=function(_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F){return [0,_15v,_15w,_15x,_15y,function(_15G){return new F(function(){return _11j(_15v,_15C,_15D,_15G);});},_15r];},_15H=new T(function(){return B(_CX("w_soVl{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv alSl} [tv] quant{tv alSj} [tv]"));}),_15I=new T(function(){return B(_CX("w_soVk{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv alSj} [tv]"));}),_15J=new T(function(){return B(_CX("w_soVj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv alSi} [tv]"));}),_15K=new T(function(){return B(_CX("w_soVi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv alSl} [tv]"));}),_15L=new T(function(){return B(_CX("w_soVh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv alSh} [tv]"));}),_15M=new T(function(){return B(_CX("w_soVg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv alSk} [tv]"));}),_15N=new T(function(){return B(_CX("w_soVm{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv alSl} [tv]"));}),_15O=new T(function(){return B(_CX("w_soVf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv alSj} [tv]"));}),_15P=new T(function(){return B(_CX("w_soVe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv alSi} [tv]"));}),_15Q=new T(function(){return B(_CX("w_soVd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv alSl} [tv]"));}),_15R=new T(function(){return B(_CX("w_soVc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv alSh} [tv]"));}),_15S=new T(function(){return B(_CX("w_soVb{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv alSk} [tv]"));}),_15T=function(_15U,_15V,_15W,_15X){var _15Y=E(_15W);switch(_15Y[0]){case 2:return [1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_15Y[2],_15X]];case 4:var _160=_15Y[2];if(!E(_15Y[3])[0]){var _161=E(_15X);switch(_161[0]){case 3:return E(_161[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_160,_161]]:[0];case 4:return E(_161[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_160,_161]]:[0];default:return [0];}}else{return [0];}break;case 6:var _162=_15Y[2];if(!E(_15Y[3])[0]){if(!E(_15Y[4])[0]){var _163=E(_15X);switch(_163[0]){case 5:return E(_163[3])[0]==0?E(_163[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_162,_163]]:[0]:[0];case 6:return E(_163[3])[0]==0?E(_163[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_162,_163]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _164=_15Y[2];if(!E(_15Y[3])[0]){var _165=E(_15X);switch(_165[0]){case 7:return E(_165[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_164,_165]]:[0];case 8:return E(_165[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_164,_165]]:[0];default:return [0];}}else{return [0];}break;case 10:var _166=_15Y[2];if(!E(_15Y[3])[0]){if(!E(_15Y[4])[0]){var _167=E(_15X);switch(_167[0]){case 9:return E(_167[3])[0]==0?E(_167[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_166,_167]]:[0]:[0];case 10:return E(_167[3])[0]==0?E(_167[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_166,_167]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_168=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_169=function(_16a){var _16b=E(_16a);switch(_16b[0]){case 3:return [2,_,_16b];case 4:return [4,_,_16b,_V];case 5:return [6,_,_16b,_V,_V];case 6:return [8,_,_16b,_S];case 7:return [10,_,_16b,_S,_S];default:return E(_168);}},_15Z=function(_16c,_16d,_16e,_16f,_16g,_16h,_16i,_16j,_16k,_16l,_16m,_16n,_16o,_16p){return [0,_16c,_16d,function(_16q,_16r){return new F(function(){return _15T(_16c,_16d,_16q,_16r);});},_169];},_16s=function(_16t,_16u,_16v){return new F(function(){return _2T(function(_16w,_16x){return new F(function(){return _e(B(A(_16t,[_16w,_15i])),_16x);});},_16u,_16v);});},_16y=function(_16z){return [0,function(_16A,_16B,_16C){return new F(function(){return _e(B(A(_16z,[_16B,_15i])),_16C);});},function(_16D){return new F(function(){return A(_16z,[_16D,_15i]);});},function(_bi,_bj){return new F(function(){return _16s(_16z,_bi,_bj);});}];},_16E=[1,_9],_16F=function(_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_16Q,_16R){var _16S=E(_16Q);if(_16S[0]==2){return E(_16E);}else{var _16T=E(_16R);if(_16T[0]==2){return E(_16E);}else{var _16U=function(_16V){var _16W=function(_16X){var _16Y=function(_16Z){var _170=function(_171){var _172=function(_173){var _174=function(_175){var _176=function(_177){var _178=function(_179){var _17a=function(_17b){var _17c=function(_17d){var _17e=function(_17f){var _17g=function(_17h){var _17i=E(_16S);switch(_17i[0]){case 1:var _17j=E(_16T);return _17j[0]==1?!B(A(_16H,[_17i[2],_17j[2]]))?[0]:E(_16E):[0];case 3:var _17k=E(_16T);return _17k[0]==3?!B(A(_16G,[_17i[2],_17k[2]]))?[0]:E(_16E):[0];case 4:var _17l=_17i[2],_17m=E(_16T);switch(_17m[0]){case 3:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[4,_,_17l,_V],[3,_,_17m[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[4,_,_17l,_V],[4,_,_17m[2],_V]]));}),_9]];default:return [0];}break;case 5:var _17o=E(_16T);return _17o[0]==5?!B(A(_16G,[_17i[2],_17o[2]]))?[0]:E(_16E):[0];case 6:var _17p=_17i[2],_17q=E(_16T);switch(_17q[0]){case 5:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[6,_,_17p,_V,_V],[5,_,_17q[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[6,_,_17p,_V,_V],[6,_,_17q[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _17r=E(_16T);return _17r[0]==7?!B(A(_16I,[_17i[2],_17r[2]]))?[0]:[1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17i[3],_17r[3]]));}),_9]]:[0];case 8:var _17s=_17i[2],_17t=_17i[3],_17u=E(_16T);switch(_17u[0]){case 7:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[8,_,_17s,_S],[7,_,_17u[2],_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17t,_17u[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[8,_,_17s,_S],[8,_,_17u[2],_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17t,_17u[3]]));}),_9]]];default:return [0];}break;case 9:var _17v=E(_16T);return _17v[0]==9?!B(A(_16I,[_17i[2],_17v[2]]))?[0]:[1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17i[3],_17v[3]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17i[4],_17v[4]]));}),_9]]]:[0];case 10:var _17w=_17i[2],_17x=_17i[3],_17y=_17i[4],_17z=function(_17A){var _17B=E(_16T);switch(_17B[0]){case 9:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[10,_,_17w,_S,_S],[9,_,_17B[2],_S,_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17x,_17B[3]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17y,_17B[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[10,_,_17w,_S,_S],[10,_,_17B[2],_S,_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17x,_17B[3]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17y,_17B[4]]));}),_9]]]];default:return [0];}};return E(_17x)[0]==0?E(_17y)[0]==0?E(_16E):B(_17z(_)):B(_17z(_));default:return [0];}},_17C=E(_16T);return _17C[0]==10?E(_17C[3])[0]==0?E(_17C[4])[0]==0?E(_16E):B(_17g(_)):B(_17g(_)):B(_17g(_));},_17D=E(_16S);return _17D[0]==8?E(_17D[3])[0]==0?E(_16E):B(_17e(_)):B(_17e(_));},_17E=E(_16T);switch(_17E[0]){case 6:return E(_17E[3])[0]==0?E(_17E[4])[0]==0?E(_16E):B(_17c(_)):B(_17c(_));case 8:return E(_17E[3])[0]==0?E(_16E):B(_17c(_));default:return new F(function(){return _17c(_);});}},_17F=E(_16S);return _17F[0]==6?E(_17F[3])[0]==0?E(_17F[4])[0]==0?E(_16E):B(_17a(_)):B(_17a(_)):B(_17a(_));},_17G=E(_16T);return _17G[0]==4?E(_17G[3])[0]==0?E(_16E):B(_178(_)):B(_178(_));},_17H=E(_16S);switch(_17H[0]){case 4:return E(_17H[3])[0]==0?E(_16E):B(_176(_));case 9:return E(_17H[3])[0]==0?E(_17H[4])[0]==0?E(_16E):B(_176(_)):B(_176(_));default:return new F(function(){return _176(_);});}},_17I=E(_16T);return _17I[0]==9?E(_17I[3])[0]==0?E(_17I[4])[0]==0?E(_16E):B(_174(_)):B(_174(_)):B(_174(_));},_17J=E(_16S);return _17J[0]==7?E(_17J[3])[0]==0?E(_16E):B(_172(_)):B(_172(_));},_17K=E(_16T);switch(_17K[0]){case 5:return E(_17K[3])[0]==0?E(_17K[4])[0]==0?E(_16E):B(_170(_)):B(_170(_));case 7:return E(_17K[3])[0]==0?E(_16E):B(_170(_));default:return new F(function(){return _170(_);});}},_17L=E(_16S);return _17L[0]==5?E(_17L[3])[0]==0?E(_17L[4])[0]==0?E(_16E):B(_16Y(_)):B(_16Y(_)):B(_16Y(_));},_17M=E(_16T);return _17M[0]==3?E(_17M[3])[0]==0?E(_16E):B(_16W(_)):B(_16W(_));},_17N=E(_16S);return _17N[0]==3?E(_17N[3])[0]==0?E(_16E):B(_16U(_)):B(_16U(_));}}},_17O=function(_17P,_17Q,_17R){return [0,_17P,_17Q,_17R];},_17S=new T(function(){return B(_CX("w_soVu{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv alRG} [tv]"));}),_17T=new T(function(){return B(_CX("w_soVq{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv alRH} [tv]"));}),_17U=function(_17V){return [0,function(_17W,_17X){return B(A(_17V,[_17W,_17X,_1]))[0]==0?false:true;},function(_17Y,_17Z){return B(A(_17V,[_17Y,_17Z,_1]))[0]==0?true:false;}];},_180=new T(function(){return B(_17U(_Z5));}),_17n=function(_181,_182,_183,_184,_185,_186,_187,_188,_189,_18a){var _18b=function(_18c,_18d){return new F(function(){return _af(_185,_187,_188,_186,_184,_189,_18a,_18c);});};return function(_mc,_18e){return new F(function(){return _17O(new T(function(){return B(_15Z(function(_18f,_18g){return new F(function(){return _16F(_181,_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18f,_18g);});},new T(function(){return B(_15u(_180,_13r,new T(function(){return B(_15n(_18b));}),new T(function(){return B(_16y(_18b));}),_185,_187,_188,_184,_186,_189,_18a));}),_17T,_181,_182,_183,_17S,_184,_185,_186,_187,_188,_189,_18a));}),_mc,_18e);});};},_18h=function(_18i,_18j,_18k){var _18l=E(_18j);if(!_18l[0]){return [0];}else{var _18m=E(_18k);return _18m[0]==0?[0]:[1,new T(function(){return B(A(_18i,[_18l[1],_18m[1]]));}),new T(function(){return B(_18h(_18i,_18l[2],_18m[2]));})];}},_18n=function(_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x,_18y,_18z){var _18A=E(_18y);if(!_18A[0]){return E(_15a);}else{var _18B=_18A[1],_18C=E(_18z);if(!_18C[0]){return E(_15a);}else{var _18D=_18C[1];return B(_15b(_18B,0))!=B(_15b(_18D,0))?[0]:[1,new T(function(){return B(_18h(new T(function(){return B(_17n(_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x));}),_18B,_18D));})];}}},_18E=new T(function(){return B(_CX("w_szV3{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv azy1} [tv]"));}),_18F=new T(function(){return B(_CX("w_szV7{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv azy0} [tv]"));}),_18G=new T(function(){return B(_17U(_Z5));}),_18H=function(_18I,_18J,_18K,_18L,_18M,_18N,_18O,_18P,_18Q,_18R){var _18S=new T(function(){return B(_14T(function(_18T,_18U){return new F(function(){return _18n(_18I,_18J,_18K,_18L,_18M,_18N,_18O,_18P,_18Q,_18R,_18T,_18U);});},new T(function(){return B(_14p(_18G,_13r,new T(function(){return B(_YJ(_18M,_18O,_18P,_18L,_18N,_18Q,_18R));}),new T(function(){return B(_b9(_18M,_18O,_18P,_18L,_18N,_18Q,_18R));}),_18M,_18O,_18P,_18L,_18N,_18Q,_18R));}),_18E,_18I,_18J,_18K,_18F,_18L,_18M,_18N,_18O,_18P,_18Q,_18R));});return function(_18V,_18W){var _18X=E(_18V),_18Y=_18X[1],_18Z=E(_18W),_190=_18Z[1];return B(_15b(_18Y,0))!=B(_15b(_190,0))?[0]:[1,[1,[0,_18S,_18X[2],_18Z[2]],new T(function(){return B(_18h(function(_129,_10x){return [0,_18S,_129,_10x];},_18Y,_190));})]];};},_191=new T(function(){return B(_CX("w_szXF{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv azxy} [tv]"));}),_192=new T(function(){return B(_CX("w_szXJ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv azxx} [tv]"));}),_193=function(_194,_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d){var _19e=new T(function(){return B(_13V(new T(function(){return B(_18H(_194,_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d));}),new T(function(){return B(_13G(_18G,_13r,new T(function(){return B(_Z3(new T(function(){return B(_YJ(_198,_19a,_19b,_197,_199,_19c,_19d));})));}),new T(function(){return B(_13f(new T(function(){return B(_b9(_198,_19a,_19b,_197,_199,_19c,_19d));})));}),_198,_19a,_19b,_197,_199,_19c,_19d));}),_191,_194,_195,_196,_192,_197,_198,_199,_19a,_19b,_19c,_19d));});return function(_19f,_19g){var _19h=E(_19f),_19i=_19h[1],_19j=E(_19g),_19k=_19j[1];return B(_15b(_19i,0))!=B(_15b(_19k,0))?[0]:[1,[1,[0,_19e,_19h[2],_19j[2]],new T(function(){return B(_18h(function(_129,_10x){return [0,_19e,_129,_10x];},_19i,_19k));})]];};},_19l=function(_19m,_19n){while(1){var _19o=E(_19n);if(!_19o[0]){return false;}else{var _19p=E(_19o[1]);if(!B(A(_10y,[_19p[1],_19m,_19p[2]]))){_19n=_19o[2];continue;}else{return true;}}}},_19q=[0,_9],_19r=function(_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_19C){var _19D=E(_19v);return !B(A(_19D[1],[new T(function(){return B(A(_19A,[_19B]));}),_19C]))?!B(_19l(_19B,B(A(_19x,[_19C]))))?[0,[1,[0,[0,_19s,[0,_19t,_19u,_19D,_19w,_19x,_19y],_19z,_19A],_19B,_19C],_9]]:[1,[1,_,[0,_19s,[0,_19t,_19u,_19D,_19w,_19x,_19y],_19z,_19A],[3,_19u,_19w,_19B,_19C]]]:E(_19q);},_19E=function(_19F){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(54,15)-(56,42)|case");});},_19G=new T(function(){return B(_19E(_));}),_19H=new T(function(){return B(unCStr(": empty list"));}),_19I=new T(function(){return B(unCStr("Prelude."));}),_19J=function(_19K){return new F(function(){return err(B(_e(_19I,new T(function(){return B(_e(_19K,_19H));},1))));});},_19L=new T(function(){return B(unCStr("head"));}),_19M=new T(function(){return B(_19J(_19L));}),_19N=function(_19O){return E(E(_19O)[2]);},_19P=function(_19Q,_19R){while(1){var _19S=E(_19Q);if(!_19S){return E(_19R);}else{var _19T=E(_19R);if(!_19T[0]){return [0];}else{_19Q=_19S-1|0;_19R=_19T[2];continue;}}}},_19U=function(_19V,_19W){var _19X=E(_19V)[1];return _19X>=0?B(_19P(_19X,_19W)):E(_19W);},_19Y=function(_19Z){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:96:31-64|function conc");});},_1a0=new T(function(){return B(_19Y(_));}),_1a1=function(_1a2){var _1a3=E(_1a2);switch(_1a3[0]){case 3:return [2,_,_1a3];case 4:return [4,_,_1a3,_V];case 5:return [6,_,_1a3,_V,_V];case 6:return [8,_,_1a3,_S];case 7:return [10,_,_1a3,_S,_S];default:return E(_168);}},_1a4=function(_1a5){var _1a6=E(_1a5);if(!_1a6[0]){return [0];}else{var _1a7=E(_1a6[1]);if(!_1a7[0]){return [0];}else{return new F(function(){return _e(_1a7[1],new T(function(){return B(_1a4(_1a6[2]));},1));});}}},_1a8=function(_1a9){var _1aa=E(_1a9);return [0,[1,[1,new T(function(){return B(_1a4(_1aa[1]));})],_9],_1aa[2]];},_1ab=function(_1ac,_1ad,_1ae){return !B(_86(_1ac,_1ad,_1ae))?E(_1ae):[1,_1ad,new T(function(){return B(_7u(function(_1af){return !B(A(_84,[_1ac,_1af,_1ad]))?true:false;},_1ae));})];},_1ag=function(_1ah,_1ai,_1aj,_1ak,_1al,_1am,_1an){return function(_1ao,_1ap){var _1aq=E(_1ao);if(!_1aq[0]){return new F(function(){return _1a8(_1ap);});}else{var _1ar=E(_1ap);return [0,[1,[1,new T(function(){return B(_1ab(new T(function(){return B(_15n(function(_1as,_1at){return new F(function(){return _af(_1an,_1am,_1al,_1aj,_1ak,_1ah,_1ai,_1as);});}));}),_1aq[1],B(_1a4(_1ar[1]))));})],_9],_1ar[2]];}};},_1au=new T(function(){return B(_17U(_Z5));}),_1av=function(_1aw){return E(E(_1aw)[1]);},_1ax=function(_1ay,_1az){var _1aA=E(_1ay);if(!_1aA){return [0];}else{var _1aB=E(_1az);return _1aB[0]==0?[0]:[1,_1aB[1],new T(function(){return B(_1ax(_1aA-1|0,_1aB[2]));})];}},_1aC=function(_1aD,_1aE){return _1aD<0?[0]:B(_1ax(_1aD,_1aE));},_1aF=function(_1aG,_1aH){var _1aI=E(_1aG)[1];return _1aI>0?B(_1aC(_1aI,_1aH)):[0];},_1aJ=function(_1aK,_1aL){return [1,_,_1aK,_1aL];},_1aM=function(_1aN){return E(E(_1aN)[2]);},_1aO=function(_1aP){return E(E(_1aP)[4]);},_1aQ=function(_1aR,_1aS,_1aT){var _1aU=E(_1aR),_1aV=E(_1aU[2]);return new F(function(){return _19r(_1aU[1],_1aV[1],_1aV[2],_1aV[3],_1aV[4],_1aV[5],_1aV[6],_1aU[3],_1aU[4],_1aS,_1aT);});},_1aW=function(_1aX,_1aY,_1aZ,_1b0,_1b1,_1b2){var _1b3=B(A(_1aZ,[_1b1,_1b2]));if(!_1b3[0]){var _1b4=B(A(_1aZ,[_1b2,_1b1]));if(!_1b4[0]){var _1b5=B(A(_1aX,[_1b1,_1b2]));if(!_1b5[0]){return [1,[0,new T(function(){return B(_1aO(_1aY));}),_1b1,_1b2]];}else{var _1b6=B(_1b7([0,_1aX,_1aY,_1aZ,_1b0],_1b5[1]));return _1b6[0]==0?E(_1b6):[1,[2,new T(function(){return B(_1aO(_1aY));}),_1b6[1],_1b1,_1b2]];}}else{var _1b8=E(_1b4[1]);return new F(function(){return _1aQ(_1b8[1],_1b8[2],_1b8[3]);});}}else{var _1b9=E(_1b3[1]);return new F(function(){return _1aQ(_1b9[1],_1b9[2],_1b9[3]);});}},_1ba=function(_1bb){return E(E(_1bb)[6]);},_1b7=function(_1bc,_1bd){var _1be=E(_1bd);if(!_1be[0]){return E(_19q);}else{var _1bf=E(_1be[1]),_1bg=E(_1bf[1]),_1bh=B(_1aW(_1bg[1],_1bg[2],_1bg[3],_1bg[4],_1bf[2],_1bf[3]));if(!_1bh[0]){var _1bi=_1bh[1],_1bj=B(_1b7(_1bc,B(_7X(function(_1bk){var _1bl=E(_1bk),_1bm=_1bl[1];return [0,_1bm,new T(function(){return B(A(_1ba,[B(_1aM(_1bm)),_1bi,_1bl[2]]));}),new T(function(){return B(A(_1ba,[B(_1aM(_1bm)),_1bi,_1bl[3]]));})];},_1be[2]))));if(!_1bj[0]){var _1bn=_1bj[1];return [0,new T(function(){var _1bo=function(_1bp){var _1bq=E(_1bp);return _1bq[0]==0?E(_1bn):[1,new T(function(){var _1br=E(_1bq[1]),_1bs=_1br[1];return [0,_1bs,_1br[2],new T(function(){return B(A(_1ba,[B(_1aM(_1bs)),_1bn,_1br[3]]));})];}),new T(function(){return B(_1bo(_1bq[2]));})];};return B(_1bo(_1bi));})];}else{return [1,new T(function(){return B(_1aJ(_1bc,_1bj[1]));})];}}else{return [1,[1,_,_1bg,_1bh[1]]];}}},_1bt=function(_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA,_1bB,_1bC,_1bD,_1bE,_1bF){var _1bG=new T(function(){return B(_19N(_1bF));}),_1bH=function(_1bI,_1bJ){return new F(function(){return _af(_1bA,_1bz,_1by,_1bw,_1bx,_1bu,_1bv,_1bI);});},_1bK=new T(function(){return B(_15u(_1au,_13r,new T(function(){return B(_15n(_1bH));}),new T(function(){return B(_16y(_1bH));}),_1bA,_1bz,_1by,_1bx,_1bw,_1bu,_1bv));}),_1bL=function(_1bM,_1bN){return new F(function(){return _16F(_1bE,_1bC,_1bD,_1bx,_1bA,_1bw,_1bz,_1by,_1bu,_1bv,_1bM,_1bN);});};return function(_1bO,_1bP,_1bQ){var _1bR=new T(function(){return B(A(_1bB,[_1bQ]));});return [0,new T(function(){return B(_18h(function(_1bS,_1bT){var _1bU=B(A(new T(function(){return B(_1ag(_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA));}),[new T(function(){var _1bV=E(E(_1bT)[1]);if(!_1bV[0]){var _1bW=[0];}else{var _1bX=E(_1bV[1]),_1bW=_1bX[0]==0?[0]:[1,new T(function(){var _1bY=E(_1bX[1]);return _1bY[0]==0?E(_19M):B(_Zv(new T(function(){var _1bZ=E(B(A(_1bG,[_1bO]))[2]);if(!_1bZ[0]){var _1c0=E(_1a0);}else{var _1c1=E(_1bZ[1]);if(!_1c1[0]){var _1c2=E(_1a0);}else{var _1c3=_1c1[1];if(!E(_1c1[2])[0]){var _1c4=B(_15T(_1bL,_1bK,_1c3,_1bR));if(!_1c4[0]){var _1c5=B(_15T(_1bL,_1bK,_1bR,_1c3));if(!_1c5[0]){var _1c6=B(_1bL(_1c3,_1bR));if(!_1c6[0]){var _1c7=[0];}else{var _1c8=B(_1b7([0,_1bL,_1bK,function(_1c9,_1ca){return new F(function(){return _15T(_1bL,_1bK,_1c9,_1ca);});},_1a1],_1c6[1])),_1c7=_1c8[0]==0?E(_1c8[1]):[0];}var _1cb=_1c7;}else{var _1cc=E(_1c5[1]),_1cd=E(_1cc[1]),_1ce=E(_1cd[2]),_1cf=B(_19r(_1cd[1],_1ce[1],_1ce[2],_1ce[3],_1ce[4],_1ce[5],_1ce[6],_1cd[3],_1cd[4],_1cc[2],_1cc[3])),_1cb=_1cf[0]==0?E(_1cf[1]):[0];}var _1cg=_1cb;}else{var _1ch=E(_1c4[1]),_1ci=E(_1ch[1]),_1cj=E(_1ci[2]),_1ck=B(_19r(_1ci[1],_1cj[1],_1cj[2],_1cj[3],_1cj[4],_1cj[5],_1cj[6],_1ci[3],_1ci[4],_1ch[2],_1ch[3])),_1cg=_1ck[0]==0?E(_1ck[1]):[0];}var _1cl=_1cg;}else{var _1cl=E(_1a0);}var _1c2=_1cl;}var _1c0=_1c2;}var _1cm=_1c0;return _1cm;}),_1bY[1]));})];}var _1cn=_1bW;return _1cn;}),_1bS])),_1co=_1bU[2],_1cp=E(E(_1bT)[1]);if(!_1cp[0]){return E(_19G);}else{var _1cq=E(_1cp[1]);if(!_1cq[0]){return E(_1cp[2])[0]==0?E(_1bU):E(_19G);}else{var _1cr=E(_1bU[1]);if(!_1cr[0]){return [0,_9,_1co];}else{var _1cs=E(_1cr[1]);if(!_1cs[0]){return E(_1bU);}else{var _1ct=_1cs[1],_1cu=new T(function(){return [0,B(_15b(_1cq[1],0))];});return [0,[1,[1,new T(function(){return B(_1aF(_1cu,_1ct));})],[1,[1,new T(function(){return B(_19U(_1cu,_1ct));})],_1cr[2]]],_1co];}}}}},_1bP,new T(function(){return B(A(new T(function(){return B(_1av(_1bF));}),[_1bO]));},1)));}),[0,new T(function(){return E(B(A(_1bG,[_1bO]))[1]);}),[1,[1,_1bR,_9]]]];};},_1cv=function(_1cw,_1cx){return [0];},_1cy=function(_1cz,_1cA,_1cB,_1cC,_1cD,_1cE,_1cF,_1cG,_1cH,_1cI,_1cJ){var _1cK=new T(function(){return B(_1bt(_1cz,_1cA,_1cB,_1cC,_1cD,_1cE,_1cF,_1cG,_1cH,_1cI,_1cJ,_12e));}),_1cL=new T(function(){return B(_193(_1cJ,_1cH,_1cI,_1cC,_1cF,_1cB,_1cE,_1cD,_1cz,_1cA));}),_1cM=[0,_1cL,new T(function(){return B(_11X(_1au,_13r,new T(function(){return B(_Yl(new T(function(){return B(_Z3(new T(function(){return B(_YJ(_1cF,_1cE,_1cD,_1cC,_1cB,_1cz,_1cA));})));})));}),new T(function(){return B(_12M(new T(function(){return B(_13f(new T(function(){return B(_b9(_1cF,_1cE,_1cD,_1cC,_1cB,_1cz,_1cA));})));})));}),_1cF,_1cE,_1cD,_1cC,_1cB,_1cz,_1cA));}),_1cv,_1];return function(_1cN,_1cO,_1cP){var _1cQ=B(_7u(function(_1cR){var _1cS=B(A(_1cL,[new T(function(){return B(A(_1cK,[_1cR,_1cO,_1cP]));}),_1cR]));return _1cS[0]==0?false:B(_1b7(_1cM,_1cS[1]))[0]==0?true:false;},E(_1cN)[1]));if(!_1cQ[0]){return [0];}else{var _1cT=_1cQ[1],_1cU=new T(function(){return B(A(_1cK,[_1cT,_1cO,_1cP]));}),_1cV=B(A(_1cL,[_1cT,_1cU]));if(!_1cV[0]){return [0];}else{var _1cW=B(_1b7(_1cM,_1cV[1]));if(!_1cW[0]){var _1cX=_1cW[1];return [1,new T(function(){var _1cY=E(E(_1cU)[2]);return [0,new T(function(){return B(_7X(function(_1cZ){return new F(function(){return _102(_1cX,_1cZ);});},_1cY[1]));}),new T(function(){return B(_102(_1cX,_1cY[2]));})];})];}else{return [0];}}}};},_1d0=[1],_1d1=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1d2=function(_1d3){return new F(function(){return err(_1d1);});},_1d4=new T(function(){return B(_1d2(_));}),_1d5=function(_1d6,_1d7,_1d8){var _1d9=E(_1d8);if(!_1d9[0]){var _1da=_1d9[1],_1db=E(_1d7);if(!_1db[0]){var _1dc=_1db[1],_1dd=_1db[2];if(_1dc<=(imul(3,_1da)|0)){return [0,(1+_1dc|0)+_1da|0,E(E(_1d6)),E(_1db),E(_1d9)];}else{var _1de=E(_1db[3]);if(!_1de[0]){var _1df=_1de[1],_1dg=E(_1db[4]);if(!_1dg[0]){var _1dh=_1dg[1],_1di=_1dg[2],_1dj=_1dg[3];if(_1dh>=(imul(2,_1df)|0)){var _1dk=function(_1dl){var _1dm=E(_1dg[4]);return _1dm[0]==0?[0,(1+_1dc|0)+_1da|0,E(_1di),E([0,(1+_1df|0)+_1dl|0,E(_1dd),E(_1de),E(_1dj)]),E([0,(1+_1da|0)+_1dm[1]|0,E(E(_1d6)),E(_1dm),E(_1d9)])]:[0,(1+_1dc|0)+_1da|0,E(_1di),E([0,(1+_1df|0)+_1dl|0,E(_1dd),E(_1de),E(_1dj)]),E([0,1+_1da|0,E(E(_1d6)),E(_1d0),E(_1d9)])];},_1dn=E(_1dj);return _1dn[0]==0?B(_1dk(_1dn[1])):B(_1dk(0));}else{return [0,(1+_1dc|0)+_1da|0,E(_1dd),E(_1de),E([0,(1+_1da|0)+_1dh|0,E(E(_1d6)),E(_1dg),E(_1d9)])];}}else{return E(_1d4);}}else{return E(_1d4);}}}else{return [0,1+_1da|0,E(E(_1d6)),E(_1d0),E(_1d9)];}}else{var _1do=E(_1d7);if(!_1do[0]){var _1dp=_1do[1],_1dq=_1do[2],_1dr=_1do[4],_1ds=E(_1do[3]);if(!_1ds[0]){var _1dt=_1ds[1],_1du=E(_1dr);if(!_1du[0]){var _1dv=_1du[1],_1dw=_1du[2],_1dx=_1du[3];if(_1dv>=(imul(2,_1dt)|0)){var _1dy=function(_1dz){var _1dA=E(_1du[4]);return _1dA[0]==0?[0,1+_1dp|0,E(_1dw),E([0,(1+_1dt|0)+_1dz|0,E(_1dq),E(_1ds),E(_1dx)]),E([0,1+_1dA[1]|0,E(E(_1d6)),E(_1dA),E(_1d0)])]:[0,1+_1dp|0,E(_1dw),E([0,(1+_1dt|0)+_1dz|0,E(_1dq),E(_1ds),E(_1dx)]),E([0,1,E(E(_1d6)),E(_1d0),E(_1d0)])];},_1dB=E(_1dx);return _1dB[0]==0?B(_1dy(_1dB[1])):B(_1dy(0));}else{return [0,1+_1dp|0,E(_1dq),E(_1ds),E([0,1+_1dv|0,E(E(_1d6)),E(_1du),E(_1d0)])];}}else{return [0,3,E(_1dq),E(_1ds),E([0,1,E(E(_1d6)),E(_1d0),E(_1d0)])];}}else{var _1dC=E(_1dr);return _1dC[0]==0?[0,3,E(_1dC[2]),E([0,1,E(_1dq),E(_1d0),E(_1d0)]),E([0,1,E(E(_1d6)),E(_1d0),E(_1d0)])]:[0,2,E(E(_1d6)),E(_1do),E(_1d0)];}}else{return [0,1,E(E(_1d6)),E(_1d0),E(_1d0)];}}},_1dD=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_1dE=function(_1dF){return new F(function(){return err(_1dD);});},_1dG=new T(function(){return B(_1dE(_));}),_1dH=function(_1dI,_1dJ,_1dK){var _1dL=E(_1dJ);if(!_1dL[0]){var _1dM=_1dL[1],_1dN=E(_1dK);if(!_1dN[0]){var _1dO=_1dN[1],_1dP=_1dN[2];if(_1dO<=(imul(3,_1dM)|0)){return [0,(1+_1dM|0)+_1dO|0,E(E(_1dI)),E(_1dL),E(_1dN)];}else{var _1dQ=E(_1dN[3]);if(!_1dQ[0]){var _1dR=_1dQ[1],_1dS=_1dQ[2],_1dT=_1dQ[3],_1dU=E(_1dN[4]);if(!_1dU[0]){var _1dV=_1dU[1];if(_1dR>=(imul(2,_1dV)|0)){var _1dW=function(_1dX){var _1dY=E(_1dI),_1dZ=E(_1dQ[4]);return _1dZ[0]==0?[0,(1+_1dM|0)+_1dO|0,E(_1dS),E([0,(1+_1dM|0)+_1dX|0,E(_1dY),E(_1dL),E(_1dT)]),E([0,(1+_1dV|0)+_1dZ[1]|0,E(_1dP),E(_1dZ),E(_1dU)])]:[0,(1+_1dM|0)+_1dO|0,E(_1dS),E([0,(1+_1dM|0)+_1dX|0,E(_1dY),E(_1dL),E(_1dT)]),E([0,1+_1dV|0,E(_1dP),E(_1d0),E(_1dU)])];},_1e0=E(_1dT);return _1e0[0]==0?B(_1dW(_1e0[1])):B(_1dW(0));}else{return [0,(1+_1dM|0)+_1dO|0,E(_1dP),E([0,(1+_1dM|0)+_1dR|0,E(E(_1dI)),E(_1dL),E(_1dQ)]),E(_1dU)];}}else{return E(_1dG);}}else{return E(_1dG);}}}else{return [0,1+_1dM|0,E(E(_1dI)),E(_1dL),E(_1d0)];}}else{var _1e1=E(_1dK);if(!_1e1[0]){var _1e2=_1e1[1],_1e3=_1e1[2],_1e4=_1e1[4],_1e5=E(_1e1[3]);if(!_1e5[0]){var _1e6=_1e5[1],_1e7=_1e5[2],_1e8=_1e5[3],_1e9=E(_1e4);if(!_1e9[0]){var _1ea=_1e9[1];if(_1e6>=(imul(2,_1ea)|0)){var _1eb=function(_1ec){var _1ed=E(_1dI),_1ee=E(_1e5[4]);return _1ee[0]==0?[0,1+_1e2|0,E(_1e7),E([0,1+_1ec|0,E(_1ed),E(_1d0),E(_1e8)]),E([0,(1+_1ea|0)+_1ee[1]|0,E(_1e3),E(_1ee),E(_1e9)])]:[0,1+_1e2|0,E(_1e7),E([0,1+_1ec|0,E(_1ed),E(_1d0),E(_1e8)]),E([0,1+_1ea|0,E(_1e3),E(_1d0),E(_1e9)])];},_1ef=E(_1e8);return _1ef[0]==0?B(_1eb(_1ef[1])):B(_1eb(0));}else{return [0,1+_1e2|0,E(_1e3),E([0,1+_1e6|0,E(E(_1dI)),E(_1d0),E(_1e5)]),E(_1e9)];}}else{return [0,3,E(_1e7),E([0,1,E(E(_1dI)),E(_1d0),E(_1d0)]),E([0,1,E(_1e3),E(_1d0),E(_1d0)])];}}else{var _1eg=E(_1e4);return _1eg[0]==0?[0,3,E(_1e3),E([0,1,E(E(_1dI)),E(_1d0),E(_1d0)]),E(_1eg)]:[0,2,E(E(_1dI)),E(_1d0),E(_1e1)];}}else{return [0,1,E(E(_1dI)),E(_1d0),E(_1d0)];}}},_1eh=function(_1ei){return [0,1,E(E(_1ei)),E(_1d0),E(_1d0)];},_1ej=function(_1ek,_1el){var _1em=E(_1el);if(!_1em[0]){return new F(function(){return _1d5(_1em[2],B(_1ej(_1ek,_1em[3])),_1em[4]);});}else{return new F(function(){return _1eh(_1ek);});}},_1en=function(_1eo,_1ep){var _1eq=E(_1ep);if(!_1eq[0]){return new F(function(){return _1dH(_1eq[2],_1eq[3],B(_1en(_1eo,_1eq[4])));});}else{return new F(function(){return _1eh(_1eo);});}},_1er=function(_1es,_1et,_1eu,_1ev,_1ew){return new F(function(){return _1dH(_1eu,_1ev,B(_1en(_1es,_1ew)));});},_1ex=function(_1ey,_1ez,_1eA,_1eB,_1eC){return new F(function(){return _1d5(_1eA,B(_1ej(_1ey,_1eB)),_1eC);});},_1eD=function(_1eE,_1eF,_1eG,_1eH,_1eI,_1eJ){var _1eK=E(_1eF);if(!_1eK[0]){var _1eL=_1eK[1],_1eM=_1eK[2],_1eN=_1eK[3],_1eO=_1eK[4];if((imul(3,_1eL)|0)>=_1eG){if((imul(3,_1eG)|0)>=_1eL){return [0,(_1eL+_1eG|0)+1|0,E(E(_1eE)),E(_1eK),E([0,_1eG,E(_1eH),E(_1eI),E(_1eJ)])];}else{return new F(function(){return _1dH(_1eM,_1eN,B(_1eD(_1eE,_1eO,_1eG,_1eH,_1eI,_1eJ)));});}}else{return new F(function(){return _1d5(_1eH,B(_1eP(_1eE,_1eL,_1eM,_1eN,_1eO,_1eI)),_1eJ);});}}else{return new F(function(){return _1ex(_1eE,_1eG,_1eH,_1eI,_1eJ);});}},_1eP=function(_1eQ,_1eR,_1eS,_1eT,_1eU,_1eV){var _1eW=E(_1eV);if(!_1eW[0]){var _1eX=_1eW[1],_1eY=_1eW[2],_1eZ=_1eW[3],_1f0=_1eW[4];if((imul(3,_1eR)|0)>=_1eX){if((imul(3,_1eX)|0)>=_1eR){return [0,(_1eR+_1eX|0)+1|0,E(E(_1eQ)),E([0,_1eR,E(_1eS),E(_1eT),E(_1eU)]),E(_1eW)];}else{return new F(function(){return _1dH(_1eS,_1eT,B(_1eD(_1eQ,_1eU,_1eX,_1eY,_1eZ,_1f0)));});}}else{return new F(function(){return _1d5(_1eY,B(_1eP(_1eQ,_1eR,_1eS,_1eT,_1eU,_1eZ)),_1f0);});}}else{return new F(function(){return _1er(_1eQ,_1eR,_1eS,_1eT,_1eU);});}},_1f1=function(_1f2,_1f3,_1f4){var _1f5=E(_1f3);if(!_1f5[0]){var _1f6=_1f5[1],_1f7=_1f5[2],_1f8=_1f5[3],_1f9=_1f5[4],_1fa=E(_1f4);if(!_1fa[0]){var _1fb=_1fa[1],_1fc=_1fa[2],_1fd=_1fa[3],_1fe=_1fa[4];if((imul(3,_1f6)|0)>=_1fb){if((imul(3,_1fb)|0)>=_1f6){return [0,(_1f6+_1fb|0)+1|0,E(E(_1f2)),E(_1f5),E(_1fa)];}else{return new F(function(){return _1dH(_1f7,_1f8,B(_1eD(_1f2,_1f9,_1fb,_1fc,_1fd,_1fe)));});}}else{return new F(function(){return _1d5(_1fc,B(_1eP(_1f2,_1f6,_1f7,_1f8,_1f9,_1fd)),_1fe);});}}else{return new F(function(){return _1er(_1f2,_1f6,_1f7,_1f8,_1f9);});}}else{return new F(function(){return _1ej(_1f2,_1f4);});}},_1ff=function(_1fg,_1fh,_1fi,_1fj){var _1fk=E(_1fj);if(!_1fk[0]){var _1fl=new T(function(){var _1fm=B(_1ff(_1fk[1],_1fk[2],_1fk[3],_1fk[4]));return [0,_1fm[1],_1fm[2]];});return [0,new T(function(){return E(E(_1fl)[1]);}),new T(function(){return B(_1d5(_1fh,_1fi,E(_1fl)[2]));})];}else{return [0,_1fh,_1fi];}},_1fn=function(_1fo,_1fp,_1fq,_1fr){var _1fs=E(_1fq);if(!_1fs[0]){var _1ft=new T(function(){var _1fu=B(_1fn(_1fs[1],_1fs[2],_1fs[3],_1fs[4]));return [0,_1fu[1],_1fu[2]];});return [0,new T(function(){return E(E(_1ft)[1]);}),new T(function(){return B(_1dH(_1fp,E(_1ft)[2],_1fr));})];}else{return [0,_1fp,_1fr];}},_1fv=function(_1fw,_1fx){var _1fy=E(_1fw);if(!_1fy[0]){var _1fz=_1fy[1],_1fA=E(_1fx);if(!_1fA[0]){var _1fB=_1fA[1];if(_1fz<=_1fB){var _1fC=B(_1fn(_1fB,_1fA[2],_1fA[3],_1fA[4]));return new F(function(){return _1d5(_1fC[1],_1fy,_1fC[2]);});}else{var _1fD=B(_1ff(_1fz,_1fy[2],_1fy[3],_1fy[4]));return new F(function(){return _1dH(_1fD[1],_1fD[2],_1fA);});}}else{return E(_1fy);}}else{return E(_1fx);}},_1fE=function(_1fF,_1fG,_1fH,_1fI,_1fJ){var _1fK=E(_1fF);if(!_1fK[0]){var _1fL=_1fK[1],_1fM=_1fK[2],_1fN=_1fK[3],_1fO=_1fK[4];if((imul(3,_1fL)|0)>=_1fG){if((imul(3,_1fG)|0)>=_1fL){return new F(function(){return _1fv(_1fK,[0,_1fG,E(_1fH),E(_1fI),E(_1fJ)]);});}else{return new F(function(){return _1dH(_1fM,_1fN,B(_1fE(_1fO,_1fG,_1fH,_1fI,_1fJ)));});}}else{return new F(function(){return _1d5(_1fH,B(_1fP(_1fL,_1fM,_1fN,_1fO,_1fI)),_1fJ);});}}else{return [0,_1fG,E(_1fH),E(_1fI),E(_1fJ)];}},_1fP=function(_1fQ,_1fR,_1fS,_1fT,_1fU){var _1fV=E(_1fU);if(!_1fV[0]){var _1fW=_1fV[1],_1fX=_1fV[2],_1fY=_1fV[3],_1fZ=_1fV[4];if((imul(3,_1fQ)|0)>=_1fW){if((imul(3,_1fW)|0)>=_1fQ){return new F(function(){return _1fv([0,_1fQ,E(_1fR),E(_1fS),E(_1fT)],_1fV);});}else{return new F(function(){return _1dH(_1fR,_1fS,B(_1fE(_1fT,_1fW,_1fX,_1fY,_1fZ)));});}}else{return new F(function(){return _1d5(_1fX,B(_1fP(_1fQ,_1fR,_1fS,_1fT,_1fY)),_1fZ);});}}else{return [0,_1fQ,E(_1fR),E(_1fS),E(_1fT)];}},_1g0=function(_1g1,_1g2){var _1g3=E(_1g1);if(!_1g3[0]){var _1g4=_1g3[1],_1g5=_1g3[2],_1g6=_1g3[3],_1g7=_1g3[4],_1g8=E(_1g2);if(!_1g8[0]){var _1g9=_1g8[1],_1ga=_1g8[2],_1gb=_1g8[3],_1gc=_1g8[4];if((imul(3,_1g4)|0)>=_1g9){if((imul(3,_1g9)|0)>=_1g4){return new F(function(){return _1fv(_1g3,_1g8);});}else{return new F(function(){return _1dH(_1g5,_1g6,B(_1fE(_1g7,_1g9,_1ga,_1gb,_1gc)));});}}else{return new F(function(){return _1d5(_1ga,B(_1fP(_1g4,_1g5,_1g6,_1g7,_1gb)),_1gc);});}}else{return E(_1g3);}}else{return E(_1g2);}},_1gd=function(_1ge,_1gf){var _1gg=E(_1gf);if(!_1gg[0]){var _1gh=_1gg[2],_1gi=_1gg[3],_1gj=_1gg[4];if(!B(A(_1ge,[_1gh]))){return new F(function(){return _1g0(B(_1gd(_1ge,_1gi)),B(_1gd(_1ge,_1gj)));});}else{return new F(function(){return _1f1(_1gh,B(_1gd(_1ge,_1gi)),B(_1gd(_1ge,_1gj)));});}}else{return [1];}},_1gk=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_1gl=new T(function(){return B(err(_1gk));}),_1gm=function(_1gn,_1go,_1gp,_1gq){while(1){var _1gr=E(_1gp);if(!_1gr[0]){_1gn=_1gr[1];_1go=_1gr[2];_1gp=_1gr[3];_1gq=_1gr[4];continue;}else{return E(_1go);}}},_1gs=function(_1gt,_1gu){var _1gv=B(_1gd(function(_1gw){return new F(function(){return _lv(E(_1gw)[2],_1gt);});},_1gu));if(!_1gv[0]){var _1gx=E(_1gv[3]);return _1gx[0]==0?B(_1gm(_1gx[1],_1gx[2],_1gx[3],_1gx[4])):E(_1gv[2]);}else{return E(_1gl);}},_1gy=[1,_9],_1gz=function(_1gA,_1gB,_1gC,_1gD,_1gE,_1gF,_1gG,_1gH,_1gI,_1gJ,_1gK,_1gL,_1gM,_1gN){var _1gO=E(_1gN);if(!_1gO[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_1gH,[_1gM]));}),_9]],_9],[1,[1,new T(function(){return B(A(_1gH,[_1gM]));}),_9]]]];}else{var _1gP=function(_1gQ){var _1gR=E(_1gQ);if(!_1gR[0]){return E(_1gy);}else{var _1gS=E(_1gR[1]),_1gT=B(_1gz(_1gA,_1gB,_1gC,_1gD,_1gE,_1gF,_1gG,_1gH,_1gI,_1gJ,_1gK,_1gL,_1gS[1],_1gS[2]));if(!_1gT[0]){return [0];}else{var _1gU=B(_1gP(_1gR[2]));return _1gU[0]==0?[0]:[1,[1,_1gT[1],_1gU[1]]];}}},_1gV=B(_1gP(_1gO[2]));return _1gV[0]==0?[0]:B(A(_1cy,[_1gA,_1gB,_1gC,_1gD,_1gE,_1gF,_1gG,_1gH,_1gI,_1gJ,_1gK,new T(function(){return B(_1gs(_1gO[1],_1gL));}),_1gV[1],_1gM]));}},_1gW=function(_1gX,_1gY,_1gZ,_1h0,_1h1,_1h2,_1h3,_1h4,_1h5,_1h6,_1h7,_1h8,_1h9,_1ha,_1hb){var _1hc=E(_1hb);return new F(function(){return _1gz(_1gX,_1gY,_1gZ,_1h0,_1h1,_1h2,_1h3,_1h4,_1h5,_1h8,_1h9,_1ha,_1hc[1],_1hc[2]);});},_1hd=function(_1he){return new F(function(){return _db(_1he,_9);});},_1hf=function(_1hg,_1hh){return _1hg<=B(_15b(_1hh,0))?[1,new T(function(){var _1hi=_1hg-1|0;if(_1hi>=0){var _1hj=B(_gp(B(_1hd(_1hh)),_1hi));}else{var _1hj=E(_gm);}var _1hk=_1hj,_1hl=_1hk;return _1hl;})]:[0];},_1hm=function(_1hn,_1ho,_1hp){var _1hq=function(_1hr){return _1hr<=B(_15b(_1hp,0))?[1,[0,new T(function(){var _1hs=_1hn-1|0;if(_1hs>=0){var _1ht=B(_gp(B(_1hd(_1hp)),_1hs));}else{var _1ht=E(_gm);}var _1hu=_1ht,_1hv=_1hu;return _1hv;}),new T(function(){var _1hw=_1ho-1|0;if(_1hw>=0){var _1hx=B(_gp(B(_1hd(_1hp)),_1hw));}else{var _1hx=E(_gm);}var _1hy=_1hx,_1hz=_1hy;return _1hz;})]]:[0];};return _1hn>_1ho?B(_1hq(_1hn)):B(_1hq(_1ho));},_1hA=[0],_1hB=new T(function(){return B(unCStr("depends on unjustified lines"));}),_1hC=new T(function(){return B(unCStr("unavailable lines"));}),_1hD=new T(function(){return B(unCStr("wrong number of premises"));}),_1hE=new T(function(){return B(unCStr("Impossible Error 1"));}),_1hF=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1hG=new T(function(){return B(unCStr("PR"));}),_1hH=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1hI=function(_1hJ,_1hK,_1hL,_1hM,_1hN,_1hO){var _1hP=function(_1hQ){var _1hR=B(A(_1hM,[_1hK]));if(!_1hR[0]){return [0,[1,_1hH,_1hN],[1,_28,_1hO]];}else{var _1hS=E(_1hR[1]);if(!_1hS[0]){switch(E(E(_1hS[1])[1])){case 1:var _1hT=E(_1hL);if(!_1hT[0]){return [0,[1,_1hD,_1hN],[1,_28,_1hO]];}else{if(!E(_1hT[2])[0]){var _1hU=B(_1hf(E(_1hT[1])[1],_1hO));if(!_1hU[0]){return [0,[1,_1hC,_1hN],[1,_28,_1hO]];}else{var _1hV=E(_1hU[1]);return _1hV[0]==0?[0,[1,_1hB,_1hN],[1,_28,_1hO]]:[0,[1,_9,_1hN],[1,[1,[0,_1hJ,[1,_1hK,[1,_1hV[1],_9]]]],_1hO]];}}else{return [0,[1,_1hD,_1hN],[1,_28,_1hO]];}}break;case 2:var _1hW=E(_1hL);if(!_1hW[0]){return [0,[1,_1hD,_1hN],[1,_28,_1hO]];}else{var _1hX=E(_1hW[2]);if(!_1hX[0]){return [0,[1,_1hD,_1hN],[1,_28,_1hO]];}else{if(!E(_1hX[2])[0]){var _1hY=B(_1hm(E(_1hW[1])[1],E(_1hX[1])[1],_1hO));if(!_1hY[0]){return [0,[1,_1hC,_1hN],[1,_28,_1hO]];}else{var _1hZ=E(_1hY[1]),_1i0=E(_1hZ[1]);if(!_1i0[0]){return [0,[1,_1hB,_1hN],[1,_28,_1hO]];}else{var _1i1=E(_1hZ[2]);return _1i1[0]==0?[0,[1,_1hB,_1hN],[1,_28,_1hO]]:[0,[1,_9,_1hN],[1,[1,[0,_1hJ,[1,_1hK,[1,_1i0[1],[1,_1i1[1],_9]]]]],_1hO]];}}}else{return [0,[1,_1hD,_1hN],[1,_28,_1hO]];}}}break;default:return [0,[1,_1hE,_1hN],[1,_28,_1hO]];}}else{return [0,[1,_1hF,_1hN],[1,_28,_1hO]];}}};return !B(_lv(_1hK,_1hG))?B(_1hP(_)):E(_1hL)[0]==0?[0,[1,_9,_1hN],[1,[1,[0,_1hJ,_1hA]],_1hO]]:B(_1hP(_));},_1i2=new T(function(){return B(unCStr("depends on an unjustified line"));}),_1i3=new T(function(){return B(unCStr("unavailable line"));}),_1i4=function(_1i5,_1i6,_1i7,_1i8){return E(B(_1i9(_1i5,_1i6,[1,_9,_1i7],[1,_28,_1i8]))[2]);},_1ia=function(_1ib,_1ic,_1id,_1ie,_1if,_1ig,_1ih,_1ii){var _1ij=B(_1hm(_1ie,_1if,B(_1i4(_1ib,_1ic,_1ih,_1ii))));if(!_1ij[0]){return new F(function(){return _1i9(_1ib,_1ic,[1,_1i3,_1ih],[1,_28,_1ii]);});}else{var _1ik=E(_1ij[1]),_1il=E(_1ik[1]);if(!_1il[0]){return new F(function(){return _1i9(_1ib,_1ic,[1,_1i2,_1ih],[1,_28,_1ii]);});}else{var _1im=E(_1ik[2]);return _1im[0]==0?B(_1i9(_1ib,_1ic,[1,_1i2,_1ih],[1,_28,_1ii])):B(_1i9(_1ib,_1ic,[1,_9,_1ih],[1,[1,[0,_1id,[1,_1ig,[1,_1il[1],[1,_1im[1],_9]]]]],_1ii]));}}},_1in=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1io=function(_1ip,_1iq,_1ir,_1is,_1it,_1iu,_1iv){var _1iw=E(_1it);if(!_1iw[0]){return new F(function(){return _1i9(_1ip,_1iq,[1,_1in,_1iu],[1,_28,_1iv]);});}else{var _1ix=E(_1iw[2]);if(!_1ix[0]){return new F(function(){return _1i9(_1ip,_1iq,[1,_1in,_1iu],[1,_28,_1iv]);});}else{if(!E(_1ix[2])[0]){return new F(function(){return _1ia(_1ip,_1iq,_1ir,E(_1iw[1])[1],E(_1ix[1])[1],_1is,_1iu,_1iv);});}else{return new F(function(){return _1i9(_1ip,_1iq,[1,_1in,_1iu],[1,_28,_1iv]);});}}}},_1iy=function(_1iz,_1iA,_1iB){return [0,[1,_9,_1iA],[1,_28,new T(function(){var _1iC=B(_15b(_1iA,0))-E(_1iz)[1]|0,_1iD=new T(function(){return _1iC>=0?B(_19P(_1iC,_1iB)):E(_1iB);});if(_1iC>0){var _1iE=function(_1iF,_1iG){var _1iH=E(_1iF);return _1iH[0]==0?E(_1iD):_1iG>1?[1,_28,new T(function(){return B(_1iE(_1iH[2],_1iG-1|0));})]:E([1,_28,_1iD]);},_1iI=B(_1iE(_1iB,_1iC));}else{var _1iI=E(_1iD);}var _1iJ=_1iI,_1iK=_1iJ,_1iL=_1iK,_1iM=_1iL;return _1iM;})]];},_1iN=function(_1iO,_1iP,_1iQ,_1iR,_1iS,_1iT,_1iU){var _1iV=new T(function(){return E(B(_1i9(_1iO,_1iP,[1,_9,_1iT],[1,_28,_1iU]))[2]);});if(_1iR<=B(_15b(_1iV,0))){var _1iW=_1iR-1|0;if(_1iW>=0){var _1iX=B(_gp(B(_1hd(_1iV)),_1iW));return _1iX[0]==0?B(_1i9(_1iO,_1iP,[1,_1i2,_1iT],[1,_28,_1iU])):B(_1i9(_1iO,_1iP,[1,_9,_1iT],[1,[1,[0,_1iQ,[1,_1iS,[1,_1iX[1],_9]]]],_1iU]));}else{return E(_gm);}}else{return new F(function(){return _1i9(_1iO,_1iP,[1,_1i3,_1iT],[1,_28,_1iU]);});}},_1iY=function(_1iZ,_1j0,_1j1,_1j2,_1j3,_1j4,_1j5){var _1j6=E(_1j3);if(!_1j6[0]){return new F(function(){return _1i9(_1iZ,_1j0,[1,_1in,_1j4],[1,_28,_1j5]);});}else{if(!E(_1j6[2])[0]){return new F(function(){return _1iN(_1iZ,_1j0,_1j1,E(_1j6[1])[1],_1j2,_1j4,_1j5);});}else{return new F(function(){return _1i9(_1iZ,_1j0,[1,_1in,_1j4],[1,_28,_1j5]);});}}},_1j7=new T(function(){return B(unCStr("Open Subproof"));}),_1j8=new T(function(){return B(unCStr("Impossible Error 2"));}),_1j9=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1ja=new T(function(){return B(unCStr("SHOW"));}),_1jb=function(_1jc,_1jd,_1je,_1jf,_1jg,_1jh,_1ji){if(!B(_lv(_1jd,_1ja))){var _1jj=B(A(_1jf,[_1jd]));if(!_1jj[0]){return [0,[1,_1hH,_1jh],[1,_28,_1ji]];}else{var _1jk=E(_1jj[1]);if(!_1jk[0]){return [0,[1,_1j9,_1jh],[1,_28,_1ji]];}else{switch(E(E(_1jk[1])[1])){case 1:var _1jl=B(_1iY(_1jg,_1jf,_1jc,_1jd,_1je,_1jh,_1ji));return new F(function(){return _1iy(new T(function(){return [0,B(_15b(_1jh,0))+1|0];},1),_1jl[1],_1jl[2]);});break;case 2:var _1jm=B(_1io(_1jg,_1jf,_1jc,_1jd,_1je,_1jh,_1ji));return new F(function(){return _1iy(new T(function(){return [0,B(_15b(_1jh,0))+1|0];},1),_1jm[1],_1jm[2]);});break;default:return [0,[1,_1j8,_1jh],[1,_28,_1ji]];}}}}else{var _1jn=B(_1i9(_1jg,_1jf,[1,_1j7,_1jh],[1,_28,_1ji]));return new F(function(){return _1iy(new T(function(){return [0,B(_15b(_1jh,0))+1|0];},1),_1jn[1],_1jn[2]);});}},_1jo=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1jp=new T(function(){return B(unCStr("formula syntax error"));}),_1jq=function(_1jr,_1js,_1jt,_1ju,_1jv){var _1jw=E(_1jr);if(!_1jw[0]){return E(_1js)[0]==0?[0,[1,_1jp,_1ju],[1,_28,_1jv]]:[0,[1,_1jo,_1ju],[1,_28,_1jv]];}else{var _1jx=_1jw[1],_1jy=E(_1js);if(!_1jy[0]){var _1jz=E(_1jx);return new F(function(){return _1hI(_1jz[1],_1jz[2],_1jz[3],_1jt,_1ju,_1jv);});}else{var _1jA=E(_1jx);return new F(function(){return _1jb(_1jA[1],_1jA[2],_1jA[3],_1jt,_1jy,_1ju,_1jv);});}}},_1i9=function(_1jB,_1jC,_1jD,_1jE){return new F(function(){return (function(_1jF,_1jG,_1jH){while(1){var _1jI=E(_1jH);if(!_1jI[0]){return [0,_1jF,_1jG];}else{var _1jJ=E(_1jI[1]),_1jK=B(_1jq(_1jJ[1],_1jJ[2],_1jC,_1jF,_1jG));_1jF=_1jK[1];_1jG=_1jK[2];_1jH=_1jI[2];continue;}}})(_1jD,_1jE,_1jB);});},_1jL=function(_1jM,_1jN){while(1){var _1jO=E(_1jN);if(!_1jO[0]){return true;}else{if(!B(A(_1jM,[_1jO[1]]))){return false;}else{_1jN=_1jO[2];continue;}}}},_1jP=[0,666],_1jQ=[0,_,_1jP],_1jR=[1,_1jQ],_1jS=[0,_1jR,_1hA],_1jT=function(_1jU){return new F(function(){return _lv(_1jU,_9);});},_1jV=function(_1jW,_1jX){var _1jY=B(_1i9(_1jW,_1jX,_9,_9)),_1jZ=_1jY[1];return !B(_1jL(_1jT,_1jZ))?[0,_1jZ]:[1,new T(function(){var _1k0=B(_15b(_1jW,0))-1|0;if(_1k0>=0){var _1k1=B(_gp(B(_db(_1jY[2],_9)),_1k0)),_1k2=_1k1[0]==0?E(_1jS):E(_1k1[1]);}else{var _1k2=E(_gm);}var _1k3=_1k2,_1k4=_1k3,_1k5=_1k4;return _1k5;})];},_1k6=function(_1k7,_1k8){return E(_1);},_1k9=function(_1ka,_1kb,_1kc,_1kd){var _1ke=E(_1kc);switch(_1ke[0]){case 0:var _1kf=E(_1kd);return _1kf[0]==0?E(_1):E(_1kf[1]);case 1:return new F(function(){return A(_1ka,[_1ke[1],_9]);});break;case 2:return new F(function(){return A(_1kb,[_1ke[1],[1,new T(function(){return B(_1k9(_1ka,_1kb,_1ke[2],_1kd));}),_9]]);});break;default:return new F(function(){return A(_1kb,[_1ke[1],[1,new T(function(){return B(_1k9(_1ka,_1kb,_1ke[2],_1kd));}),[1,new T(function(){return B(_1k9(_1ka,_1kb,_1ke[3],_1kd));}),_9]]]);});}},_1kg=function(_1kh,_1ki,_1kj,_1kk,_1kl,_1km,_1kn,_1ko){var _1kp=E(_1kn);switch(_1kp[0]){case 0:return [0];case 1:return new F(function(){return A(_1kk,[_1kp[1],_9]);});break;case 2:return new F(function(){return A(_1kh,[_1kp[1],[1,new T(function(){return B(_1k9(_1kk,_1kl,_1kp[2],_1ko));}),_9]]);});break;case 3:return new F(function(){return A(_1kh,[_1kp[1],[1,new T(function(){return B(_1k9(_1kk,_1kl,_1kp[2],_1ko));}),[1,new T(function(){return B(_1k9(_1kk,_1kl,_1kp[3],_1ko));}),_9]]]);});break;case 4:return new F(function(){return A(_1ki,[_1kp[1],[1,new T(function(){return B(_1kg(_1kh,_1ki,_1kj,_1kk,_1kl,_1km,_1kp[2],_1ko));}),_9]]);});break;case 5:return new F(function(){return A(_1ki,[_1kp[1],[1,new T(function(){return B(_1kg(_1kh,_1ki,_1kj,_1kk,_1kl,_1km,_1kp[2],_1ko));}),[1,new T(function(){return B(_1kg(_1kh,_1ki,_1kj,_1kk,_1kl,_1km,_1kp[3],_1ko));}),_9]]]);});break;default:var _1kq=_1kp[1],_1kr=_1kp[2];return new F(function(){return A(_1kj,[_1kq,[1,new T(function(){return B(A(_1km,[new T(function(){return B(A(_1kr,[_ae]));}),_1kq]));}),[1,new T(function(){return B(_1kg(_1kh,_1ki,_1kj,_1kk,_1kl,_1km,B(A(_1kr,[_ae])),[1,new T(function(){return B(A(_1km,[new T(function(){return B(A(_1kr,[_ae]));}),_1kq]));}),_9]));}),_9]]]);});}},_1ks=[0,95],_1kt=[1,_1ks,_9],_1ku=[1,_1kt,_9],_1kv=function(_1kw,_){return _1kw;},_1kx=function(_1ky){var _1kz=E(_1ky);return _1kz[0]==0?E(_1kv):function(_1kA,_){var _1kB=B(A(new T(function(){var _1kC=E(_1kz[1]);return B(_1kD(_1kC[1],_1kC[2]));}),[_1kA,_])),_1kE=_1kB,_1kF=B(A(new T(function(){return B(_1kx(_1kz[2]));}),[_1kA,_])),_1kG=_1kF;return _1kA;};},_1kH=function(_1kI,_1kJ){return function(_1kK,_){var _1kL=B(A(new T(function(){var _1kM=E(_1kI);return B(_1kD(_1kM[1],_1kM[2]));}),[_1kK,_])),_1kN=_1kL,_1kO=B(A(new T(function(){return B(_1kx(_1kJ));}),[_1kK,_])),_1kP=_1kO;return _1kK;};},_1kQ=function(_1kR,_1kS){return new F(function(){return _F(0,E(_1kR)[1],_1kS);});},_1kT=function(_1kU){return function(_mc,_18e){return new F(function(){return _56(new T(function(){return B(_2T(_1kQ,_1kU,_9));}),_mc,_18e);});};},_1kV=function(_1kW){return function(_mc,_18e){return new F(function(){return _56(new T(function(){return B(_1kg(_Q,_u,_Q,_N,_Q,_1k6,_1kW,_1ku));}),_mc,_18e);});};},_1kX=new T(function(){return B(unCStr("open"));}),_1kY=new T(function(){return B(unCStr("termination"));}),_1kZ=new T(function(){return B(unCStr("closed"));}),_1l0=function(_1l1){var _1l2=E(_1l1);return _1l2[0]==0?E(_1kv):function(_1l3,_){var _1l4=B(A(new T(function(){var _1l5=E(_1l2[1]);return B(_1kD(_1l5[1],_1l5[2]));}),[_1l3,_])),_1l6=_1l4,_1l7=B(A(new T(function(){return B(_1l0(_1l2[2]));}),[_1l3,_])),_1l8=_1l7;return _1l3;};},_1l9=function(_1la,_1lb){return function(_1lc,_){var _1ld=B(A(new T(function(){var _1le=E(_1la);return B(_1kD(_1le[1],_1le[2]));}),[_1lc,_])),_1lf=_1ld,_1lg=B(A(new T(function(){return B(_1l0(_1lb));}),[_1lc,_])),_1lh=_1lg;return _1lc;};},_1li=new T(function(){return B(unCStr("SHOW"));}),_1kD=function(_1lj,_1lk){var _1ll=E(_1lj);if(!_1ll[0]){return function(_mc,_18e){return new F(function(){return _bX(_56,_1ll[1],_mc,_18e);});};}else{var _1lm=E(_1ll[1]),_1ln=_1lm[1],_1lo=_1lm[2],_1lp=_1lm[3];if(!B(_lv(_1lo,_1li))){var _1lq=E(_1lk);return _1lq[0]==0?function(_mc,_18e){return new F(function(){return _bX(_63,function(_1lr,_){var _1ls=B(_5T(_1kV,_1ln,_1lr,_)),_1lt=_1ls,_1lu=B(_5T(_63,function(_1lv,_){var _1lw=B(_5T(_56,_1lo,_1lv,_)),_1lx=_1lw,_1ly=B(_5T(_1kT,_1lp,_1lv,_)),_1lz=_1ly;return _1lv;},_1lr,_)),_1lA=_1lu;return _1lr;},_mc,_18e);});}:function(_mc,_18e){return new F(function(){return _bX(_63,function(_1lB,_){var _1lC=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1kg(_Q,_u,_Q,_N,_Q,_1k6,_1ln,_1ku));})));}),_1lB,_)),_1lD=_1lC,_1lE=B(_bX(_63,function(_1lF,_){var _1lG=B(_5T(_63,new T(function(){return B(_1kH(_1lq[1],_1lq[2]));}),_1lF,_)),_1lH=_1lG,_1lI=B(_bX(_63,function(_1lJ,_){var _1lK=B(_5T(_56,_9,_1lJ,_)),_1lL=_1lK,_1lM=B(A(_5d,[_5q,_1lL,_bP,_1kY,_])),_1lN=_1lM,_1lO=B(_5T(_63,function(_1lP,_){var _1lQ=B(_5T(_56,_1lo,_1lP,_)),_1lR=_1lQ,_1lS=B(_5T(_1kT,_1lp,_1lP,_)),_1lT=_1lS;return _1lP;},_1lJ,_)),_1lU=_1lO;return _1lJ;},_1lF,_)),_1lV=_1lI;return _1lF;},_1lB,_)),_1lW=_1lE,_1lX=B(A(_5d,[_5q,_1lW,_bP,_1kZ,_])),_1lY=_1lX;return _1lB;},_mc,_18e);});};}else{var _1lZ=E(_1lk);return _1lZ[0]==0?function(_mc,_18e){return new F(function(){return _bX(_63,function(_bB,_){return new F(function(){return _5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1kg(_Q,_u,_Q,_N,_Q,_1k6,_1ln,_1ku));})));}),_bB,_);});},_mc,_18e);});}:function(_mc,_18e){return new F(function(){return _bX(_63,function(_1m0,_){var _1m1=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1kg(_Q,_u,_Q,_N,_Q,_1k6,_1ln,_1ku));})));}),_1m0,_)),_1m2=_1m1,_1m3=B(_bX(_63,function(_bB,_){return new F(function(){return _5T(_63,new T(function(){return B(_1l9(_1lZ[1],_1lZ[2]));}),_bB,_);});},_1m0,_)),_1m4=_1m3,_1m5=B(A(_5d,[_5q,_1m4,_bP,_1kX,_])),_1m6=_1m5;return _1m0;},_mc,_18e);});};}}},_1m7=function(_1m8){var _1m9=E(_1m8);return _1m9[0]==0?E(_1kv):function(_1ma,_){var _1mb=B(A(new T(function(){var _1mc=E(_1m9[1]);return B(_1kD(_1mc[1],_1mc[2]));}),[_1ma,_])),_1md=_1mb,_1me=B(A(new T(function(){return B(_1m7(_1m9[2]));}),[_1ma,_])),_1mf=_1me;return _1ma;};},_1mg=[0,10],_1mh=[1,_1mg,_9],_1mi=function(_1mj,_1mk,_){var _1ml=jsCreateElem(toJSStr(E(_1mj))),_1mm=_1ml,_1mn=jsAppendChild(_1mm,E(_1mk)[1]);return [0,_1mm];},_1mo=function(_1mp,_1mq,_1mr,_){var _1ms=B(_1mi(_1mp,_1mr,_)),_1mt=_1ms,_1mu=B(A(_1mq,[_1mt,_])),_1mv=_1mu;return _1mt;},_1mw=new T(function(){return B(unCStr("()"));}),_1mx=new T(function(){return B(unCStr("GHC.Tuple"));}),_1my=new T(function(){return B(unCStr("ghc-prim"));}),_1mz=new T(function(){var _1mA=hs_wordToWord64(2170319554),_1mB=_1mA,_1mC=hs_wordToWord64(26914641),_1mD=_1mC;return [0,_1mB,_1mD,[0,_1mB,_1mD,_1my,_1mx,_1mw],_9];}),_1mE=function(_1mF){return E(_1mz);},_1mG=new T(function(){return B(unCStr("PerchM"));}),_1mH=new T(function(){return B(unCStr("Haste.Perch"));}),_1mI=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1mJ=new T(function(){var _1mK=hs_wordToWord64(3005229400),_1mL=_1mK,_1mM=hs_wordToWord64(2682402736),_1mN=_1mM;return [0,_1mL,_1mN,[0,_1mL,_1mN,_1mI,_1mH,_1mG],_9];}),_1mO=function(_1mP){return E(_1mJ);},_1mQ=function(_1mR){var _1mS=E(_1mR);if(!_1mS[0]){return [0];}else{var _1mT=E(_1mS[1]);return [1,[0,_1mT[1],_1mT[2]],new T(function(){return B(_1mQ(_1mS[2]));})];}},_1mU=function(_1mV,_1mW){var _1mX=E(_1mV);if(!_1mX){return [0,_9,_1mW];}else{var _1mY=E(_1mW);if(!_1mY[0]){return [0,_9,_9];}else{var _1mZ=new T(function(){var _1n0=B(_1mU(_1mX-1|0,_1mY[2]));return [0,_1n0[1],_1n0[2]];});return [0,[1,_1mY[1],new T(function(){return E(E(_1mZ)[1]);})],new T(function(){return E(E(_1mZ)[2]);})];}}},_1n1=[0,120],_1n2=[0,48],_1n3=function(_1n4){var _1n5=new T(function(){var _1n6=B(_1mU(8,new T(function(){var _1n7=md5(toJSStr(E(_1n4))),_1n8=_1n7;return fromJSStr(_1n8);})));return [0,_1n6[1],_1n6[2]];}),_1n9=parseInt([0,toJSStr([1,_1n2,[1,_1n1,new T(function(){return E(E(_1n5)[1]);})]])]),_1na=_1n9,_1nb=new T(function(){var _1nc=B(_1mU(8,new T(function(){return E(E(_1n5)[2]);})));return [0,_1nc[1],_1nc[2]];}),_1nd=parseInt([0,toJSStr([1,_1n2,[1,_1n1,new T(function(){return E(E(_1nb)[1]);})]])]),_1ne=_1nd,_1nf=hs_mkWord64(_1na,_1ne),_1ng=_1nf,_1nh=parseInt([0,toJSStr([1,_1n2,[1,_1n1,new T(function(){return E(B(_1mU(8,new T(function(){return E(E(_1nb)[2]);})))[1]);})]])]),_1ni=_1nh,_1nj=hs_mkWord64(_1ni,_1ni),_1nk=_1nj;return [0,_1ng,_1nk];},_1nl=function(_1nm,_1nn){var _1no=jsShowI(_1nm),_1np=_1no,_1nq=md5(_1np),_1nr=_1nq;return new F(function(){return _e(fromJSStr(_1nr),new T(function(){var _1ns=jsShowI(_1nn),_1nt=_1ns,_1nu=md5(_1nt),_1nv=_1nu;return fromJSStr(_1nv);},1));});},_1nw=function(_1nx){var _1ny=E(_1nx);return new F(function(){return _1nl(_1ny[1],_1ny[2]);});},_1nz=function(_1nA,_1nB){return function(_1nC){return E(new T(function(){var _1nD=B(A(_1nA,[_])),_1nE=E(_1nD[3]),_1nF=_1nE[1],_1nG=_1nE[2],_1nH=B(_e(_1nD[4],[1,new T(function(){return B(A(_1nB,[_]));}),_9]));if(!_1nH[0]){var _1nI=[0,_1nF,_1nG,_1nE,_9];}else{var _1nJ=B(_1n3(new T(function(){return B(_7r(B(_7X(_1nw,[1,[0,_1nF,_1nG],new T(function(){return B(_1mQ(_1nH));})]))));},1))),_1nI=[0,_1nJ[1],_1nJ[2],_1nE,_1nH];}var _1nK=_1nI,_1nL=_1nK;return _1nL;}));};},_1nM=new T(function(){return B(_1nz(_1mO,_1mE));}),_1nN=function(_1nO,_1nP,_1nQ,_){var _1nR=E(_1nP),_1nS=B(A(_1nO,[_1nQ,_])),_1nT=_1nS,_1nU=B(A(_5d,[_5q,_1nT,_1nR[1],_1nR[2],_])),_1nV=_1nU;return _1nT;},_1nW=function(_1nX,_1nY){while(1){var _1nZ=(function(_1o0,_1o1){var _1o2=E(_1o1);if(!_1o2[0]){return E(_1o0);}else{_1nX=function(_1o3,_){return new F(function(){return _1nN(_1o0,_1o2[1],_1o3,_);});};_1nY=_1o2[2];return null;}})(_1nX,_1nY);if(_1nZ!=null){return _1nZ;}}},_1o4=new T(function(){return B(unCStr("value"));}),_1o5=new T(function(){return B(unCStr("id"));}),_1o6=new T(function(){return B(unCStr("onclick"));}),_1o7=new T(function(){return B(unCStr("checked"));}),_1o8=[0,_1o7,_9],_1o9=new T(function(){return B(unCStr("type"));}),_1oa=new T(function(){return B(unCStr("input"));}),_1ob=function(_1oc,_){return new F(function(){return _1mi(_1oa,_1oc,_);});},_1od=function(_1oe,_1of,_1og){return new F(function(){return _1nW(function(_1o3,_){return new F(function(){return _1nN(_1oe,_1of,_1o3,_);});},_1og);});},_1oh=function(_1oi,_1oj,_1ok,_1ol,_1om){var _1on=new T(function(){var _1oo=new T(function(){return B(_1od(_1ob,[0,_1o9,_1oj],[1,[0,_1o5,_1oi],[1,[0,_1o4,_1ok],_9]]));});return !E(_1ol)?E(_1oo):B(_1od(_1oo,_1o8,_9));}),_1op=E(_1om);return _1op[0]==0?E(_1on):B(_1od(_1on,[0,_1o6,_1op[1]],_9));},_1oq=new T(function(){return B(unCStr("href"));}),_1or=[0,97],_1os=[1,_1or,_9],_1ot=function(_1ou,_){return new F(function(){return _1mi(_1os,_1ou,_);});},_1ov=function(_1ow,_1ox){return function(_1oy,_){var _1oz=B(A(new T(function(){return B(_1od(_1ot,[0,_1oq,_1ow],_9));}),[_1oy,_])),_1oA=_1oz,_1oB=B(A(_1ox,[_1oA,_])),_1oC=_1oB;return _1oA;};},_1oD=function(_1oE){return new F(function(){return _1ov(_1oE,function(_1o3,_){return new F(function(){return _56(_1oE,_1o3,_);});});});},_1oF=new T(function(){return B(unCStr("option"));}),_1oG=function(_1oH,_){return new F(function(){return _1mi(_1oF,_1oH,_);});},_1oI=new T(function(){return B(unCStr("selected"));}),_1oJ=[0,_1oI,_9],_1oK=function(_1oL,_1oM,_1oN){var _1oO=new T(function(){return B(_1od(_1oG,[0,_1o4,_1oL],_9));});if(!E(_1oN)){return function(_1oP,_){var _1oQ=B(A(_1oO,[_1oP,_])),_1oR=_1oQ,_1oS=B(A(_1oM,[_1oR,_])),_1oT=_1oS;return _1oR;};}else{return new F(function(){return _1od(function(_1oU,_){var _1oV=B(A(_1oO,[_1oU,_])),_1oW=_1oV,_1oX=B(A(_1oM,[_1oW,_])),_1oY=_1oX;return _1oW;},_1oJ,_9);});}},_1oZ=function(_1p0,_1p1){return new F(function(){return _1oK(_1p0,function(_1o3,_){return new F(function(){return _56(_1p0,_1o3,_);});},_1p1);});},_1p2=new T(function(){return B(unCStr("method"));}),_1p3=new T(function(){return B(unCStr("action"));}),_1p4=new T(function(){return B(unCStr("UTF-8"));}),_1p5=new T(function(){return B(unCStr("acceptCharset"));}),_1p6=[0,_1p5,_1p4],_1p7=new T(function(){return B(unCStr("form"));}),_1p8=function(_1p9,_){return new F(function(){return _1mi(_1p7,_1p9,_);});},_1pa=function(_1pb,_1pc,_1pd){return function(_1pe,_){var _1pf=B(A(new T(function(){return B(_1od(_1p8,_1p6,[1,[0,_1p3,_1pb],[1,[0,_1p2,_1pc],_9]]));}),[_1pe,_])),_1pg=_1pf,_1ph=B(A(_1pd,[_1pg,_])),_1pi=_1ph;return _1pg;};},_1pj=new T(function(){return B(unCStr("select"));}),_1pk=function(_1pl,_){return new F(function(){return _1mi(_1pj,_1pl,_);});},_1pm=function(_1pn,_1po){return function(_1pp,_){var _1pq=B(A(new T(function(){return B(_1od(_1pk,[0,_1o5,_1pn],_9));}),[_1pp,_])),_1pr=_1pq,_1ps=B(A(_1po,[_1pr,_])),_1pt=_1ps;return _1pr;};},_1pu=new T(function(){return B(unCStr("textarea"));}),_1pv=function(_1pw,_){return new F(function(){return _1mi(_1pu,_1pw,_);});},_1px=function(_1py,_1pz){return function(_1pA,_){var _1pB=B(A(new T(function(){return B(_1od(_1pv,[0,_1o5,_1py],_9));}),[_1pA,_])),_1pC=_1pB,_1pD=B(_56(_1pz,_1pC,_)),_1pE=_1pD;return _1pC;};},_1pF=new T(function(){return B(unCStr("color:red"));}),_1pG=new T(function(){return B(unCStr("style"));}),_1pH=[0,_1pG,_1pF],_1pI=[0,98],_1pJ=[1,_1pI,_9],_1pK=function(_1pL){return new F(function(){return _1od(function(_1pM,_){var _1pN=B(_1mi(_1pJ,_1pM,_)),_1pO=_1pN,_1pP=B(A(_1pL,[_1pO,_])),_1pQ=_1pP;return _1pO;},_1pH,_9);});},_1pR=function(_1pS,_1pT,_){var _1pU=E(_1pS);if(!_1pU[0]){return _1pT;}else{var _1pV=B(A(_1pU[1],[_1pT,_])),_1pW=_1pV,_1pX=B(_1pR(_1pU[2],_1pT,_)),_1pY=_1pX;return _1pT;}},_1pZ=function(_1q0,_1q1,_){return new F(function(){return _1pR(_1q0,_1q1,_);});},_1q2=function(_1q3,_1q4,_1q5,_){var _1q6=B(A(_1q3,[_1q5,_])),_1q7=_1q6,_1q8=B(A(_1q4,[_1q5,_])),_1q9=_1q8;return _1q5;},_1qa=[0,_5t,_1q2,_1pZ],_1qb=[0,_1qa,_1nM,_56,_56,_1mo,_1pK,_1ov,_1oD,_1oh,_1px,_1pm,_1oK,_1oZ,_1pa,_1nW],_1qc=function(_1qd,_1qe,_){var _1qf=B(A(_1qe,[_])),_1qg=_1qf;return _1qd;},_1qh=function(_1qi,_1qj,_){var _1qk=B(A(_1qj,[_])),_1ql=_1qk;return new T(function(){return B(A(_1qi,[_1ql]));});},_1qm=[0,_1qh,_1qc],_1qn=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1qo=new T(function(){return B(unCStr("base"));}),_1qp=new T(function(){return B(unCStr("IOException"));}),_1qq=new T(function(){var _1qr=hs_wordToWord64(4053623282),_1qs=_1qr,_1qt=hs_wordToWord64(3693590983),_1qu=_1qt;return [0,_1qs,_1qu,[0,_1qs,_1qu,_1qo,_1qn,_1qp],_9];}),_1qv=function(_1qw){return E(_1qq);},_1qx=function(_1qy){var _1qz=E(_1qy);return new F(function(){return _2y(B(_2w(_1qz[1])),_1qv,_1qz[2]);});},_1qA=new T(function(){return B(unCStr(": "));}),_1qB=[0,41],_1qC=new T(function(){return B(unCStr(" ("));}),_1qD=new T(function(){return B(unCStr("already exists"));}),_1qE=new T(function(){return B(unCStr("does not exist"));}),_1qF=new T(function(){return B(unCStr("protocol error"));}),_1qG=new T(function(){return B(unCStr("failed"));}),_1qH=new T(function(){return B(unCStr("invalid argument"));}),_1qI=new T(function(){return B(unCStr("inappropriate type"));}),_1qJ=new T(function(){return B(unCStr("hardware fault"));}),_1qK=new T(function(){return B(unCStr("unsupported operation"));}),_1qL=new T(function(){return B(unCStr("timeout"));}),_1qM=new T(function(){return B(unCStr("resource vanished"));}),_1qN=new T(function(){return B(unCStr("interrupted"));}),_1qO=new T(function(){return B(unCStr("resource busy"));}),_1qP=new T(function(){return B(unCStr("resource exhausted"));}),_1qQ=new T(function(){return B(unCStr("end of file"));}),_1qR=new T(function(){return B(unCStr("illegal operation"));}),_1qS=new T(function(){return B(unCStr("permission denied"));}),_1qT=new T(function(){return B(unCStr("user error"));}),_1qU=new T(function(){return B(unCStr("unsatisified constraints"));}),_1qV=new T(function(){return B(unCStr("system error"));}),_1qW=function(_1qX,_1qY){switch(E(_1qX)){case 0:return new F(function(){return _e(_1qD,_1qY);});break;case 1:return new F(function(){return _e(_1qE,_1qY);});break;case 2:return new F(function(){return _e(_1qO,_1qY);});break;case 3:return new F(function(){return _e(_1qP,_1qY);});break;case 4:return new F(function(){return _e(_1qQ,_1qY);});break;case 5:return new F(function(){return _e(_1qR,_1qY);});break;case 6:return new F(function(){return _e(_1qS,_1qY);});break;case 7:return new F(function(){return _e(_1qT,_1qY);});break;case 8:return new F(function(){return _e(_1qU,_1qY);});break;case 9:return new F(function(){return _e(_1qV,_1qY);});break;case 10:return new F(function(){return _e(_1qF,_1qY);});break;case 11:return new F(function(){return _e(_1qG,_1qY);});break;case 12:return new F(function(){return _e(_1qH,_1qY);});break;case 13:return new F(function(){return _e(_1qI,_1qY);});break;case 14:return new F(function(){return _e(_1qJ,_1qY);});break;case 15:return new F(function(){return _e(_1qK,_1qY);});break;case 16:return new F(function(){return _e(_1qL,_1qY);});break;case 17:return new F(function(){return _e(_1qM,_1qY);});break;default:return new F(function(){return _e(_1qN,_1qY);});}},_1qZ=[0,125],_1r0=new T(function(){return B(unCStr("{handle: "));}),_1r1=function(_1r2,_1r3,_1r4,_1r5,_1r6,_1r7){var _1r8=new T(function(){var _1r9=new T(function(){return B(_1qW(_1r3,new T(function(){var _1ra=E(_1r5);return _1ra[0]==0?E(_1r7):B(_e(_1qC,new T(function(){return B(_e(_1ra,[1,_1qB,_1r7]));},1)));},1)));},1),_1rb=E(_1r4);return _1rb[0]==0?E(_1r9):B(_e(_1rb,new T(function(){return B(_e(_1qA,_1r9));},1)));},1),_1rc=E(_1r6);if(!_1rc[0]){var _1rd=E(_1r2);if(!_1rd[0]){return E(_1r8);}else{var _1re=E(_1rd[1]);return _1re[0]==0?B(_e(_1r0,new T(function(){return B(_e(_1re[1],[1,_1qZ,new T(function(){return B(_e(_1qA,_1r8));})]));},1))):B(_e(_1r0,new T(function(){return B(_e(_1re[1],[1,_1qZ,new T(function(){return B(_e(_1qA,_1r8));})]));},1)));}}else{return new F(function(){return _e(_1rc[1],new T(function(){return B(_e(_1qA,_1r8));},1));});}},_1rf=function(_1rg){var _1rh=E(_1rg);return new F(function(){return _1r1(_1rh[1],_1rh[2],_1rh[3],_1rh[4],_1rh[6],_9);});},_1ri=function(_1rj,_1rk){var _1rl=E(_1rj);return new F(function(){return _1r1(_1rl[1],_1rl[2],_1rl[3],_1rl[4],_1rl[6],_1rk);});},_1rm=function(_1rn,_1ro){return new F(function(){return _2T(_1ri,_1rn,_1ro);});},_1rp=function(_1rq,_1rr,_1rs){var _1rt=E(_1rr);return new F(function(){return _1r1(_1rt[1],_1rt[2],_1rt[3],_1rt[4],_1rt[6],_1rs);});},_1ru=[0,_1rp,_1rf,_1rm],_1rv=new T(function(){return [0,_1qv,_1ru,_1rw,_1qx];}),_1rw=function(_1rx){return [0,_1rv,_1rx];},_1ry=7,_1rz=function(_1rA){return [0,_28,_1ry,_9,_1rA,_28,_28];},_1rB=function(_1rC,_){return new F(function(){return die(new T(function(){return B(_1rw(new T(function(){return B(_1rz(_1rC));})));}));});},_1rD=function(_1rE,_){return new F(function(){return _1rB(_1rE,_);});},_1rF=function(_1rG,_){return new F(function(){return _1rD(_1rG,_);});},_1rH=function(_1rI,_){return new F(function(){return _1rF(_1rI,_);});},_1rJ=function(_1rK,_1rL,_){var _1rM=B(A(_1rK,[_])),_1rN=_1rM;return new F(function(){return A(_1rL,[_1rN,_]);});},_1rO=function(_1rP,_1rQ,_){var _1rR=B(A(_1rP,[_])),_1rS=_1rR;return new F(function(){return A(_1rQ,[_]);});},_1rT=[0,_1rJ,_1rO,_5t,_1rH],_1rU=[0,_1rT,_5q],_1rV=function(_1rW){return E(E(_1rW)[1]);},_1rX=function(_1rY){return E(E(_1rY)[2]);},_1rZ=function(_1s0,_1s1){var _1s2=new T(function(){return B(_1rV(_1s0));});return function(_1s3){return new F(function(){return A(new T(function(){return B(_Ox(_1s2));}),[new T(function(){return B(A(_1rX,[_1s0,_1s1]));}),function(_1s4){return new F(function(){return A(new T(function(){return B(_iK(_1s2));}),[[0,_1s4,_1s3]]);});}]);});};},_1s5=function(_1s6,_1s7){return [0,_1s6,function(_1s8){return new F(function(){return _1rZ(_1s7,_1s8);});}];},_1s9=function(_1sa,_1sb,_1sc,_1sd){return new F(function(){return A(_Ox,[_1sa,new T(function(){return B(A(_1sb,[_1sd]));}),function(_1se){return new F(function(){return A(_1sc,[new T(function(){return E(E(_1se)[1]);}),new T(function(){return E(E(_1se)[2]);})]);});}]);});},_1sf=function(_1sg,_1sh,_1si,_1sj){return new F(function(){return A(_Ox,[_1sg,new T(function(){return B(A(_1sh,[_1sj]));}),function(_1sk){return new F(function(){return A(_1si,[new T(function(){return E(E(_1sk)[2]);})]);});}]);});},_1sl=function(_1sm,_1sn,_1so,_1sp){return new F(function(){return _1sf(_1sm,_1sn,_1so,_1sp);});},_1sq=function(_1sr){return E(E(_1sr)[4]);},_1ss=function(_1st,_1su){return function(_1sv){return E(new T(function(){return B(A(_1sq,[_1st,_1su]));}));};},_1sw=function(_1sx){return [0,function(_1sn,_1so,_1sp){return new F(function(){return _1s9(_1sx,_1sn,_1so,_1sp);});},function(_1sn,_1so,_1sp){return new F(function(){return _1sl(_1sx,_1sn,_1so,_1sp);});},function(_1sy,_1sz){return new F(function(){return A(new T(function(){return B(_iK(_1sx));}),[[0,_1sy,_1sz]]);});},function(_1sp){return new F(function(){return _1ss(_1sx,_1sp);});}];},_1sA=function(_1sB,_1sC,_1sD){return new F(function(){return A(_iK,[_1sB,[0,_1sC,_1sD]]);});},_1sE=[0,10],_1sF=function(_1sG,_1sH){var _1sI=E(_1sH);if(!_1sI[0]){return E(_5q);}else{var _1sJ=_1sI[1],_1sK=E(_1sI[2]);if(!_1sK[0]){var _1sL=E(_1sJ);return new F(function(){return _1sM(_1sE,_1sL[3],_1sL[4]);});}else{return function(_1sN){return new F(function(){return A(new T(function(){var _1sO=E(_1sJ);return B(_1sM(_1sE,_1sO[3],_1sO[4]));}),[new T(function(){return B(A(_1sG,[new T(function(){return B(A(new T(function(){return B(_1sF(_1sG,_1sK));}),[_1sN]));})]));})]);});};}}},_1sP=new T(function(){return B(unCStr("(->)"));}),_1sQ=new T(function(){return B(unCStr("GHC.Prim"));}),_1sR=new T(function(){var _1sS=hs_wordToWord64(4173248105),_1sT=_1sS,_1sU=hs_wordToWord64(4270398258),_1sV=_1sU;return [0,_1sT,_1sV,[0,_1sT,_1sV,_1my,_1sQ,_1sP],_9];}),_1sW=new T(function(){return E(E(_1sR)[3]);}),_1sX=new T(function(){return B(unCStr("GHC.Types"));}),_1sY=new T(function(){return B(unCStr("[]"));}),_1sZ=new T(function(){var _1t0=hs_wordToWord64(4033920485),_1t1=_1t0,_1t2=hs_wordToWord64(786266835),_1t3=_1t2;return [0,_1t1,_1t3,[0,_1t1,_1t3,_1my,_1sX,_1sY],_9];}),_1t4=[1,_1mz,_9],_1t5=function(_1t6){var _1t7=E(_1t6);if(!_1t7[0]){return [0];}else{var _1t8=E(_1t7[1]);return [1,[0,_1t8[1],_1t8[2]],new T(function(){return B(_1t5(_1t7[2]));})];}},_1t9=new T(function(){var _1ta=E(_1sZ),_1tb=E(_1ta[3]),_1tc=B(_e(_1ta[4],_1t4));if(!_1tc[0]){var _1td=E(_1tb);}else{var _1te=B(_1n3(new T(function(){return B(_7r(B(_7X(_1nw,[1,[0,_1tb[1],_1tb[2]],new T(function(){return B(_1t5(_1tc));})]))));},1))),_1td=E(_1tb);}var _1tf=_1td,_1tg=_1tf;return _1tg;}),_1th=[0,8],_1ti=[0,32],_1tj=function(_1tk){return [1,_1ti,_1tk];},_1tl=new T(function(){return B(unCStr(" -> "));}),_1tm=[0,9],_1tn=[0,93],_1to=[0,91],_1tp=[0,41],_1tq=[0,44],_1tr=function(_1tk){return [1,_1tq,_1tk];},_1ts=[0,40],_1tt=[0,0],_1sM=function(_1tu,_1tv,_1tw){var _1tx=E(_1tw);if(!_1tx[0]){return function(_1ty){return new F(function(){return _e(E(_1tv)[5],_1ty);});};}else{var _1tz=_1tx[1],_1tA=function(_1tB){var _1tC=E(_1tv)[5],_1tD=function(_1tE){var _1tF=new T(function(){return B(_1sF(_1tj,_1tx));});return E(_1tu)[1]<=9?function(_1tG){return new F(function(){return _e(_1tC,[1,_1ti,new T(function(){return B(A(_1tF,[_1tG]));})]);});}:function(_1tH){return [1,_E,new T(function(){return B(_e(_1tC,[1,_1ti,new T(function(){return B(A(_1tF,[[1,_D,_1tH]]));})]));})];};},_1tI=E(_1tC);if(!_1tI[0]){return new F(function(){return _1tD(_);});}else{if(E(E(_1tI[1])[1])==40){var _1tJ=E(_1tI[2]);if(!_1tJ[0]){return new F(function(){return _1tD(_);});}else{if(E(E(_1tJ[1])[1])==44){return function(_1tK){return [1,_1ts,new T(function(){return B(A(new T(function(){return B(_1sF(_1tr,_1tx));}),[[1,_1tp,_1tK]]));})];};}else{return new F(function(){return _1tD(_);});}}}else{return new F(function(){return _1tD(_);});}}},_1tL=E(_1tx[2]);if(!_1tL[0]){var _1tM=E(_1tv),_1tN=E(_1t9),_1tO=hs_eqWord64(_1tM[1],_1tN[1]),_1tP=_1tO;if(!E(_1tP)){return new F(function(){return _1tA(_);});}else{var _1tQ=hs_eqWord64(_1tM[2],_1tN[2]),_1tR=_1tQ;if(!E(_1tR)){return new F(function(){return _1tA(_);});}else{return function(_1tS){return [1,_1to,new T(function(){return B(A(new T(function(){var _1tT=E(_1tz);return B(_1sM(_1tt,_1tT[3],_1tT[4]));}),[[1,_1tn,_1tS]]));})];};}}}else{if(!E(_1tL[2])[0]){var _1tU=E(_1tv),_1tV=E(_1sW),_1tW=hs_eqWord64(_1tU[1],_1tV[1]),_1tX=_1tW;if(!E(_1tX)){return new F(function(){return _1tA(_);});}else{var _1tY=hs_eqWord64(_1tU[2],_1tV[2]),_1tZ=_1tY;if(!E(_1tZ)){return new F(function(){return _1tA(_);});}else{var _1u0=new T(function(){var _1u1=E(_1tL[1]);return B(_1sM(_1th,_1u1[3],_1u1[4]));}),_1u2=new T(function(){var _1u3=E(_1tz);return B(_1sM(_1tm,_1u3[3],_1u3[4]));});return E(_1tu)[1]<=8?function(_1u4){return new F(function(){return A(_1u2,[new T(function(){return B(_e(_1tl,new T(function(){return B(A(_1u0,[_1u4]));},1)));})]);});}:function(_1u5){return [1,_E,new T(function(){return B(A(_1u2,[new T(function(){return B(_e(_1tl,new T(function(){return B(A(_1u0,[[1,_D,_1u5]]));},1)));})]));})];};}}}else{return new F(function(){return _1tA(_);});}}}},_1u6=function(_1u7,_1u8){return new F(function(){return A(_1u7,[function(_){return new F(function(){return jsFind(toJSStr(E(_1u8)));});}]);});},_1u9=[0],_1ua=function(_1ub){return E(E(_1ub)[3]);},_1uc=new T(function(){return [0,"value"];}),_1ud=function(_1ue){return E(E(_1ue)[6]);},_1uf=function(_1ug){return E(E(_1ug)[1]);},_1uh=new T(function(){return B(unCStr("Char"));}),_1ui=new T(function(){var _1uj=hs_wordToWord64(3763641161),_1uk=_1uj,_1ul=hs_wordToWord64(1343745632),_1um=_1ul;return [0,_1uk,_1um,[0,_1uk,_1um,_1my,_1sX,_1uh],_9];}),_1un=function(_1uo){return E(_1ui);},_1up=function(_1uq){return E(_1sZ);},_1ur=new T(function(){return B(_1nz(_1up,_1un));}),_1us=new T(function(){return B(A(_1ur,[_]));}),_1ut=function(_1uu,_1uv,_1uw,_1ux,_1uy,_1uz,_1uA,_1uB,_1uC){var _1uD=new T(function(){return B(A(_1ux,[_1u9]));});return new F(function(){return A(_1uv,[new T(function(){return B(_1u6(E(_1uu)[2],_1uC));}),function(_1uE){var _1uF=E(_1uE);return _1uF[0]==0?E(_1uD):B(A(_1uv,[new T(function(){return B(A(E(_1uu)[2],[function(_){var _1uG=jsGet(E(_1uF[1])[1],E(_1uc)[1]),_1uH=_1uG;return [1,new T(function(){return fromJSStr(_1uH);})];}]));}),function(_1uI){var _1uJ=E(_1uI);if(!_1uJ[0]){return E(_1uD);}else{var _1uK=_1uJ[1];if(!E(new T(function(){var _1uL=B(A(_1uz,[_])),_1uM=E(_1us),_1uN=hs_eqWord64(_1uL[1],_1uM[1]),_1uO=_1uN;if(!E(_1uO)){var _1uP=false;}else{var _1uQ=hs_eqWord64(_1uL[2],_1uM[2]),_1uR=_1uQ,_1uP=E(_1uR)==0?false:true;}var _1uS=_1uP,_1uT=_1uS;return _1uT;}))){var _1uU=function(_1uV){return new F(function(){return A(_1ux,[[1,_1uK,new T(function(){return B(A(new T(function(){return B(_1ud(_1uB));}),[new T(function(){return B(A(new T(function(){return B(_1ua(_1uB));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1uK,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1uW=B(A(_1uz,[_]));return B(A(_1sM,[_1tt,_1uW[3],_1uW[4],_9]));})));})));})));})]));})]));})]]);});},_1uX=B(A(new T(function(){return B(A(_1uf,[_1uA,_1R]));}),[_1uK]));if(!_1uX[0]){return new F(function(){return _1uU(_);});}else{var _1uY=E(_1uX[1]);return E(_1uY[2])[0]==0?E(_1uX[2])[0]==0?B(A(_1ux,[[2,_1uY[1]]])):B(_1uU(_)):B(_1uU(_));}}else{return new F(function(){return A(_1ux,[[2,_1uK]]);});}}}]));}]);});},_1uZ=function(_1v0){return E(E(_1v0)[10]);},_1v1=function(_1v2){return new F(function(){return _kY([1,function(_1v3){return new F(function(){return A(_sE,[_1v3,function(_1v4){return E(new T(function(){return B(_tU(function(_1v5){var _1v6=E(_1v5);return _1v6[0]==0?B(A(_1v2,[_1v6[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_ug(_1v7,_1v2))];}));});},_1v7=function(_1v8,_1v9){return new F(function(){return _1v1(_1v9);});},_1va=[0,91],_1vb=[1,_1va,_9],_1vc=function(_1vd,_1ve){var _1vf=function(_1vg,_1vh){return [1,function(_1vi){return new F(function(){return A(_sE,[_1vi,function(_1vj){return E(new T(function(){return B(_tU(function(_1vk){var _1vl=E(_1vk);if(_1vl[0]==2){var _1vm=E(_1vl[1]);if(!_1vm[0]){return [2];}else{var _1vn=_1vm[2];switch(E(E(_1vm[1])[1])){case 44:return E(_1vn)[0]==0?!E(_1vg)?[2]:E(new T(function(){return B(A(_1vd,[_uf,function(_1vo){return new F(function(){return _1vf(_ob,function(_1vp){return new F(function(){return A(_1vh,[[1,_1vo,_1vp]]);});});});}]));})):[2];case 93:return E(_1vn)[0]==0?E(new T(function(){return B(A(_1vh,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1vq=function(_1vr){return new F(function(){return _kY([1,function(_1vs){return new F(function(){return A(_sE,[_1vs,function(_1vt){return E(new T(function(){return B(_tU(function(_1vu){var _1vv=E(_1vu);return _1vv[0]==2?!B(_lv(_1vv[1],_1vb))?[2]:E(new T(function(){return B(_kY(B(_1vf(_1S,_1vr)),new T(function(){return B(A(_1vd,[_uf,function(_1vw){return new F(function(){return _1vf(_ob,function(_1vx){return new F(function(){return A(_1vr,[[1,_1vw,_1vx]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_ug(function(_1vy,_1vz){return new F(function(){return _1vq(_1vz);});},_1vr))];}));});};return new F(function(){return _1vq(_1ve);});},_1vA=function(_1vB){return new F(function(){return _kY(B(_kY([1,function(_1vC){return new F(function(){return A(_sE,[_1vC,function(_1vD){return E(new T(function(){return B(_tU(function(_1vE){var _1vF=E(_1vE);return _1vF[0]==1?B(A(_1vB,[_1vF[1]])):[2];}));}));}]);});}],new T(function(){return B(_1vc(_1v7,_1vB));}))),new T(function(){return [1,B(_ug(_1vG,_1vB))];}));});},_1vG=function(_1vH,_1vI){return new F(function(){return _1vA(_1vI);});},_1vJ=new T(function(){return B(_1vA(_lM));}),_1vK=function(_1vL){return new F(function(){return _kO(_1vJ,_1vL);});},_1vM=new T(function(){return B(_1v1(_lM));}),_1vN=function(_1vL){return new F(function(){return _kO(_1vM,_1vL);});},_1vO=function(_1vP){return E(_1vN);},_1vQ=[0,_1vO,_1vK,_1v7,_1vG],_1vR=function(_1vS){return E(E(_1vS)[4]);},_1vT=function(_1vU,_1vV,_1vW){return new F(function(){return _1vc(new T(function(){return B(_1vR(_1vU));}),_1vW);});},_1vX=function(_1vY){return function(_mc){return new F(function(){return _kO(new T(function(){return B(_1vc(new T(function(){return B(_1vR(_1vY));}),_lM));}),_mc);});};},_1vZ=function(_1w0,_1w1){return function(_mc){return new F(function(){return _kO(new T(function(){return B(A(_1vR,[_1w0,_1w1,_lM]));}),_mc);});};},_1w2=function(_1w3){return [0,function(_1vL){return new F(function(){return _1vZ(_1w3,_1vL);});},new T(function(){return B(_1vX(_1w3));}),new T(function(){return B(_1vR(_1w3));}),function(_1w4,_1vL){return new F(function(){return _1vT(_1w3,_1w4,_1vL);});}];},_1w5=new T(function(){return B(_1w2(_1vQ));}),_1w6=function(_1w7,_1w8,_1w9){var _1wa=new T(function(){return B(_1uZ(_1w7));}),_1wb=new T(function(){return B(_1rV(_1w9));}),_1wc=new T(function(){return B(_iK(_1wb));});return function(_1wd,_1we){return new F(function(){return A(new T(function(){return B(_Ox(_1wb));}),[new T(function(){return B(A(new T(function(){return B(_Ox(_1wb));}),[new T(function(){return B(A(new T(function(){return B(_iK(_1wb));}),[[0,_1we,_1we]]));}),function(_1wf){var _1wg=new T(function(){return E(E(_1wf)[1]);}),_1wh=new T(function(){return E(E(_1wg)[2]);});return new F(function(){return A(new T(function(){return B(_Ox(_1wb));}),[new T(function(){return B(A(new T(function(){return B(_iK(_1wb));}),[[0,_5c,new T(function(){var _1wi=E(_1wg);return [0,_1wi[1],new T(function(){return [0,E(_1wh)[1]+1|0];}),_1wi[3],_1wi[4],_1wi[5],_1wi[6],_1wi[7]];})]]));}),function(_1wj){return new F(function(){return A(new T(function(){return B(_iK(_1wb));}),[[0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_1wh)[1],_9)),new T(function(){return E(E(_1wg)[1]);},1)));})],new T(function(){return E(E(_1wj)[2]);})]]);});}]);});}]));}),function(_1wk){var _1wl=new T(function(){return E(E(_1wk)[1]);});return new F(function(){return A(new T(function(){return B(_Ox(_1wb));}),[new T(function(){return B(A(_1ut,[new T(function(){return B(_1s5(new T(function(){return B(_1sw(_1wb));}),_1w9));}),function(_1wm,_1o3,_1wn){return new F(function(){return _1s9(_1wb,_1wm,_1o3,_1wn);});},function(_1wm,_1o3,_1wn){return new F(function(){return _1sl(_1wb,_1wm,_1o3,_1wn);});},function(_1o3,_1wn){return new F(function(){return _1sA(_1wb,_1o3,_1wn);});},function(_1wn){return new F(function(){return _1ss(_1wb,_1wn);});},_1ur,_1w5,_1w7,_1wl,new T(function(){return E(E(_1wk)[2]);})]));}),function(_1wo){var _1wp=E(_1wo),_1wq=_1wp[2],_1wr=E(_1wp[1]);switch(_1wr[0]){case 0:return new F(function(){return A(_1wc,[[0,[0,new T(function(){return B(A(_1wa,[_1wl,_1wd]));}),_28],_1wq]]);});break;case 1:return new F(function(){return A(_1wc,[[0,[0,new T(function(){return B(A(_1wa,[_1wl,_1wr[1]]));}),_28],_1wq]]);});break;default:var _1ws=_1wr[1];return new F(function(){return A(_1wc,[[0,[0,new T(function(){return B(A(_1wa,[_1wl,_1ws]));}),[1,_1ws]],_1wq]]);});}}]);});}]);});};},_1wt=new T(function(){return B(_1w6(_1qb,_1qm,_1rU));}),_1wu=new T(function(){return B(_CX("w_s7VY{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv a73Y} [tv]"));}),_1wv=new T(function(){return B(_CX("w_s7VZ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv a73X} [tv]"));}),_1ww=function(_1wx){return E(E(_1wx)[2]);},_1wy=function(_1wz){return E(E(_1wz)[1]);},_1wA=function(_1wB,_1wC,_1wD){return function(_1wE,_){var _1wF=B(A(_1wC,[_1wE,_])),_1wG=_1wF,_1wH=E(_1wG),_1wI=E(_1wH[1]),_1wJ=new T(function(){return B(A(new T(function(){return B(_1ww(_1wB));}),[_1wD,function(_){var _1wK=E(E(_1wE)[4]),_1wL=B(A(_1wK[1],[_])),_1wM=_1wL,_1wN=E(_1wM);if(!_1wN[0]){return _5c;}else{var _1wO=B(A(_1wK[2],[_1wN[1],_])),_1wP=_1wO;return _5c;}}]));});return [0,[0,function(_1wQ,_){var _1wR=B(A(_1wI[1],[_1wQ,_])),_1wS=_1wR,_1wT=E(_1wS),_1wU=E(_1wJ),_1wV=jsSetCB(_1wT[1],toJSStr(E(new T(function(){return B(A(_1wy,[_1wB,_1wD]));}))),_1wJ),_1wW=_1wV;return _1wT;},_1wI[2]],_1wH[2]];};},_1wX=function(_1wY,_1wZ,_1x0,_1x1,_1x2,_1x3,_1x4,_1x5,_1x6,_1x7,_1x8){return function(_1x9,_1xa){return function(_mc,_18e){return new F(function(){return _65(function(_1xb,_){var _1xc=B(A(new T(function(){return B(_1wA(_55,new T(function(){return B(_1wA(_55,new T(function(){return B(A(_1wt,[_1xa]));}),_1p));}),_1o));}),[_1xb,_])),_1xd=_1xc,_1xe=E(_1xd),_1xf=E(_1xe[1]);return [0,[0,function(_1xg,_){var _1xh=B(A(_1xf[1],[_1xg,_])),_1xi=_1xh,_1xj=B(A(_5d,[_5q,_1xi,_bP,_cf,_])),_1xk=_1xj;return _1xi;},_1xf[2]],_1xe[2]];},function(_1xl){var _1xm=new T(function(){var _1xn=B(_E9(_D1,_Ev,[0,new T(function(){return B(_e(_1xl,_1mh));}),E(_CU),E(_5c)]));if(!_1xn[0]){var _1xo=E(_1xn[1]);if(!_1xo[0]){var _1xp=E(E(_1xo[1])[1]);}else{var _1xp=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1xo[1]));})));})],_9],_9];}var _1xq=_1xp;}else{var _1xr=E(_1xn[1]);if(!_1xr[0]){var _1xs=E(E(_1xr[1])[1]);}else{var _1xs=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1xr[1]));})));})],_9],_9];}var _1xq=_1xs;}return _1xq;});return function(_mc,_18e){return new F(function(){return _65(_bA,function(_1xt,_1xu,_){return new F(function(){return _65(_bG,function(_1xv,_1xw,_){return new F(function(){return _65(_bL,function(_1xx,_1xy,_){return new F(function(){return _65(function(_1xz,_){return [0,[0,function(_1xA,_){var _1xB=B(_bX(_56,_9,_1xA,_)),_1xC=_1xB,_1xD=B(A(_5d,[_5q,_1xC,_5p,_1xt,_])),_1xE=_1xD,_1xF=B(A(_5d,[_5q,_1xC,_bP,_bM,_])),_1xG=_1xF;return _1xC;},_bS],_1xz];},function(_1xH,_1xI,_){return new F(function(){return _65(function(_1xJ,_){return [0,[0,function(_1xK,_){var _1xL=B(_5T(_63,new T(function(){return B(_1m7(_1xm));}),_1xK,_)),_1xM=_1xL,_1xN=B(A(_5d,[_5q,_1xM,_5p,_1xv,_])),_1xO=_1xN,_1xP=B(A(_5d,[_5q,_1xM,_bP,_bN,_])),_1xQ=_1xP;return _1xM;},_bS],_1xJ];},function(_1xR){return E(new T(function(){var _1xS=E(new T(function(){var _1xT=B(_1jV(_1xm,new T(function(){return E(E(_1x9)[1]);})));return _1xT[0]==0?[0,_1xT[1]]:[1,new T(function(){return B(_1gW(_1wY,_1wZ,_1x0,_1x1,_1x2,_1x3,_1x4,_1x5,_1x6,_1wu,_1wv,_1x7,_1x8,new T(function(){return E(E(_1x9)[2]);}),_1xT[1]));})];}));if(!_1xS[0]){var _1xU=function(_1xV,_){return [0,[0,function(_1xW,_){var _1xX=B(_bX(_63,function(_bB,_){return new F(function(){return _c7(new T(function(){return B(_db(_1xS[1],_9));}),_bB,_);});},_1xW,_)),_1xY=_1xX,_1xZ=B(A(_5d,[_5q,_1xY,_5p,_1xx,_])),_1y0=_1xZ,_1y1=B(A(_5d,[_5q,_1xY,_bP,_bO,_])),_1y2=_1y1;return _1xY;},_bS],_1xV];};}else{var _1y3=E(_1xS[1]);if(!_1y3[0]){var _1y4=function(_bB,_){return new F(function(){return _ch(_1xt,_bt,_bU,_bB,_);});};}else{var _1y4=function(_mc,_18e){return new F(function(){return _ch(_1xt,_bt,function(_1y5,_){return [0,[0,function(_bB,_){return new F(function(){return _5T(_56,new T(function(){var _1y6=E(_1y3[1]);return B(_bo(new T(function(){return B(_b9(_1x4,_1x3,_1x2,_1x1,_1x0,_1wY,_1wZ));}),_1y6[1],_1y6[2]));}),_bB,_);});},_bS],_1y5];},_mc,_18e);});};}var _1xU=_1y4;}return _1xU;}));},_1xI,_);});},_1xy,_);});},_1xw,_);});},_1xu,_);});},_mc,_18e);});};},_mc,_18e);});};};},_1y7=function(_1y8,_1y9,_1ya,_1yb){return new F(function(){return A(_1y8,[function(_){var _1yc=jsSet(E(_1y9)[1],toJSStr(E(_1ya)),toJSStr(E(_1yb)));return _5c;}]);});},_1yd=new T(function(){return B(unCStr("innerHTML"));}),_1ye=new T(function(){return B(unCStr("textContent"));}),_1yf=function(_1yg,_1yh,_1yi,_1yj,_1yk,_1yl,_1ym,_1yn,_1yo,_1yp,_1yq,_1yr,_1ys,_){var _1yt=B(_1j(_1ys,_1ye,_)),_1yu=_1yt,_1yv=[0,_1ys],_1yw=B(A(_1y7,[_5q,_1yv,_1yd,_9,_])),_1yx=_1yw,_1yy=E(_2l)[1],_1yz=takeMVar(_1yy),_1yA=_1yz,_1yB=B(A(_1wX,[_1yg,_1yh,_1yi,_1yj,_1yk,_1yl,_1ym,_1yn,_1yo,_1yp,_1yq,_1yr,_1yu,_1yA,_])),_1yC=_1yB,_1yD=E(_1yC),_1yE=E(_1yD[1]),_=putMVar(_1yy,_1yD[2]),_1yF=B(A(_1yE[1],[_1yv,_])),_1yG=_1yF;return _1yE[2];},_1yH=function(_){var _1yI=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1yJ=_1yI;return _5c;},_1yK=new T(function(){return B(unCStr("proofbox"));}),_1yL=function(_1yM,_1yN,_1yO,_1yP,_1yQ,_1yR,_1yS,_1yT,_1yU,_1yV,_1yW,_1yX,_){var _1yY=jsElemsByClassName(toJSStr(E(_1yK))),_1yZ=_1yY,_1z0=B((function(_1z1,_){while(1){var _1z2=E(_1z1);if(!_1z2[0]){return _5c;}else{var _1z3=B(_1yf(_1yM,_1yN,_1yO,_1yP,_1yQ,_1yR,_1yS,_1yT,_1yU,_1yV,_1yW,_1yX,E(_1z2[1])[1],_)),_1z4=_1z3;_1z1=_1z2[2];continue;}}})(_1yZ,_)),_1z5=_1z0,_1z6=jsSetTimeout(60,_1yH);return _5c;},_1z7=new T(function(){return B(unCStr("ADD"));}),_1z8=new T(function(){return B(unCStr("ADJ"));}),_1z9=[0,1],_1za=[1,_1z9],_1zb=[1,_1za],_1zc=[0,_1z9],_1zd=[1,_1zc],_1ze=new T(function(){return B(unCStr("DN"));}),_1zf=new T(function(){return B(_lv(_9,_1ze));}),_1zg=new T(function(){return B(unCStr("MTP"));}),_1zh=new T(function(){return B(unCStr("MP"));}),_1zi=new T(function(){return B(unCStr("ID"));}),_1zj=new T(function(){return B(unCStr("CD"));}),_1zk=[0,2],_1zl=[1,_1zk],_1zm=[1,_1zl],_1zn=[0,_1zk],_1zo=[1,_1zn],_1zp=function(_1zq){if(!B(_lv(_1zq,_1z7))){if(!B(_lv(_1zq,_1z8))){if(!B(_lv(_1zq,_1zj))){if(!B(_lv(_1zq,_1zi))){if(!B(_lv(_1zq,_1zh))){if(!B(_lv(_1zq,_1zg))){var _1zr=E(_1zq);return _1zr[0]==0?!E(_1zf)?[0]:E(_1zd):E(E(_1zr[1])[1])==83?E(_1zr[2])[0]==0?E(_1zd):!B(_lv(_1zr,_1ze))?[0]:E(_1zd):!B(_lv(_1zr,_1ze))?[0]:E(_1zd);}else{return E(_1zo);}}else{return E(_1zo);}}else{return E(_1zm);}}else{return E(_1zb);}}else{return E(_1zo);}}else{return E(_1zd);}},_1zs=function(_1zt){return E(E(_1zt)[2]);},_1zu=function(_1zv,_1zw,_1zx){while(1){var _1zy=E(_1zw);if(!_1zy[0]){return E(_1zx)[0]==0?1:0;}else{var _1zz=E(_1zx);if(!_1zz[0]){return 2;}else{var _1zA=B(A(_1zs,[_1zv,_1zy[1],_1zz[1]]));if(_1zA==1){_1zw=_1zy[2];_1zx=_1zz[2];continue;}else{return E(_1zA);}}}}},_1zB=function(_1zC){return E(E(_1zC)[3]);},_1zD=function(_1zE,_1zF,_1zG,_1zH,_1zI){switch(B(_1zu(_1zE,_1zF,_1zH))){case 0:return true;case 1:return new F(function(){return A(_1zB,[_1zE,_1zG,_1zI]);});break;default:return false;}},_1zJ=function(_1zK,_1zL,_1zM,_1zN){var _1zO=E(_1zM),_1zP=E(_1zN);return new F(function(){return _1zD(_1zL,_1zO[1],_1zO[2],_1zP[1],_1zP[2]);});},_1zQ=function(_1zR){return E(E(_1zR)[6]);},_1zS=function(_1zT,_1zU,_1zV,_1zW,_1zX){switch(B(_1zu(_1zT,_1zU,_1zW))){case 0:return true;case 1:return new F(function(){return A(_1zQ,[_1zT,_1zV,_1zX]);});break;default:return false;}},_1zY=function(_1zZ,_1A0,_1A1,_1A2){var _1A3=E(_1A1),_1A4=E(_1A2);return new F(function(){return _1zS(_1A0,_1A3[1],_1A3[2],_1A4[1],_1A4[2]);});},_1A5=function(_1A6){return E(E(_1A6)[5]);},_1A7=function(_1A8,_1A9,_1Aa,_1Ab,_1Ac){switch(B(_1zu(_1A8,_1A9,_1Ab))){case 0:return false;case 1:return new F(function(){return A(_1A5,[_1A8,_1Aa,_1Ac]);});break;default:return true;}},_1Ad=function(_1Ae,_1Af,_1Ag,_1Ah){var _1Ai=E(_1Ag),_1Aj=E(_1Ah);return new F(function(){return _1A7(_1Af,_1Ai[1],_1Ai[2],_1Aj[1],_1Aj[2]);});},_1Ak=function(_1Al){return E(E(_1Al)[4]);},_1Am=function(_1An,_1Ao,_1Ap,_1Aq,_1Ar){switch(B(_1zu(_1An,_1Ao,_1Aq))){case 0:return false;case 1:return new F(function(){return A(_1Ak,[_1An,_1Ap,_1Ar]);});break;default:return true;}},_1As=function(_1At,_1Au,_1Av,_1Aw){var _1Ax=E(_1Av),_1Ay=E(_1Aw);return new F(function(){return _1Am(_1Au,_1Ax[1],_1Ax[2],_1Ay[1],_1Ay[2]);});},_1Az=function(_1AA,_1AB,_1AC,_1AD,_1AE){switch(B(_1zu(_1AA,_1AB,_1AD))){case 0:return 0;case 1:return new F(function(){return A(_1zs,[_1AA,_1AC,_1AE]);});break;default:return 2;}},_1AF=function(_1AG,_1AH,_1AI,_1AJ){var _1AK=E(_1AI),_1AL=E(_1AJ);return new F(function(){return _1Az(_1AH,_1AK[1],_1AK[2],_1AL[1],_1AL[2]);});},_1AM=function(_1AN,_1AO,_1AP,_1AQ){var _1AR=E(_1AP),_1AS=_1AR[1],_1AT=_1AR[2],_1AU=E(_1AQ),_1AV=_1AU[1],_1AW=_1AU[2];switch(B(_1zu(_1AO,_1AS,_1AV))){case 0:return [0,_1AV,_1AW];case 1:return !B(A(_1zQ,[_1AO,_1AT,_1AW]))?[0,_1AS,_1AT]:[0,_1AV,_1AW];default:return [0,_1AS,_1AT];}},_1AX=function(_1AY,_1AZ,_1B0,_1B1){var _1B2=E(_1B0),_1B3=_1B2[1],_1B4=_1B2[2],_1B5=E(_1B1),_1B6=_1B5[1],_1B7=_1B5[2];switch(B(_1zu(_1AZ,_1B3,_1B6))){case 0:return [0,_1B3,_1B4];case 1:return !B(A(_1zQ,[_1AZ,_1B4,_1B7]))?[0,_1B6,_1B7]:[0,_1B3,_1B4];default:return [0,_1B6,_1B7];}},_1B8=function(_1B9,_1Ba){return [0,_1B9,function(_Yn,_Yo){return new F(function(){return _1AF(_1B9,_1Ba,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1zJ(_1B9,_1Ba,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1As(_1B9,_1Ba,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Ad(_1B9,_1Ba,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1zY(_1B9,_1Ba,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1AM(_1B9,_1Ba,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1AX(_1B9,_1Ba,_Yn,_Yo);});}];},_1Bb=function(_1Bc,_1Bd,_1Be,_1Bf){return !B(A(_1Bc,[_1Be,_1Bf]))?B(_cO(B(A(_1Bd,[_1Be,_15i])),B(A(_1Bd,[_1Bf,_15i]))))==2?false:true:false;},_1Bg=function(_1Bh,_1Bi,_1Bj,_1Bk){return new F(function(){return _1Bb(E(_1Bh)[1],_1Bi,_1Bj,_1Bk);});},_1Bl=function(_1Bm,_1Bn,_1Bo,_1Bp){return B(_cO(B(A(_1Bn,[_1Bo,_15i])),B(A(_1Bn,[_1Bp,_15i]))))==2?false:true;},_1Bq=function(_1Br,_1Bs,_1Bt,_1Bu){return !B(A(_1Br,[_1Bt,_1Bu]))?B(_cO(B(A(_1Bs,[_1Bt,_15i])),B(A(_1Bs,[_1Bu,_15i]))))==2?true:false:false;},_1Bv=function(_1Bw,_1Bx,_1By,_1Bz){return new F(function(){return _1Bq(E(_1Bw)[1],_1Bx,_1By,_1Bz);});},_1BA=function(_1BB,_1BC,_1BD,_1BE){return !B(A(_1BB,[_1BD,_1BE]))?B(_cO(B(A(_1BC,[_1BD,_15i])),B(A(_1BC,[_1BE,_15i]))))==2?true:false:true;},_1BF=function(_1BG,_1BH,_1BI,_1BJ){return new F(function(){return _1BA(E(_1BG)[1],_1BH,_1BI,_1BJ);});},_1BK=function(_1BL,_1BM,_1BN,_1BO){return !B(A(_1BL,[_1BN,_1BO]))?B(_cO(B(A(_1BM,[_1BN,_15i])),B(A(_1BM,[_1BO,_15i]))))==2?2:0:1;},_1BP=function(_1BQ,_1BR,_1BS,_1BT){return new F(function(){return _1BK(E(_1BQ)[1],_1BR,_1BS,_1BT);});},_1BU=function(_1BV,_1BW,_1BX,_1BY){return B(_cO(B(A(_1BW,[_1BX,_15i])),B(A(_1BW,[_1BY,_15i]))))==2?E(_1BX):E(_1BY);},_1BZ=function(_1C0,_1C1,_1C2,_1C3){return B(_cO(B(A(_1C1,[_1C2,_15i])),B(A(_1C1,[_1C3,_15i]))))==2?E(_1C3):E(_1C2);},_1C4=function(_1C5,_1C6){return [0,_1C5,function(_bi,_bj){return new F(function(){return _1BP(_1C5,_1C6,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Bg(_1C5,_1C6,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1BF(_1C5,_1C6,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Bv(_1C5,_1C6,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Bl(_1C5,_1C6,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1BU(_1C5,_1C6,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1BZ(_1C5,_1C6,_bi,_bj);});}];},_1C7=function(_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce){var _1Cf=function(_1Cg,_1Ch){return new F(function(){return _af(_1C8,_1C9,_1Ca,_1Cc,_1Cb,_1Ce,_1Cd,_1Cg);});};return function(_1Ci,_1Cj){var _1Ck=E(_1Ci);if(!_1Ck[0]){var _1Cl=E(_1Cj);return _1Cl[0]==0?B(_cO(B(_a1(_1Ck[1])),B(_a1(_1Cl[1]))))==2?false:true:true;}else{var _1Cm=E(_1Cj);return _1Cm[0]==0?false:B(_1zu(new T(function(){return B(_1C4(new T(function(){return B(_15n(_1Cf));}),_1Cf));}),_1Ck[1],_1Cm[1]))==2?false:true;}};},_1Cn=function(_1Co,_1Cp,_1Cq,_1Cr,_1Cs,_1Ct,_1Cu,_1Cv,_1Cw,_1Cx){return !B(A(_1C7,[_1Cp,_1Cq,_1Cr,_1Cs,_1Ct,_1Cu,_1Cv,_1Cw,_1Cx]))?E(_1Cw):E(_1Cx);},_1Cy=function(_1Cz,_1CA,_1CB,_1CC,_1CD,_1CE,_1CF,_1CG,_1CH,_1CI){return !B(A(_1C7,[_1CA,_1CB,_1CC,_1CD,_1CE,_1CF,_1CG,_1CH,_1CI]))?E(_1CI):E(_1CH);},_1CJ=function(_1CK,_1CL,_1CM,_1CN,_1CO,_1CP,_1CQ){var _1CR=function(_1CS,_1CT){return new F(function(){return _af(_1CK,_1CL,_1CM,_1CO,_1CN,_1CQ,_1CP,_1CS);});};return function(_1CU,_1CV){var _1CW=E(_1CU);if(!_1CW[0]){var _1CX=_1CW[1],_1CY=E(_1CV);if(!_1CY[0]){var _1CZ=_1CY[1];return B(_Z5(_1CX,_1CZ,_1))[0]==0?B(_cO(B(_a1(_1CX)),B(_a1(_1CZ))))==2?false:true:false;}else{return true;}}else{var _1D0=E(_1CV);return _1D0[0]==0?false:B(_1zu(new T(function(){return B(_1C4(new T(function(){return B(_15n(_1CR));}),_1CR));}),_1CW[1],_1D0[1]))==0?true:false;}};},_1D1=function(_1D2,_1D3,_1D4,_1D5,_1D6,_1D7,_1D8){var _1D9=function(_1Da,_1Db){return new F(function(){return _af(_1D2,_1D3,_1D4,_1D6,_1D5,_1D8,_1D7,_1Da);});};return function(_1Dc,_1Dd){var _1De=E(_1Dc);if(!_1De[0]){var _1Df=_1De[1],_1Dg=E(_1Dd);if(!_1Dg[0]){var _1Dh=_1Dg[1];return B(_Z5(_1Df,_1Dh,_1))[0]==0?B(_cO(B(_a1(_1Df)),B(_a1(_1Dh))))==2?true:false:false;}else{return false;}}else{var _1Di=E(_1Dd);return _1Di[0]==0?true:B(_1zu(new T(function(){return B(_1C4(new T(function(){return B(_15n(_1D9));}),_1D9));}),_1De[1],_1Di[1]))==2?true:false;}};},_1Dj=function(_1Dk,_1Dl,_1Dm,_1Dn,_1Do,_1Dp,_1Dq){var _1Dr=function(_1Ds,_1Dt){return new F(function(){return _af(_1Dk,_1Dl,_1Dm,_1Do,_1Dn,_1Dq,_1Dp,_1Ds);});};return function(_1Du,_1Dv){var _1Dw=E(_1Du);if(!_1Dw[0]){var _1Dx=_1Dw[1],_1Dy=E(_1Dv);if(!_1Dy[0]){var _1Dz=_1Dy[1];return B(_Z5(_1Dx,_1Dz,_1))[0]==0?B(_cO(B(_a1(_1Dx)),B(_a1(_1Dz))))==2?true:false:true;}else{return false;}}else{var _1DA=E(_1Dv);return _1DA[0]==0?true:B(_1zu(new T(function(){return B(_1C4(new T(function(){return B(_15n(_1Dr));}),_1Dr));}),_1Dw[1],_1DA[1]))==0?false:true;}};},_1DB=function(_1DC,_1DD,_1DE,_1DF,_1DG,_1DH,_1DI){var _1DJ=function(_1DK,_1DL){return new F(function(){return _af(_1DC,_1DD,_1DE,_1DG,_1DF,_1DI,_1DH,_1DK);});};return function(_1DM,_1DN){var _1DO=E(_1DM);if(!_1DO[0]){var _1DP=_1DO[1],_1DQ=E(_1DN);if(!_1DQ[0]){var _1DR=_1DQ[1];return B(_Z5(_1DP,_1DR,_1))[0]==0?B(_cO(B(_a1(_1DP)),B(_a1(_1DR))))==2?2:0:1;}else{return 0;}}else{var _1DS=E(_1DN);return _1DS[0]==0?2:B(_1zu(new T(function(){return B(_1C4(new T(function(){return B(_15n(_1DJ));}),_1DJ));}),_1DO[1],_1DS[1]));}};},_1DT=function(_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1){return [0,_1DU,new T(function(){return B(_1DB(_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1));}),new T(function(){return B(_1CJ(_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1));}),new T(function(){return B(_1Dj(_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1));}),new T(function(){return B(_1D1(_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1));}),new T(function(){return B(_1C7(_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1));}),function(_bi,_bj){return new F(function(){return _1Cn(_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Cy(_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_bi,_bj);});}];},_1E2=new T(function(){return B(_YJ(_Q,_u,_Q,_Q,_N,_2,_15));}),_1E3=new T(function(){return B(_1DT(_1E2,_Q,_u,_Q,_Q,_N,_15,_2));}),_1E4=new T(function(){return B(_Z3(_1E2));}),_1E5=new T(function(){return B(_1B8(_1E4,_1E3));}),_1E6=function(_1E7,_1E8,_1E9,_1Ea){var _1Eb=E(_1E9),_1Ec=E(_1Ea);return new F(function(){return _1zD(_1E8,_1Eb[1],_1Eb[2],_1Ec[1],_1Ec[2]);});},_1Ed=function(_1Ee,_1Ef,_1Eg,_1Eh){var _1Ei=E(_1Eg),_1Ej=E(_1Eh);return new F(function(){return _1zS(_1Ef,_1Ei[1],_1Ei[2],_1Ej[1],_1Ej[2]);});},_1Ek=function(_1El,_1Em,_1En,_1Eo){var _1Ep=E(_1En),_1Eq=E(_1Eo);return new F(function(){return _1A7(_1Em,_1Ep[1],_1Ep[2],_1Eq[1],_1Eq[2]);});},_1Er=function(_1Es,_1Et,_1Eu,_1Ev){var _1Ew=E(_1Eu),_1Ex=E(_1Ev);return new F(function(){return _1Am(_1Et,_1Ew[1],_1Ew[2],_1Ex[1],_1Ex[2]);});},_1Ey=function(_1Ez,_1EA,_1EB,_1EC){var _1ED=E(_1EB),_1EE=E(_1EC);return new F(function(){return _1Az(_1EA,_1ED[1],_1ED[2],_1EE[1],_1EE[2]);});},_1EF=function(_1EG,_1EH,_1EI,_1EJ){var _1EK=E(_1EI),_1EL=_1EK[1],_1EM=_1EK[2],_1EN=E(_1EJ),_1EO=_1EN[1],_1EP=_1EN[2];switch(B(_1zu(_1EH,_1EL,_1EO))){case 0:return [0,_1EO,_1EP];case 1:return !B(A(_1zQ,[_1EH,_1EM,_1EP]))?[0,_1EL,_1EM]:[0,_1EO,_1EP];default:return [0,_1EL,_1EM];}},_1EQ=function(_1ER,_1ES,_1ET,_1EU){var _1EV=E(_1ET),_1EW=_1EV[1],_1EX=_1EV[2],_1EY=E(_1EU),_1EZ=_1EY[1],_1F0=_1EY[2];switch(B(_1zu(_1ES,_1EW,_1EZ))){case 0:return [0,_1EW,_1EX];case 1:return !B(A(_1zQ,[_1ES,_1EX,_1F0]))?[0,_1EZ,_1F0]:[0,_1EW,_1EX];default:return [0,_1EZ,_1F0];}},_1F1=function(_1F2,_1F3){return [0,_1F2,function(_Yn,_Yo){return new F(function(){return _1Ey(_1F2,_1F3,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1E6(_1F2,_1F3,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Er(_1F2,_1F3,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Ek(_1F2,_1F3,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Ed(_1F2,_1F3,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1EF(_1F2,_1F3,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1EQ(_1F2,_1F3,_Yn,_Yo);});}];},_1F4=function(_1F5,_1F6){return B(_cO(_1F5,_1F6))==0?false:true;},_1F7=function(_1F8){return E(E(_1F8)[1]);},_1F9=function(_1Fa){return function(_1Fb,_1Fc){var _1Fd=E(_1Fb),_1Fe=E(_1Fc);switch(B(_1zu(new T(function(){return B(_1F1(new T(function(){return B(_Yl(new T(function(){return B(_1F7(_1Fa));})));}),_1Fa));}),_1Fd[1],_1Fe[1]))){case 0:return false;case 1:return new F(function(){return _1F4(_1Fd[2],_1Fe[2]);});break;default:return true;}};},_1Ff=new T(function(){return B(_1F9(_1E5));}),_1Fg=function(_1Fh,_1Fi,_1Fj){var _1Fk=E(_1Fh);if(_1Fk==1){var _1Fl=E(_1Fj);return _1Fl[0]==0?[0,new T(function(){return [0,1,E(E(_1Fi)),E(_1d0),E(_1d0)];}),_9,_9]:!B(A(_1Ff,[_1Fi,_1Fl[1]]))?[0,new T(function(){return [0,1,E(E(_1Fi)),E(_1d0),E(_1d0)];}),_1Fl,_9]:[0,new T(function(){return [0,1,E(E(_1Fi)),E(_1d0),E(_1d0)];}),_9,_1Fl];}else{var _1Fm=B(_1Fg(_1Fk>>1,_1Fi,_1Fj)),_1Fn=_1Fm[1],_1Fo=_1Fm[3],_1Fp=E(_1Fm[2]);if(!_1Fp[0]){return [0,_1Fn,_9,_1Fo];}else{var _1Fq=_1Fp[1],_1Fr=E(_1Fp[2]);if(!_1Fr[0]){return [0,new T(function(){return B(_1en(_1Fq,_1Fn));}),_9,_1Fo];}else{var _1Fs=_1Fr[1];if(!B(A(_1Ff,[_1Fq,_1Fs]))){var _1Ft=B(_1Fg(_1Fk>>1,_1Fs,_1Fr[2]));return [0,new T(function(){return B(_1f1(_1Fq,_1Fn,_1Ft[1]));}),_1Ft[2],_1Ft[3]];}else{return [0,_1Fn,_9,_1Fp];}}}}},_1Fu=function(_1Fv,_1Fw){return B(_cO(_1Fv,_1Fw))==2?false:true;},_1Fx=function(_1Fy){return function(_1Fz,_1FA){var _1FB=E(_1Fz),_1FC=E(_1FA);switch(B(_1zu(new T(function(){return B(_1F1(new T(function(){return B(_Yl(new T(function(){return B(_1F7(_1Fy));})));}),_1Fy));}),_1FB[1],_1FC[1]))){case 0:return true;case 1:return new F(function(){return _1Fu(_1FB[2],_1FC[2]);});break;default:return false;}};},_1FD=function(_1FE,_1FF,_1FG,_1FH){return !B(A(_1Fx,[_1FF,_1FG,_1FH]))?E(_1FG):E(_1FH);},_1FI=function(_1FJ,_1FK,_1FL,_1FM){return !B(A(_1Fx,[_1FK,_1FL,_1FM]))?E(_1FM):E(_1FL);},_1FN=function(_1FO,_1FP){return B(_cO(_1FO,_1FP))==0?true:false;},_1FQ=function(_1FR){return function(_1FS,_1FT){var _1FU=E(_1FS),_1FV=E(_1FT);switch(B(_1zu(new T(function(){return B(_1F1(new T(function(){return B(_Yl(new T(function(){return B(_1F7(_1FR));})));}),_1FR));}),_1FU[1],_1FV[1]))){case 0:return true;case 1:return new F(function(){return _1FN(_1FU[2],_1FV[2]);});break;default:return false;}};},_1FW=function(_1FX,_1FY){return B(_cO(_1FX,_1FY))==2?true:false;},_1FZ=function(_1G0){return function(_1G1,_1G2){var _1G3=E(_1G1),_1G4=E(_1G2);switch(B(_1zu(new T(function(){return B(_1F1(new T(function(){return B(_Yl(new T(function(){return B(_1F7(_1G0));})));}),_1G0));}),_1G3[1],_1G4[1]))){case 0:return false;case 1:return new F(function(){return _1FW(_1G3[2],_1G4[2]);});break;default:return true;}};},_1G5=function(_1G6){return function(_1G7,_1G8){var _1G9=E(_1G7),_1Ga=E(_1G8);switch(B(_1zu(new T(function(){return B(_1F1(new T(function(){return B(_Yl(new T(function(){return B(_1F7(_1G6));})));}),_1G6));}),_1G9[1],_1Ga[1]))){case 0:return 0;case 1:return new F(function(){return _cO(_1G9[2],_1Ga[2]);});break;default:return 2;}};},_1Gb=function(_1Gc,_1Gd){return [0,_1Gc,new T(function(){return B(_1G5(_1Gd));}),new T(function(){return B(_1FQ(_1Gd));}),new T(function(){return B(_1F9(_1Gd));}),new T(function(){return B(_1FZ(_1Gd));}),new T(function(){return B(_1Fx(_1Gd));}),function(_Yn,_Yo){return new F(function(){return _1FD(_1Gc,_1Gd,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1FI(_1Gc,_1Gd,_Yn,_Yo);});}];},_1Ge=function(_1Gf,_1Gg,_1Gh,_1Gi,_1Gj){return !B(_XX(new T(function(){return B(_Yl(_1Gf));}),_1Gg,_1Gi))?true:!B(_lv(_1Gh,_1Gj))?true:false;},_1Gk=function(_1Gl,_1Gm,_1Gn){var _1Go=E(_1Gm),_1Gp=E(_1Gn);return new F(function(){return _1Ge(_1Gl,_1Go[1],_1Go[2],_1Gp[1],_1Gp[2]);});},_1Gq=function(_1Gr){return function(_1Gs,_1Gt){var _1Gu=E(_1Gs),_1Gv=E(_1Gt);return !B(_XX(new T(function(){return B(_Yl(_1Gr));}),_1Gu[1],_1Gv[1]))?false:B(_lv(_1Gu[2],_1Gv[2]));};},_1Gw=function(_1Gx){return [0,new T(function(){return B(_1Gq(_1Gx));}),function(_Yn,_Yo){return new F(function(){return _1Gk(_1Gx,_Yn,_Yo);});}];},_1Gy=new T(function(){return B(_1Gw(_1E4));}),_1Gz=new T(function(){return B(_1Gb(_1Gy,_1E5));}),_1GA=function(_1GB,_1GC,_1GD){var _1GE=E(_1GC),_1GF=E(_1GD);if(!_1GF[0]){var _1GG=_1GF[2],_1GH=_1GF[3],_1GI=_1GF[4];switch(B(A(_1zs,[_1GB,_1GE,_1GG]))){case 0:return new F(function(){return _1d5(_1GG,B(_1GA(_1GB,_1GE,_1GH)),_1GI);});break;case 1:return [0,_1GF[1],E(_1GE),E(_1GH),E(_1GI)];default:return new F(function(){return _1dH(_1GG,_1GH,B(_1GA(_1GB,_1GE,_1GI)));});}}else{return [0,1,E(_1GE),E(_1d0),E(_1d0)];}},_1GJ=function(_1GK,_1GL){while(1){var _1GM=E(_1GL);if(!_1GM[0]){return E(_1GK);}else{var _1GN=B(_1GA(_1Gz,_1GM[1],_1GK));_1GL=_1GM[2];_1GK=_1GN;continue;}}},_1GO=function(_1GP,_1GQ,_1GR){return new F(function(){return _1GJ(B(_1GA(_1Gz,_1GQ,_1GP)),_1GR);});},_1GS=function(_1GT,_1GU,_1GV){while(1){var _1GW=E(_1GV);if(!_1GW[0]){return E(_1GU);}else{var _1GX=_1GW[1],_1GY=E(_1GW[2]);if(!_1GY[0]){return new F(function(){return _1en(_1GX,_1GU);});}else{var _1GZ=_1GY[1];if(!B(A(_1Ff,[_1GX,_1GZ]))){var _1H0=B(_1Fg(_1GT,_1GZ,_1GY[2])),_1H1=_1H0[1],_1H2=E(_1H0[3]);if(!_1H2[0]){var _1H3=_1GT<<1,_1H4=B(_1f1(_1GX,_1GU,_1H1));_1GV=_1H0[2];_1GT=_1H3;_1GU=_1H4;continue;}else{return new F(function(){return _1GO(B(_1f1(_1GX,_1GU,_1H1)),_1H2[1],_1H2[2]);});}}else{return new F(function(){return _1GO(_1GU,_1GX,_1GY);});}}}}},_1H5=function(_1H6,_1H7,_1H8,_1H9){var _1Ha=E(_1H9);if(!_1Ha[0]){return new F(function(){return _1en(_1H8,_1H7);});}else{var _1Hb=_1Ha[1];if(!B(A(_1Ff,[_1H8,_1Hb]))){var _1Hc=B(_1Fg(_1H6,_1Hb,_1Ha[2])),_1Hd=_1Hc[1],_1He=E(_1Hc[3]);if(!_1He[0]){return new F(function(){return _1GS(_1H6<<1,B(_1f1(_1H8,_1H7,_1Hd)),_1Hc[2]);});}else{return new F(function(){return _1GO(B(_1f1(_1H8,_1H7,_1Hd)),_1He[1],_1He[2]);});}}else{return new F(function(){return _1GO(_1H7,_1H8,_1Ha);});}}},_1Hf=function(_1Hg){var _1Hh=E(_1Hg);if(!_1Hh[0]){return [1];}else{var _1Hi=_1Hh[1],_1Hj=E(_1Hh[2]);if(!_1Hj[0]){return [0,1,E(E(_1Hi)),E(_1d0),E(_1d0)];}else{var _1Hk=_1Hj[1],_1Hl=_1Hj[2];if(!B(A(_1Ff,[_1Hi,_1Hk]))){return new F(function(){return _1H5(1,[0,1,E(E(_1Hi)),E(_1d0),E(_1d0)],_1Hk,_1Hl);});}else{return new F(function(){return _1GO([0,1,E(E(_1Hi)),E(_1d0),E(_1d0)],_1Hk,_1Hl);});}}}},_1Hm=new T(function(){return B(_F(0,1,_9));}),_1Hn=new T(function(){return B(unAppCStr("delta_",_1Hm));}),_1Ho=[9,_,_,_1Hn],_1Hp=[0,_1Ho],_1Hq=[1,_1Hp,_9],_1Hr=new T(function(){return B(unAppCStr("phi_",_1Hm));}),_1Hs=[3,_,_,_1Hr],_1Ht=[2,_,_1Hs],_1Hu=[1,_1Ht,_9],_1Hv=[1,_1Hu],_1Hw=[0,_1Hq,_1Hv],_1Hx=new T(function(){return B(_F(0,2,_9));}),_1Hy=new T(function(){return B(unAppCStr("phi_",_1Hx));}),_1Hz=[3,_,_,_1Hy],_1HA=[2,_,_1Hz],_1HB=[1,_1HA,_9],_1HC=[1,_1HB],_1HD=new T(function(){return B(unAppCStr("delta_",_1Hx));}),_1HE=[9,_,_,_1HD],_1HF=[0,_1HE],_1HG=[1,_1HF,_9],_1HH=[0,_1HG,_1HC],_1HI=[1,_1HH,_9],_1HJ=[1,_1Hw,_1HI],_1HK=[9,_,_PR,_1Ht,_1HA],_1HL=[1,_1HK,_9],_1HM=[1,_1HL],_1HN=[1,_1Hp,_1HG],_1HO=[0,_1HN,_1HM],_1HP=[0,_1HJ,_1HO],_1HQ=[0,_1HG,_1Hv],_1HR=[1,_1HQ,_9],_1HS=[0,_1Hq,_1HC],_1HT=[1,_1HS,_1HR],_1HU=[0,_1HT,_1HO],_1HV=[1,_1HU,_9],_1HW=[1,_1HP,_1HV],_1HX=[0,_1HW,_1z8],_1HY=[1,_1Hw,_9],_1HZ=[9,_,_Pt,_1Ht,_1HA],_1I0=[1,_1HZ,_9],_1I1=[1,_1I0],_1I2=[0,_1Hq,_1I1],_1I3=[0,_1HY,_1I2],_1I4=[9,_,_Pt,_1HA,_1Ht],_1I5=[1,_1I4,_9],_1I6=[1,_1I5],_1I7=[0,_1Hq,_1I6],_1I8=[0,_1HY,_1I7],_1I9=[1,_1I8,_9],_1Ia=[1,_1I3,_1I9],_1Ib=[0,_1Ia,_1z7],_1Ic=[1,_1Hv,_1HG],_1Id=[7,_,_Qi,_1HA],_1Ie=[1,_1Id,_9],_1If=[1,_1Ie],_1Ig=[0,_1Ic,_1If],_1Ih=[1,_1Ig,_9],_1Ii=[1,_1Hv,_1Hq],_1Ij=[0,_1Ii,_1HC],_1Ik=[1,_1Ij,_1Ih],_1Il=[7,_,_Qi,_1Ht],_1Im=[1,_1Il,_9],_1In=[1,_1Im],_1Io=[0,_1HN,_1In],_1Ip=[0,_1Ik,_1Io],_1Iq=[1,_1HS,_1Ih],_1Ir=[0,_1Iq,_1Io],_1Is=[0,_1HG,_1If],_1It=[1,_1Is,_9],_1Iu=[1,_1Ij,_1It],_1Iv=[0,_1Iu,_1Io],_1Iw=[1,_1HS,_1It],_1Ix=[0,_1Iw,_1Io],_1Iy=[1,_1Ij,_9],_1Iz=[1,_1Ig,_1Iy],_1IA=[0,_1Iz,_1Io],_1IB=[1,_1Is,_1Iy],_1IC=[0,_1IB,_1Io],_1ID=[1,_1HS,_9],_1IE=[1,_1Ig,_1ID],_1IF=[0,_1IE,_1Io],_1IG=[1,_1Is,_1ID],_1IH=[0,_1IG,_1Io],_1II=[1,_1In,_1HG],_1IJ=[0,_1II,_1If],_1IK=[1,_1In,_1Hq],_1IL=[0,_1IK,_1HC],_1IM=[1,_1IL,_9],_1IN=[1,_1IJ,_1IM],_1IO=[0,_1HN,_1Hv],_1IP=[0,_1IN,_1IO],_1IQ=[1,_1Is,_1IM],_1IR=[0,_1IQ,_1IO],_1IS=[1,_1IJ,_1ID],_1IT=[0,_1IS,_1IO],_1IU=[0,_1IG,_1IO],_1IV=[1,_1IU,_9],_1IW=[1,_1IT,_1IV],_1IX=[1,_1IR,_1IW],_1IY=[1,_1IP,_1IX],_1IZ=[1,_1IH,_1IY],_1J0=[1,_1IF,_1IZ],_1J1=[1,_1IC,_1J0],_1J2=[1,_1IA,_1J1],_1J3=[1,_1Ix,_1J2],_1J4=[1,_1Iv,_1J3],_1J5=[1,_1Ir,_1J4],_1J6=[1,_1Ip,_1J5],_1J7=[0,_1J6,_1zi],_1J8=[1,_1J7,_9],_1J9=[1,_1Ib,_1J8],_1Ja=[0,83],_1Jb=[1,_1Ja,_9],_1Jc=[0,_1Hq,_1HM],_1Jd=[1,_1Jc,_9],_1Je=[0,_1Jd,_1Hw],_1Jf=[0,_1Jd,_1HS],_1Jg=[1,_1Jf,_9],_1Jh=[1,_1Je,_1Jg],_1Ji=[0,_1Jh,_1Jb],_1Jj=[1,_1Ji,_1J9],_1Jk=[0,_1HN,_1HC],_1Jl=[0,_1HG,_1In],_1Jm=[1,_1Jl,_9],_1Jn=[1,_1I7,_1Jm],_1Jo=[0,_1Jn,_1Jk],_1Jp=[1,_1I7,_9],_1Jq=[1,_1Jl,_1Jp],_1Jr=[0,_1Jq,_1Jk],_1Js=[1,_1Jo,_9],_1Jt=[1,_1Jr,_1Js],_1Ju=[1,_1Jo,_1Jt],_1Jv=[1,_1Jo,_1Ju],_1Jw=[0,_1Jv,_1zg],_1Jx=[1,_1Jw,_1Jj],_1Jy=[9,_,_Oh,_1Ht,_1HA],_1Jz=[1,_1Jy,_9],_1JA=[1,_1Jz],_1JB=[0,_1HG,_1JA],_1JC=[1,_1JB,_9],_1JD=[1,_1Hw,_1JC],_1JE=[0,_1JD,_1Jk],_1JF=[0,_1Hq,_1JA],_1JG=[1,_1JF,_1HR],_1JH=[0,_1JG,_1Jk],_1JI=[1,_1JH,_9],_1JJ=[1,_1JE,_1JI],_1JK=[0,_1JJ,_1zh],_1JL=[1,_1JK,_1Jx],_1JM=[0,_1Iy,_1JF],_1JN=[0,_1ID,_1JF],_1JO=[1,_1JN,_9],_1JP=[1,_1JM,_1JO],_1JQ=[0,_1JP,_1zj],_1JR=[1,_1JQ,_1JL],_1JS=[1,_1HX,_1JR],_1JT=new T(function(){return B(_1Hf(_1JS));}),_1JU=[0,_1zp,_1JT],_1JV=function(_){return new F(function(){return _1yL(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1JU,_);});},_1JW=function(_){return new F(function(){return _1JV(_);});};
var hasteMain = function() {B(A(_1JW, [0]));};window.onload = hasteMain;