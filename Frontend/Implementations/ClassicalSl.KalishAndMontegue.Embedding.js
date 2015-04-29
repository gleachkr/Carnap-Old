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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr(" . "));}),_1r=function(_1s){var _1t=E(_1s);switch(_1t[0]){case 0:return E(_1t[3]);case 1:return E(_1t[3]);case 2:return E(_1t[3]);case 3:return E(_1t[3]);case 4:return E(_1t[3]);case 5:return E(_1t[3]);case 6:return E(_1t[3]);case 7:return E(_1t[3]);case 8:return E(_1t[3]);default:return E(_1t[3]);}},_1u=[0,41],_1v=[1,_1u,_9],_1w=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1x=new T(function(){return B(unCStr("base"));}),_1y=new T(function(){return B(unCStr("PatternMatchFail"));}),_1z=new T(function(){var _1A=hs_wordToWord64(18445595),_1B=_1A,_1C=hs_wordToWord64(52003073),_1D=_1C;return [0,_1B,_1D,[0,_1B,_1D,_1x,_1w,_1y],_9];}),_1E=function(_1F){return E(_1z);},_1G=function(_1H){return E(E(_1H)[1]);},_1I=function(_1J,_1K,_1L){var _1M=B(A(_1J,[_])),_1N=B(A(_1K,[_])),_1O=hs_eqWord64(_1M[1],_1N[1]),_1P=_1O;if(!E(_1P)){return [0];}else{var _1Q=hs_eqWord64(_1M[2],_1N[2]),_1R=_1Q;return E(_1R)==0?[0]:[1,_1L];}},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return _1I(B(_1G(_1U[1])),_1E,_1U[2]);});},_1V=function(_1W){return E(E(_1W)[1]);},_1X=function(_1Y,_1Z){return new F(function(){return _e(E(_1Y)[1],_1Z);});},_20=[0,44],_21=[0,93],_22=[0,91],_23=function(_24,_25,_26){var _27=E(_25);return _27[0]==0?B(unAppCStr("[]",_26)):[1,_22,new T(function(){return B(A(_24,[_27[1],new T(function(){var _28=function(_29){var _2a=E(_29);return _2a[0]==0?E([1,_21,_26]):[1,_20,new T(function(){return B(A(_24,[_2a[1],new T(function(){return B(_28(_2a[2]));})]));})];};return B(_28(_27[2]));})]));})];},_2b=function(_2c,_2d){return new F(function(){return _23(_1X,_2c,_2d);});},_2e=function(_2f,_2g,_2h){return new F(function(){return _e(E(_2g)[1],_2h);});},_2i=[0,_2e,_1V,_2b],_2j=new T(function(){return [0,_1E,_2i,_2k,_1S];}),_2k=function(_2l){return [0,_2j,_2l];},_2m=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_2n=function(_2o,_2p){return new F(function(){return die(new T(function(){return B(A(_2p,[_2o]));}));});},_2q=function(_2r,_2s){var _2t=E(_2s);if(!_2t[0]){return [0,_9,_9];}else{var _2u=_2t[1];if(!B(A(_2r,[_2u]))){return [0,_9,_2t];}else{var _2v=new T(function(){var _2w=B(_2q(_2r,_2t[2]));return [0,_2w[1],_2w[2]];});return [0,[1,_2u,new T(function(){return E(E(_2v)[1]);})],new T(function(){return E(E(_2v)[2]);})];}}},_2x=[0,32],_2y=[0,10],_2z=[1,_2y,_9],_2A=function(_2B){return E(E(_2B)[1])==124?false:true;},_2C=function(_2D,_2E){var _2F=B(_2q(_2A,B(unCStr(_2D)))),_2G=_2F[1],_2H=function(_2I,_2J){return new F(function(){return _e(_2I,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_2E,new T(function(){return B(_e(_2J,_2z));},1)));})));},1));});},_2K=E(_2F[2]);if(!_2K[0]){return new F(function(){return _2H(_2G,_9);});}else{return E(E(_2K[1])[1])==124?B(_2H(_2G,[1,_2x,_2K[2]])):B(_2H(_2G,_9));}},_2L=function(_2M){return new F(function(){return _2n([0,new T(function(){return B(_2C(_2M,_2m));})],_2k);});},_2N=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_2O=[0,44],_2P=[0,40],_2Q=function(_2R,_2S,_2T){var _2U=E(_2T);switch(_2U[0]){case 0:return E(_2N);case 1:return new F(function(){return A(_2R,[_2U[2],_9]);});break;case 2:return new F(function(){return _1r(_2U[2]);});break;case 3:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),[1,new T(function(){return B(_2Q(_2R,_2S,_2U[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[4])),_1v));})]));})]);});}},_2V=[0],_2W=function(_2X,_2Y,_2Z,_30,_31,_32,_33,_34){var _35=E(_34);switch(_35[0]){case 0:return [0];case 1:return new F(function(){return A(_30,[_35[2],_9]);});break;case 2:return new F(function(){return _1r(_35[2]);});break;case 3:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),[1,new T(function(){return B(_2Q(_30,_31,_35[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_30,_31,_35[4])),_1v));})]));})]);});break;case 7:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_1r(_35[2])),new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));},1));});break;case 9:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4]));}),_9]]]);});break;case 10:return [1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3])),new T(function(){return B(_e(B(_1r(_35[2])),new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4])),_1v));},1)));},1)));})];case 11:var _36=_35[2],_37=_35[3];return new F(function(){return A(_2Z,[_36,[1,new T(function(){return B(A(_32,[new T(function(){return B(A(_37,[_2V]));}),_36]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_37,[_2V]))));}),_9]]]);});break;default:var _38=_35[2],_39=_35[3];return new F(function(){return _e(B(_1r(_38)),new T(function(){return B(_e(B(A(_33,[new T(function(){return B(A(_39,[_2V]));}),_38])),[1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_39,[_2V])))),_1v));})]));},1));});}},_3a=function(_3b){var _3c=E(_3b);if(!_3c[0]){return [0];}else{return new F(function(){return _e(_3c[1],new T(function(){return B(_3a(_3c[2]));},1));});}},_3d=function(_3e,_3f){var _3g=E(_3f);return _3g[0]==0?[0]:[1,new T(function(){return B(A(_3e,[_3g[1]]));}),new T(function(){return B(_3d(_3e,_3g[2]));})];},_3h=function(_3i,_3j){var _3k=E(_3j);return _3k[0]==0?[0]:[1,_3i,[1,_3k[1],new T(function(){return B(_3h(_3i,_3k[2]));})]];},_3l=function(_3m,_3n,_3o,_3p,_3q,_3r,_3s,_3t){var _3u=E(_3t);if(!_3u[0]){return new F(function(){return _1r(_3u[1]);});}else{var _3v=B(_3d(function(_3w){return new F(function(){return _2W(_3m,_3n,_3o,_3q,_3p,_3r,_3s,_3w);});},_3u[1]));return _3v[0]==0?[0]:B(_3a([1,_3v[1],new T(function(){return B(_3h(_1q,_3v[2]));})]));}},_3x=function(_3y,_3z){while(1){var _3A=E(_3y);if(!_3A[0]){return E(_3z)[0]==0?true:false;}else{var _3B=E(_3z);if(!_3B[0]){return false;}else{if(E(_3A[1])[1]!=E(_3B[1])[1]){return false;}else{_3y=_3A[2];_3z=_3B[2];continue;}}}}},_3C=function(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K,_3L){return new F(function(){return _3x(B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K)),B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3L)));});},_3M=function(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V){return !B(_3C(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V))?true:false;},_3W=function(_3X,_3Y,_3Z,_40,_41,_42,_43){return [0,function(_44,_45){return new F(function(){return _3C(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});},function(_44,_45){return new F(function(){return _3M(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});}];},_46=new T(function(){return B(unCStr("wheel"));}),_47=new T(function(){return B(unCStr("mouseout"));}),_48=new T(function(){return B(unCStr("mouseover"));}),_49=new T(function(){return B(unCStr("mousemove"));}),_4a=new T(function(){return B(unCStr("blur"));}),_4b=new T(function(){return B(unCStr("focus"));}),_4c=new T(function(){return B(unCStr("change"));}),_4d=new T(function(){return B(unCStr("unload"));}),_4e=new T(function(){return B(unCStr("load"));}),_4f=new T(function(){return B(unCStr("submit"));}),_4g=new T(function(){return B(unCStr("keydown"));}),_4h=new T(function(){return B(unCStr("keyup"));}),_4i=new T(function(){return B(unCStr("keypress"));}),_4j=new T(function(){return B(unCStr("mouseup"));}),_4k=new T(function(){return B(unCStr("mousedown"));}),_4l=new T(function(){return B(unCStr("dblclick"));}),_4m=new T(function(){return B(unCStr("click"));}),_4n=function(_4o){switch(E(_4o)[0]){case 0:return E(_4e);case 1:return E(_4d);case 2:return E(_4c);case 3:return E(_4b);case 4:return E(_4a);case 5:return E(_49);case 6:return E(_48);case 7:return E(_47);case 8:return E(_4m);case 9:return E(_4l);case 10:return E(_4k);case 11:return E(_4j);case 12:return E(_4i);case 13:return E(_4h);case 14:return E(_4g);case 15:return E(_4f);default:return E(_46);}},_4p=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_4q=new T(function(){return B(unCStr("main"));}),_4r=new T(function(){return B(unCStr("EventData"));}),_4s=new T(function(){var _4t=hs_wordToWord64(3703396926),_4u=_4t,_4v=hs_wordToWord64(1660403598),_4w=_4v;return [0,_4u,_4w,[0,_4u,_4w,_4q,_4p,_4r],_9];}),_4x=[0,0],_4y=false,_4z=2,_4A=[1],_4B=new T(function(){return B(unCStr("Dynamic"));}),_4C=new T(function(){return B(unCStr("Data.Dynamic"));}),_4D=new T(function(){return B(unCStr("base"));}),_4E=new T(function(){var _4F=hs_wordToWord64(628307645),_4G=_4F,_4H=hs_wordToWord64(949574464),_4I=_4H;return [0,_4G,_4I,[0,_4G,_4I,_4D,_4C,_4B],_9];}),_4J=[0],_4K=new T(function(){return B(unCStr("OnLoad"));}),_4L=[0,_4K,_4J],_4M=[0,_4s,_4L],_4N=[0,_4E,_4M],_4O=[0],_4P=function(_){return _4O;},_4Q=function(_4R,_){return _4O;},_4S=[0,_4P,_4Q],_4T=[0,_9,_4x,_4z,_4S,_4y,_4N,_4A],_4U=function(_){var _=0,_4V=newMVar(),_4W=_4V,_=putMVar(_4W,_4T);return [0,_4W];},_4X=function(_4Y){var _4Z=B(A(_4Y,[_])),_50=_4Z;return E(_50);},_51=new T(function(){return B(_4X(_4U));}),_52=new T(function(){return B(_2L("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_53=[0,_4e,_4J],_54=[0,_4s,_53],_55=[0,_4d,_4J],_56=[0,_4s,_55],_57=[0,_4c,_4J],_58=[0,_4s,_57],_59=[0,_4b,_4J],_5a=[0,_4s,_59],_5b=[0,_4a,_4J],_5c=[0,_4s,_5b],_5d=[3],_5e=[0,_47,_5d],_5f=[0,_4s,_5e],_5g=function(_5h,_5i){switch(E(_5h)[0]){case 0:return function(_){var _5j=E(_51)[1],_5k=takeMVar(_5j),_5l=_5k,_=putMVar(_5j,new T(function(){var _5m=E(_5l);return [0,_5m[1],_5m[2],_5m[3],_5m[4],_5m[5],_54,_5m[7]];}));return new F(function(){return A(_5i,[_]);});};case 1:return function(_){var _5n=E(_51)[1],_5o=takeMVar(_5n),_5p=_5o,_=putMVar(_5n,new T(function(){var _5q=E(_5p);return [0,_5q[1],_5q[2],_5q[3],_5q[4],_5q[5],_56,_5q[7]];}));return new F(function(){return A(_5i,[_]);});};case 2:return function(_){var _5r=E(_51)[1],_5s=takeMVar(_5r),_5t=_5s,_=putMVar(_5r,new T(function(){var _5u=E(_5t);return [0,_5u[1],_5u[2],_5u[3],_5u[4],_5u[5],_58,_5u[7]];}));return new F(function(){return A(_5i,[_]);});};case 3:return function(_){var _5v=E(_51)[1],_5w=takeMVar(_5v),_5x=_5w,_=putMVar(_5v,new T(function(){var _5y=E(_5x);return [0,_5y[1],_5y[2],_5y[3],_5y[4],_5y[5],_5a,_5y[7]];}));return new F(function(){return A(_5i,[_]);});};case 4:return function(_){var _5z=E(_51)[1],_5A=takeMVar(_5z),_5B=_5A,_=putMVar(_5z,new T(function(){var _5C=E(_5B);return [0,_5C[1],_5C[2],_5C[3],_5C[4],_5C[5],_5c,_5C[7]];}));return new F(function(){return A(_5i,[_]);});};case 5:return function(_5D){return function(_){var _5E=E(_51)[1],_5F=takeMVar(_5E),_5G=_5F,_=putMVar(_5E,new T(function(){var _5H=E(_5G);return [0,_5H[1],_5H[2],_5H[3],_5H[4],_5H[5],[0,_4s,[0,_49,[2,E(_5D)]]],_5H[7]];}));return new F(function(){return A(_5i,[_]);});};};case 6:return function(_5I){return function(_){var _5J=E(_51)[1],_5K=takeMVar(_5J),_5L=_5K,_=putMVar(_5J,new T(function(){var _5M=E(_5L);return [0,_5M[1],_5M[2],_5M[3],_5M[4],_5M[5],[0,_4s,[0,_48,[2,E(_5I)]]],_5M[7]];}));return new F(function(){return A(_5i,[_]);});};};case 7:return function(_){var _5N=E(_51)[1],_5O=takeMVar(_5N),_5P=_5O,_=putMVar(_5N,new T(function(){var _5Q=E(_5P);return [0,_5Q[1],_5Q[2],_5Q[3],_5Q[4],_5Q[5],_5f,_5Q[7]];}));return new F(function(){return A(_5i,[_]);});};case 8:return function(_5R,_5S){return function(_){var _5T=E(_51)[1],_5U=takeMVar(_5T),_5V=_5U,_=putMVar(_5T,new T(function(){var _5W=E(_5V);return [0,_5W[1],_5W[2],_5W[3],_5W[4],_5W[5],[0,_4s,[0,_4m,[1,_5R,E(_5S)]]],_5W[7]];}));return new F(function(){return A(_5i,[_]);});};};case 9:return function(_5X,_5Y){return function(_){var _5Z=E(_51)[1],_60=takeMVar(_5Z),_61=_60,_=putMVar(_5Z,new T(function(){var _62=E(_61);return [0,_62[1],_62[2],_62[3],_62[4],_62[5],[0,_4s,[0,_4l,[1,_5X,E(_5Y)]]],_62[7]];}));return new F(function(){return A(_5i,[_]);});};};case 10:return function(_63,_64){return function(_){var _65=E(_51)[1],_66=takeMVar(_65),_67=_66,_=putMVar(_65,new T(function(){var _68=E(_67);return [0,_68[1],_68[2],_68[3],_68[4],_68[5],[0,_4s,[0,_4k,[1,_63,E(_64)]]],_68[7]];}));return new F(function(){return A(_5i,[_]);});};};case 11:return function(_69,_6a){return function(_){var _6b=E(_51)[1],_6c=takeMVar(_6b),_6d=_6c,_=putMVar(_6b,new T(function(){var _6e=E(_6d);return [0,_6e[1],_6e[2],_6e[3],_6e[4],_6e[5],[0,_4s,[0,_4j,[1,_69,E(_6a)]]],_6e[7]];}));return new F(function(){return A(_5i,[_]);});};};case 12:return function(_6f,_){var _6g=E(_51)[1],_6h=takeMVar(_6g),_6i=_6h,_=putMVar(_6g,new T(function(){var _6j=E(_6i);return [0,_6j[1],_6j[2],_6j[3],_6j[4],_6j[5],[0,_4s,[0,_4i,[4,_6f]]],_6j[7]];}));return new F(function(){return A(_5i,[_]);});};case 13:return function(_6k,_){var _6l=E(_51)[1],_6m=takeMVar(_6l),_6n=_6m,_=putMVar(_6l,new T(function(){var _6o=E(_6n);return [0,_6o[1],_6o[2],_6o[3],_6o[4],_6o[5],[0,_4s,[0,_4h,[4,_6k]]],_6o[7]];}));return new F(function(){return A(_5i,[_]);});};case 14:return function(_6p,_){var _6q=E(_51)[1],_6r=takeMVar(_6q),_6s=_6r,_=putMVar(_6q,new T(function(){var _6t=E(_6s);return [0,_6t[1],_6t[2],_6t[3],_6t[4],_6t[5],[0,_4s,[0,_4g,[4,_6p]]],_6t[7]];}));return new F(function(){return A(_5i,[_]);});};default:return E(_52);}},_6u=[0,_4n,_5g],_6v=function(_6w,_6x,_){var _6y=jsCreateTextNode(toJSStr(E(_6w))),_6z=_6y,_6A=jsAppendChild(_6z,E(_6x)[1]);return [0,_6z];},_6B=0,_6C=function(_6D,_6E,_6F,_6G){return new F(function(){return A(_6D,[function(_){var _6H=jsSetAttr(E(_6E)[1],toJSStr(E(_6F)),toJSStr(E(_6G)));return _6B;}]);});},_6I=[0,112],_6J=function(_6K){var _6L=new T(function(){return E(E(_6K)[2]);});return function(_6M,_){return [0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_6L)[1],_9)),new T(function(){return E(E(_6K)[1]);},1)));})],new T(function(){var _6N=E(_6K);return [0,_6N[1],new T(function(){return [0,E(_6L)[1]+1|0];}),_6N[3],_6N[4],_6N[5],_6N[6],_6N[7]];})];};},_6O=new T(function(){return B(unCStr("id"));}),_6P=function(_6Q){return E(_6Q);},_6R=new T(function(){return B(unCStr("noid"));}),_6S=function(_6T,_){return _6T;},_6U=function(_6V,_6W,_){var _6X=jsFind(toJSStr(E(_6W))),_6Y=_6X,_6Z=E(_6Y);if(!_6Z[0]){var _70=E(_51)[1],_71=takeMVar(_70),_72=_71,_73=B(A(_6V,[_72,_])),_74=_73,_75=E(_74),_=putMVar(_70,_75[2]);return E(_75[1])[2];}else{var _76=E(_6Z[1]),_77=jsClearChildren(_76[1]),_78=E(_51)[1],_79=takeMVar(_78),_7a=_79,_7b=B(A(_6V,[_7a,_])),_7c=_7b,_7d=E(_7c),_7e=E(_7d[1]),_=putMVar(_78,_7d[2]),_7f=B(A(_7e[1],[_76,_])),_7g=_7f;return _7e[2];}},_7h=new T(function(){return B(unCStr("span"));}),_7i=function(_7j,_7k,_7l,_){var _7m=jsCreateElem(toJSStr(E(_7h))),_7n=_7m,_7o=jsAppendChild(_7n,E(_7l)[1]),_7p=[0,_7n],_7q=B(A(_7j,[_7k,_7p,_])),_7r=_7q;return _7p;},_7s=function(_7t){return E(_7t);},_7u=function(_7v,_7w,_7x,_){var _7y=B(A(_6J,[_7x,_7x,_])),_7z=_7y,_7A=E(_7z),_7B=_7A[1],_7C=E(_7A[2]),_7D=_7C[2],_7E=E(_7C[4]),_7F=B(A(_7v,[[0,_7C[1],_7D,_7C[3],[0,function(_){return new F(function(){return _6U(function(_7G,_){var _7H=B(A(_7v,[new T(function(){var _7I=E(_7G);return [0,_7I[1],_7D,_7I[3],_7I[4],_7I[5],_7I[6],_7I[7]];}),_])),_7J=_7H;return [0,[0,_6S,E(E(_7J)[1])[2]],_7G];},_6R,_);});},function(_7K,_){var _7L=B(_6U(new T(function(){return B(A(_7w,[_7K]));},1),_7B,_)),_7M=_7L,_7N=E(_7M);return _7N[0]==0?_4O:B(A(_7E[2],[_7N[1],_]));}],_7C[5],_7C[6],_7C[7]],_])),_7O=_7F,_7P=E(_7O),_7Q=_7P[2],_7R=E(_7P[1]),_7S=_7R[1],_7T=E(_7R[2]);if(!_7T[0]){return [0,[0,function(_7U,_){var _7V=B(A(_7S,[_7U,_])),_7W=_7V;if(!E(E(_7x)[5])){var _7X=B(_7i(_7s,_6S,_7U,_)),_7Y=_7X,_7Z=B(A(_6C,[_6P,_7Y,_6O,_7B,_])),_80=_7Z;return _7U;}else{return _7U;}},_4O],new T(function(){var _81=E(_7Q);return [0,_81[1],_81[2],_81[3],_7E,_81[5],_81[6],_81[7]];})];}else{var _82=B(A(_7w,[_7T[1],new T(function(){var _83=E(_7Q);return [0,_83[1],_83[2],_83[3],_7E,_83[5],_83[6],_83[7]];}),_])),_84=_82,_85=E(_84),_86=E(_85[1]),_87=_86[1];return [0,[0,function(_88,_){var _89=B(A(_7S,[_88,_])),_8a=_89;if(!E(E(_7x)[5])){var _8b=B(_7i(_7s,_87,_88,_)),_8c=_8b,_8d=B(A(_6C,[_6P,_8c,_6O,_7B,_])),_8e=_8d;return _88;}else{var _8f=B(A(_87,[_88,_])),_8g=_8f;return _88;}},_86[2]],_85[2]];}},_8h=function(_8i,_8j){switch(E(_8i)[0]){case 0:switch(E(_8j)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_8j)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_8j)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_8j)[0]==3?1:2;}},_8k=new T(function(){return B(unCStr("end of input"));}),_8l=new T(function(){return B(unCStr("unexpected"));}),_8m=new T(function(){return B(unCStr("expecting"));}),_8n=new T(function(){return B(unCStr("unknown parse error"));}),_8o=new T(function(){return B(unCStr("or"));}),_8p=[0,58],_8q=[0,34],_8r=[0,41],_8s=[1,_8r,_9],_8t=function(_8u,_8v,_8w){var _8x=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_8v,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_8w,_9)),_8s));})));},1)));})));}),_8y=E(_8u);return _8y[0]==0?E(_8x):[1,_8q,new T(function(){return B(_e(_8y,new T(function(){return B(unAppCStr("\" ",_8x));},1)));})];},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C[0]){return E(_8B)[0]==0?true:false;}else{var _8D=E(_8B);if(!_8D[0]){return false;}else{if(E(_8C[1])[1]!=E(_8D[1])[1]){return false;}else{_8A=_8C[2];_8B=_8D[2];continue;}}}}},_8E=function(_8F,_8G){return !B(_8z(_8F,_8G))?true:false;},_8H=[0,_8z,_8E],_8I=function(_8J,_8K,_8L){var _8M=E(_8L);if(!_8M[0]){return E(_8K);}else{return new F(function(){return _e(_8K,new T(function(){return B(_e(_8J,new T(function(){return B(_8I(_8J,_8M[1],_8M[2]));},1)));},1));});}},_8N=function(_8O){return E(_8O)[0]==0?false:true;},_8P=new T(function(){return B(unCStr(", "));}),_8Q=function(_8R){var _8S=E(_8R);if(!_8S[0]){return [0];}else{return new F(function(){return _e(_8S[1],new T(function(){return B(_8Q(_8S[2]));},1));});}},_8T=function(_8U,_8V){while(1){var _8W=(function(_8X,_8Y){var _8Z=E(_8Y);if(!_8Z[0]){return [0];}else{var _90=_8Z[1],_91=_8Z[2];if(!B(A(_8X,[_90]))){var _92=_8X;_8V=_91;_8U=_92;return null;}else{return [1,_90,new T(function(){return B(_8T(_8X,_91));})];}}})(_8U,_8V);if(_8W!=null){return _8W;}}},_93=function(_94,_95){var _96=E(_95);return _96[0]==0?[0]:[1,_94,new T(function(){return B(_93(_96[1],_96[2]));})];},_97=function(_98,_99){while(1){var _9a=E(_99);if(!_9a[0]){return E(_98);}else{_98=_9a[1];_99=_9a[2];continue;}}},_9b=function(_9c){switch(E(_9c)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_9d=function(_9e){return E(_9e)[0]==1?true:false;},_9f=function(_9g){return E(_9g)[0]==2?true:false;},_9h=[0,10],_9i=[1,_9h,_9],_9j=function(_9k){return new F(function(){return _e(_9i,_9k);});},_9l=[0,32],_9m=function(_9n){var _9o=E(_9n);switch(_9o[0]){case 0:return E(_9o[1]);case 1:return E(_9o[1]);case 2:return E(_9o[1]);default:return E(_9o[1]);}},_9p=function(_9q){return E(E(_9q)[1]);},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v[0]){return false;}else{if(!B(A(_9p,[_9s,_9t,_9v[1]]))){_9u=_9v[2];continue;}else{return true;}}}},_9w=function(_9x,_9y){var _9z=function(_9A,_9B){while(1){var _9C=(function(_9D,_9E){var _9F=E(_9D);if(!_9F[0]){return [0];}else{var _9G=_9F[1],_9H=_9F[2];if(!B(_9r(_9x,_9G,_9E))){return [1,_9G,new T(function(){return B(_9z(_9H,[1,_9G,_9E]));})];}else{_9A=_9H;var _9I=_9E;_9B=_9I;return null;}}})(_9A,_9B);if(_9C!=null){return _9C;}}};return new F(function(){return _9z(_9y,_9);});},_9J=function(_9K,_9L,_9M,_9N,_9O,_9P){var _9Q=E(_9P);if(!_9Q[0]){return E(_9L);}else{var _9R=new T(function(){var _9S=B(_2q(_9b,_9Q));return [0,_9S[1],_9S[2]];}),_9T=new T(function(){var _9U=B(_2q(_9d,E(_9R)[2]));return [0,_9U[1],_9U[2]];}),_9V=new T(function(){return E(E(_9T)[1]);}),_9W=function(_9X,_9Y){var _9Z=E(_9Y);if(!_9Z[0]){return E(_9X);}else{var _a0=new T(function(){return B(_e(_9K,[1,_9l,new T(function(){return B(_97(_9X,_9Z));})]));}),_a1=B(_9w(_8H,B(_8T(_8N,B(_93(_9X,_9Z))))));if(!_a1[0]){return new F(function(){return _e(_9,[1,_9l,_a0]);});}else{var _a2=_a1[1],_a3=E(_a1[2]);if(!_a3[0]){return new F(function(){return _e(_a2,[1,_9l,_a0]);});}else{return new F(function(){return _e(B(_e(_a2,new T(function(){return B(_e(_8P,new T(function(){return B(_8I(_8P,_a3[1],_a3[2]));},1)));},1))),[1,_9l,_a0]);});}}}},_a4=function(_a5,_a6){var _a7=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_a6))))));if(!_a7[0]){return [0];}else{var _a8=_a7[1],_a9=_a7[2],_aa=E(_a5);return _aa[0]==0?B(_9W(_a8,_a9)):B(_e(_aa,[1,_9l,new T(function(){return B(_9W(_a8,_a9));})]));}},_ab=new T(function(){var _ac=B(_2q(_9f,E(_9T)[2]));return [0,_ac[1],_ac[2]];});return new F(function(){return _8Q(B(_3d(_9j,B(_9w(_8H,B(_8T(_8N,[1,new T(function(){if(!E(_9V)[0]){var _ad=E(E(_9R)[1]);if(!_ad[0]){var _ae=[0];}else{var _af=E(_ad[1]);switch(_af[0]){case 0:var _ag=E(_af[1]),_ah=_ag[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ag]));break;case 1:var _ai=E(_af[1]),_ah=_ai[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ai]));break;case 2:var _aj=E(_af[1]),_ah=_aj[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_aj]));break;default:var _ak=E(_af[1]),_ah=_ak[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ak]));}var _ae=_ah;}var _al=_ae,_am=_al;}else{var _am=[0];}return _am;}),[1,new T(function(){return B(_a4(_9N,_9V));}),[1,new T(function(){return B(_a4(_9M,E(_ab)[1]));}),[1,new T(function(){return B((function(_an){var _ao=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_an))))));return _ao[0]==0?[0]:B(_9W(_ao[1],_ao[2]));})(E(_ab)[2]));}),_9]]]])))))));});}},_ap=[1,_9,_9],_aq=function(_ar,_as){var _at=function(_au,_av){var _aw=E(_au);if(!_aw[0]){return E(_av);}else{var _ax=_aw[1],_ay=E(_av);if(!_ay[0]){return E(_aw);}else{var _az=_ay[1];return B(A(_ar,[_ax,_az]))==2?[1,_az,new T(function(){return B(_at(_aw,_ay[2]));})]:[1,_ax,new T(function(){return B(_at(_aw[2],_ay));})];}}},_aA=function(_aB){var _aC=E(_aB);if(!_aC[0]){return [0];}else{var _aD=E(_aC[2]);return _aD[0]==0?E(_aC):[1,new T(function(){return B(_at(_aC[1],_aD[1]));}),new T(function(){return B(_aA(_aD[2]));})];}},_aE=function(_aF){while(1){var _aG=E(_aF);if(!_aG[0]){return E(new T(function(){return B(_aE(B(_aA(_9))));}));}else{if(!E(_aG[2])[0]){return E(_aG[1]);}else{_aF=B(_aA(_aG));continue;}}}},_aH=new T(function(){return B(_aI(_9));}),_aI=function(_aJ){var _aK=E(_aJ);if(!_aK[0]){return E(_ap);}else{var _aL=_aK[1],_aM=E(_aK[2]);if(!_aM[0]){return [1,_aK,_9];}else{var _aN=_aM[1],_aO=_aM[2];if(B(A(_ar,[_aL,_aN]))==2){return new F(function(){return (function(_aP,_aQ,_aR){while(1){var _aS=(function(_aT,_aU,_aV){var _aW=E(_aV);if(!_aW[0]){return [1,[1,_aT,_aU],_aH];}else{var _aX=_aW[1];if(B(A(_ar,[_aT,_aX]))==2){_aP=_aX;var _aY=[1,_aT,_aU];_aR=_aW[2];_aQ=_aY;return null;}else{return [1,[1,_aT,_aU],new T(function(){return B(_aI(_aW));})];}}})(_aP,_aQ,_aR);if(_aS!=null){return _aS;}}})(_aN,[1,_aL,_9],_aO);});}else{return new F(function(){return (function(_aZ,_b0,_b1){while(1){var _b2=(function(_b3,_b4,_b5){var _b6=E(_b5);if(!_b6[0]){return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),_aH];}else{var _b7=_b6[1],_b8=_b6[2];switch(B(A(_ar,[_b3,_b7]))){case 0:_aZ=_b7;_b0=function(_b9){return new F(function(){return A(_b4,[[1,_b3,_b9]]);});};_b1=_b8;return null;case 1:_aZ=_b7;_b0=function(_ba){return new F(function(){return A(_b4,[[1,_b3,_ba]]);});};_b1=_b8;return null;default:return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),new T(function(){return B(_aI(_b6));})];}}})(_aZ,_b0,_b1);if(_b2!=null){return _b2;}}})(_aN,function(_bb){return [1,_aL,_bb];},_aO);});}}}};return new F(function(){return _aE(B(_aI(_as)));});},_bc=function(_bd,_be,_bf,_bg){return new F(function(){return _e(B(_8t(_bd,_be,_bf)),[1,_8p,new T(function(){return B(_9J(_8o,_8n,_8m,_8l,_8k,B(_aq(_8h,_bg))));})]);});},_bh=function(_bi){var _bj=E(_bi),_bk=E(_bj[1]);return new F(function(){return _bc(_bk[1],_bk[2],_bk[3],_bj[2]);});},_bl=function(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bt,_bu){return new F(function(){return _23(function(_bv,_bw){return new F(function(){return _e(B(_3l(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bv)),_bw);});},_bt,_bu);});},_bx=function(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bF,_bG,_bH){return new F(function(){return _e(B(_3l(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bG)),_bH);});},_bI=function(_bJ,_bK,_bL,_bM,_bN,_bO,_bP){return [0,function(_bQ,_44,_45){return new F(function(){return _bx(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_bQ,_44,_45);});},function(_45){return new F(function(){return _3l(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_45);});},function(_44,_45){return new F(function(){return _bl(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_44,_45);});}];},_bR=new T(function(){return B(unCStr(" . "));}),_bS=new T(function(){return B(unCStr(" \u2234 "));}),_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW,_bX,_bY,_bZ){var _c0=B(_3d(new T(function(){return B(_bT(_bW));}),B(_9w(_bX,_bY))));if(!_c0[0]){return new F(function(){return _e(_bS,new T(function(){return B(A(_bT,[_bW,_bZ]));},1));});}else{return new F(function(){return _e(B(_3a([1,_c0[1],new T(function(){return B(_3h(_bR,_c0[2]));})])),new T(function(){return B(_e(_bS,new T(function(){return B(A(_bT,[_bW,_bZ]));},1)));},1));});}},_c1=2,_c2=new T(function(){return B(unCStr("lined"));}),_c3=function(_c4,_){return [0,[0,_6S,[1,_c4]],_c4];},_c5=function(_c6){return function(_c7,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _c8=E(_c6);return B(_e(B(_F(0,E(_c8[2])[1],_9)),_c8[1]));})]]],_c7];};},_c9=function(_ca,_){return new F(function(){return _7u(_c3,_c5,_ca,_);});},_cb=function(_cc){return function(_cd,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _ce=E(_cc);return B(_e(B(_F(0,E(_ce[2])[1],_9)),_ce[1]));})]]],_cd];};},_cf=function(_ca,_){return new F(function(){return _7u(_c3,_cb,_ca,_);});},_cg=function(_ch){return function(_ci,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _cj=E(_ch);return B(_e(B(_F(0,E(_cj[2])[1],_9)),_cj[1]));})]]],_ci];};},_ck=function(_ca,_){return new F(function(){return _7u(_c3,_cg,_ca,_);});},_cl=new T(function(){return B(unCStr("rslt"));}),_cm=new T(function(){return B(unCStr("root"));}),_cn=new T(function(){return B(unCStr("class"));}),_co=new T(function(){return B(unCStr("analysis"));}),_cp=new T(function(){return B(unCStr("invalid"));}),_cq=function(_ca,_){return new F(function(){return _7i(_6v,_cp,_ca,_);});},_cr=[1,_6B],_cs=[0,_cq,_cr],_ct=function(_cu,_){return [0,_cs,_cu];},_cv=new T(function(){return B(unCStr("span"));}),_cw=function(_cx,_cy,_cz,_cA,_){var _cB=B(A(_cz,[_cA,_])),_cC=_cB,_cD=E(_cC),_cE=E(_cD[1]),_cF=_cE[1];return [0,[0,function(_cG,_){var _cH=jsFind(toJSStr(E(_cx))),_cI=_cH,_cJ=E(_cI);if(!_cJ[0]){return _cG;}else{var _cK=_cJ[1];switch(E(_cy)){case 0:var _cL=B(A(_cF,[_cK,_])),_cM=_cL;return _cG;case 1:var _cN=E(_cK),_cO=_cN[1],_cP=jsGetChildren(_cO),_cQ=_cP,_cR=E(_cQ);if(!_cR[0]){var _cS=B(A(_cF,[_cN,_])),_cT=_cS;return _cG;}else{var _cU=jsCreateElem(toJSStr(E(_cv))),_cV=_cU,_cW=jsAddChildBefore(_cV,_cO,E(_cR[1])[1]),_cX=B(A(_cF,[[0,_cV],_])),_cY=_cX;return _cG;}break;default:var _cZ=E(_cK),_d0=jsClearChildren(_cZ[1]),_d1=B(A(_cF,[_cZ,_])),_d2=_d1;return _cG;}}},_cE[2]],_cD[2]];},_d3=function(_d4,_d5){while(1){var _d6=E(_d4);if(!_d6[0]){return E(_d5)[0]==0?1:0;}else{var _d7=E(_d5);if(!_d7[0]){return 2;}else{var _d8=E(_d6[1])[1],_d9=E(_d7[1])[1];if(_d8!=_d9){return _d8>_d9?2:0;}else{_d4=_d6[2];_d5=_d7[2];continue;}}}}},_da=new T(function(){return B(_e(_9,_9));}),_db=function(_dc,_dd,_de,_df,_dg,_dh,_di,_dj){var _dk=[0,_dc,_dd,_de],_dl=function(_dm){var _dn=E(_df);if(!_dn[0]){var _do=E(_dj);if(!_do[0]){switch(B(_d3(_dc,_dg))){case 0:return [0,[0,_dg,_dh,_di],_9];case 1:return _dd>=_dh?_dd!=_dh?[0,_dk,_9]:_de>=_di?_de!=_di?[0,_dk,_9]:[0,_dk,_da]:[0,[0,_dg,_dh,_di],_9]:[0,[0,_dg,_dh,_di],_9];default:return [0,_dk,_9];}}else{return [0,[0,_dg,_dh,_di],_do];}}else{switch(B(_d3(_dc,_dg))){case 0:return [0,[0,_dg,_dh,_di],_dj];case 1:return _dd>=_dh?_dd!=_dh?[0,_dk,_dn]:_de>=_di?_de!=_di?[0,_dk,_dn]:[0,_dk,new T(function(){return B(_e(_dn,_dj));})]:[0,[0,_dg,_dh,_di],_dj]:[0,[0,_dg,_dh,_di],_dj];default:return [0,_dk,_dn];}}};if(!E(_dj)[0]){var _dp=E(_df);return _dp[0]==0?B(_dl(_)):[0,_dk,_dp];}else{return new F(function(){return _dl(_);});}},_dq=function(_dr,_ds){while(1){var _dt=E(_dr);if(!_dt[0]){return E(_ds);}else{_dr=_dt[2];var _du=[1,_dt[1],_ds];_ds=_du;continue;}}},_dv=new T(function(){return B(_dq(_9,_9));}),_dw=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_dx=new T(function(){return B(err(_dw));}),_dy=function(_dz,_dA,_dB,_dC,_dD){var _dE=function(_dF,_dG,_dH){var _dI=[1,_dG,_dF];return new F(function(){return A(_dz,[_dH,new T(function(){var _dJ=E(_dF);return function(_dK,_dL,_dM){return new F(function(){return _dE(_dI,_dK,_dL);});};}),_dC,_dx,function(_dN){return new F(function(){return A(_dB,[new T(function(){return B(_dq(_dI,_9));}),_dH,new T(function(){var _dO=E(E(_dH)[2]),_dP=E(_dN),_dQ=E(_dP[1]),_dR=B(_db(_dQ[1],_dQ[2],_dQ[3],_dP[2],_dO[1],_dO[2],_dO[3],_9));return [0,E(_dR[1]),_dR[2]];})]);});}]);});};return new F(function(){return A(_dz,[_dA,function(_dS,_dT,_dU){return new F(function(){return _dE(_9,_dS,_dT);});},_dC,_dx,function(_dV){return new F(function(){return A(_dD,[_dv,_dA,new T(function(){var _dW=E(E(_dA)[2]),_dX=E(_dV),_dY=E(_dX[1]),_dZ=B(_db(_dY[1],_dY[2],_dY[3],_dX[2],_dW[1],_dW[2],_dW[3],_9));return [0,E(_dZ[1]),_dZ[2]];})]);});}]);});},_e0=function(_e1,_e2){var _e3=E(_e1),_e4=E(_e3[1]),_e5=E(_e2),_e6=E(_e5[1]),_e7=B(_db(_e4[1],_e4[2],_e4[3],_e3[2],_e6[1],_e6[2],_e6[3],_e5[2]));return [0,E(_e7[1]),_e7[2]];},_e8=function(_e9,_ea,_eb,_ec,_ed,_ee){var _ef=function(_eg,_eh,_ei,_ej,_ek){return new F(function(){return _dy(_e9,_eh,function(_el,_em,_en){return new F(function(){return A(_ei,[[1,_eg,_el],_em,new T(function(){var _eo=E(E(_em)[2]),_ep=E(_en),_eq=E(_ep[1]),_er=B(_db(_eq[1],_eq[2],_eq[3],_ep[2],_eo[1],_eo[2],_eo[3],_9));return [0,E(_er[1]),_er[2]];})]);});},_ej,function(_es,_et,_eu){return new F(function(){return A(_ek,[[1,_eg,_es],_et,new T(function(){var _ev=E(E(_et)[2]),_ew=E(_eu),_ex=E(_ew[1]),_ey=B(_db(_ex[1],_ex[2],_ex[3],_ew[2],_ev[1],_ev[2],_ev[3],_9));return [0,E(_ey[1]),_ey[2]];})]);});});});};return new F(function(){return A(_e9,[_ea,function(_ez,_eA,_eB){return new F(function(){return _ef(_ez,_eA,_eb,_ec,function(_eC,_eD,_eE){return new F(function(){return A(_eb,[_eC,_eD,new T(function(){return B(_e0(_eB,_eE));})]);});});});},_ec,function(_eF,_eG,_eH){return new F(function(){return _ef(_eF,_eG,_eb,_ec,function(_eI,_eJ,_eK){return new F(function(){return A(_ed,[_eI,_eJ,new T(function(){return B(_e0(_eH,_eK));})]);});});});},_ee]);});},_eL=function(_eM,_eN,_eO,_eP,_eQ){var _eR=function(_eS,_eT){return new F(function(){return A(_eM,[_eT,new T(function(){var _eU=E(_eS);return function(_eV,_eW,_eX){return new F(function(){return _eR(_9,_eW);});};}),_eP,_dx,function(_eY){return new F(function(){return A(_eO,[_6B,_eT,new T(function(){var _eZ=E(E(_eT)[2]),_f0=E(_eY),_f1=E(_f0[1]),_f2=B(_db(_f1[1],_f1[2],_f1[3],_f0[2],_eZ[1],_eZ[2],_eZ[3],_9));return [0,E(_f2[1]),_f2[2]];})]);});}]);});};return new F(function(){return A(_eM,[_eN,function(_f3,_f4,_f5){return new F(function(){return _eR(_9,_f4);});},_eP,_dx,function(_f6){return new F(function(){return A(_eQ,[_6B,_eN,new T(function(){var _f7=E(E(_eN)[2]),_f8=E(_f6),_f9=E(_f8[1]),_fa=B(_db(_f9[1],_f9[2],_f9[3],_f8[2],_f7[1],_f7[2],_f7[3],_9));return [0,E(_fa[1]),_fa[2]];})]);});}]);});},_fb=function(_fc,_fd,_fe,_ff,_fg,_fh,_fi){var _fj=function(_fk,_fl,_fm,_fn,_fo){var _fp=[1,_fk,_9],_fq=function(_fr,_fs,_ft,_fu){return new F(function(){return _fb(_fc,_fd,_fr,function(_fv,_fw,_fx){return new F(function(){return A(_fs,[[1,_fk,_fv],_fw,new T(function(){var _fy=E(E(_fw)[2]),_fz=E(_fx),_fA=E(_fz[1]),_fB=B(_db(_fA[1],_fA[2],_fA[3],_fz[2],_fy[1],_fy[2],_fy[3],_9));return [0,E(_fB[1]),_fB[2]];})]);});},_ft,function(_fC,_fD,_fE){return new F(function(){return A(_fu,[[1,_fk,_fC],_fD,new T(function(){var _fF=E(E(_fD)[2]),_fG=E(_fE),_fH=E(_fG[1]),_fI=B(_db(_fH[1],_fH[2],_fH[3],_fG[2],_fF[1],_fF[2],_fF[3],_9));return [0,E(_fI[1]),_fI[2]];})]);});},function(_fJ){return new F(function(){return A(_fu,[_fp,_fr,new T(function(){var _fK=E(E(_fr)[2]),_fL=_fK[1],_fM=_fK[2],_fN=_fK[3],_fO=E(_fJ),_fP=E(_fO[1]),_fQ=B(_db(_fP[1],_fP[2],_fP[3],_fO[2],_fL,_fM,_fN,_9)),_fR=E(_fQ[1]),_fS=B(_db(_fR[1],_fR[2],_fR[3],_fQ[2],_fL,_fM,_fN,_9));return [0,E(_fS[1]),_fS[2]];})]);});});});};return new F(function(){return A(_fd,[_fl,function(_fT,_fU,_fV){return new F(function(){return _fq(_fU,_fm,_fn,function(_fW,_fX,_fY){return new F(function(){return A(_fm,[_fW,_fX,new T(function(){return B(_e0(_fV,_fY));})]);});});});},_fn,function(_fZ,_g0,_g1){return new F(function(){return _fq(_g0,_fm,_fn,function(_g2,_g3,_g4){return new F(function(){return A(_fo,[_g2,_g3,new T(function(){return B(_e0(_g1,_g4));})]);});});});},function(_g5){return new F(function(){return A(_fo,[_fp,_fl,new T(function(){var _g6=E(E(_fl)[2]),_g7=E(_g5),_g8=E(_g7[1]),_g9=B(_db(_g8[1],_g8[2],_g8[3],_g7[2],_g6[1],_g6[2],_g6[3],_9));return [0,E(_g9[1]),_g9[2]];})]);});}]);});};return new F(function(){return A(_fc,[_fe,function(_ga,_gb,_gc){return new F(function(){return _fj(_ga,_gb,_ff,_fg,function(_gd,_ge,_gf){return new F(function(){return A(_ff,[_gd,_ge,new T(function(){return B(_e0(_gc,_gf));})]);});});});},_fg,function(_gg,_gh,_gi){return new F(function(){return _fj(_gg,_gh,_ff,_fg,function(_gj,_gk,_gl){return new F(function(){return A(_fh,[_gj,_gk,new T(function(){return B(_e0(_gi,_gl));})]);});});});},_fi]);});},_gm=function(_gn,_go){return new F(function(){return A(_go,[_gn]);});},_gp=[0,34],_gq=[1,_gp,_9],_gr=[0,E(_9)],_gs=[1,_gr,_9],_gt=function(_gu,_gv){var _gw=_gu%_gv;if(_gu<=0){if(_gu>=0){return E(_gw);}else{if(_gv<=0){return E(_gw);}else{var _gx=E(_gw);return _gx==0?0:_gx+_gv|0;}}}else{if(_gv>=0){if(_gu>=0){return E(_gw);}else{if(_gv<=0){return E(_gw);}else{var _gy=E(_gw);return _gy==0?0:_gy+_gv|0;}}}else{var _gz=E(_gw);return _gz==0?0:_gz+_gv|0;}}},_gA=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_gB=new T(function(){return B(err(_gA));}),_gC=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_gD=new T(function(){return B(err(_gC));}),_gE=function(_gF,_gG){while(1){var _gH=E(_gF);if(!_gH[0]){return E(_gD);}else{var _gI=E(_gG);if(!_gI){return E(_gH[1]);}else{_gF=_gH[2];_gG=_gI-1|0;continue;}}}},_gJ=new T(function(){return B(unCStr("ACK"));}),_gK=new T(function(){return B(unCStr("BEL"));}),_gL=new T(function(){return B(unCStr("BS"));}),_gM=new T(function(){return B(unCStr("SP"));}),_gN=[1,_gM,_9],_gO=new T(function(){return B(unCStr("US"));}),_gP=[1,_gO,_gN],_gQ=new T(function(){return B(unCStr("RS"));}),_gR=[1,_gQ,_gP],_gS=new T(function(){return B(unCStr("GS"));}),_gT=[1,_gS,_gR],_gU=new T(function(){return B(unCStr("FS"));}),_gV=[1,_gU,_gT],_gW=new T(function(){return B(unCStr("ESC"));}),_gX=[1,_gW,_gV],_gY=new T(function(){return B(unCStr("SUB"));}),_gZ=[1,_gY,_gX],_h0=new T(function(){return B(unCStr("EM"));}),_h1=[1,_h0,_gZ],_h2=new T(function(){return B(unCStr("CAN"));}),_h3=[1,_h2,_h1],_h4=new T(function(){return B(unCStr("ETB"));}),_h5=[1,_h4,_h3],_h6=new T(function(){return B(unCStr("SYN"));}),_h7=[1,_h6,_h5],_h8=new T(function(){return B(unCStr("NAK"));}),_h9=[1,_h8,_h7],_ha=new T(function(){return B(unCStr("DC4"));}),_hb=[1,_ha,_h9],_hc=new T(function(){return B(unCStr("DC3"));}),_hd=[1,_hc,_hb],_he=new T(function(){return B(unCStr("DC2"));}),_hf=[1,_he,_hd],_hg=new T(function(){return B(unCStr("DC1"));}),_hh=[1,_hg,_hf],_hi=new T(function(){return B(unCStr("DLE"));}),_hj=[1,_hi,_hh],_hk=new T(function(){return B(unCStr("SI"));}),_hl=[1,_hk,_hj],_hm=new T(function(){return B(unCStr("SO"));}),_hn=[1,_hm,_hl],_ho=new T(function(){return B(unCStr("CR"));}),_hp=[1,_ho,_hn],_hq=new T(function(){return B(unCStr("FF"));}),_hr=[1,_hq,_hp],_hs=new T(function(){return B(unCStr("VT"));}),_ht=[1,_hs,_hr],_hu=new T(function(){return B(unCStr("LF"));}),_hv=[1,_hu,_ht],_hw=new T(function(){return B(unCStr("HT"));}),_hx=[1,_hw,_hv],_hy=[1,_gL,_hx],_hz=[1,_gK,_hy],_hA=[1,_gJ,_hz],_hB=new T(function(){return B(unCStr("ENQ"));}),_hC=[1,_hB,_hA],_hD=new T(function(){return B(unCStr("EOT"));}),_hE=[1,_hD,_hC],_hF=new T(function(){return B(unCStr("ETX"));}),_hG=[1,_hF,_hE],_hH=new T(function(){return B(unCStr("STX"));}),_hI=[1,_hH,_hG],_hJ=new T(function(){return B(unCStr("SOH"));}),_hK=[1,_hJ,_hI],_hL=new T(function(){return B(unCStr("NUL"));}),_hM=[1,_hL,_hK],_hN=[0,92],_hO=new T(function(){return B(unCStr("\\DEL"));}),_hP=new T(function(){return B(unCStr("\\a"));}),_hQ=new T(function(){return B(unCStr("\\\\"));}),_hR=new T(function(){return B(unCStr("\\SO"));}),_hS=new T(function(){return B(unCStr("\\r"));}),_hT=new T(function(){return B(unCStr("\\f"));}),_hU=new T(function(){return B(unCStr("\\v"));}),_hV=new T(function(){return B(unCStr("\\n"));}),_hW=new T(function(){return B(unCStr("\\t"));}),_hX=new T(function(){return B(unCStr("\\b"));}),_hY=function(_hZ,_i0){if(_hZ<=127){var _i1=E(_hZ);switch(_i1){case 92:return new F(function(){return _e(_hQ,_i0);});break;case 127:return new F(function(){return _e(_hO,_i0);});break;default:if(_i1<32){var _i2=E(_i1);switch(_i2){case 7:return new F(function(){return _e(_hP,_i0);});break;case 8:return new F(function(){return _e(_hX,_i0);});break;case 9:return new F(function(){return _e(_hW,_i0);});break;case 10:return new F(function(){return _e(_hV,_i0);});break;case 11:return new F(function(){return _e(_hU,_i0);});break;case 12:return new F(function(){return _e(_hT,_i0);});break;case 13:return new F(function(){return _e(_hS,_i0);});break;case 14:return new F(function(){return _e(_hR,new T(function(){var _i3=E(_i0);if(!_i3[0]){var _i4=[0];}else{var _i4=E(E(_i3[1])[1])==72?B(unAppCStr("\\&",_i3)):E(_i3);}return _i4;},1));});break;default:return new F(function(){return _e([1,_hN,new T(function(){var _i5=_i2;return _i5>=0?B(_gE(_hM,_i5)):E(_gB);})],_i0);});}}else{return [1,[0,_i1],_i0];}}}else{return [1,_hN,new T(function(){var _i6=jsShowI(_hZ),_i7=_i6;return B(_e(fromJSStr(_i7),new T(function(){var _i8=E(_i0);if(!_i8[0]){var _i9=[0];}else{var _ia=E(_i8[1])[1];if(_ia<48){var _ib=E(_i8);}else{var _ib=_ia>57?E(_i8):B(unAppCStr("\\&",_i8));}var _ic=_ib,_id=_ic,_i9=_id;}return _i9;},1)));})];}},_ie=new T(function(){return B(unCStr("\\\""));}),_if=function(_ig,_ih){var _ii=E(_ig);if(!_ii[0]){return E(_ih);}else{var _ij=_ii[2],_ik=E(E(_ii[1])[1]);if(_ik==34){return new F(function(){return _e(_ie,new T(function(){return B(_if(_ij,_ih));},1));});}else{return new F(function(){return _hY(_ik,new T(function(){return B(_if(_ij,_ih));}));});}}},_il=function(_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv){var _iw=[0,_iq,_ir,_is];return new F(function(){return A(_im,[new T(function(){return B(A(_in,[_ip]));}),function(_ix){var _iy=E(_ix);if(!_iy[0]){return E(new T(function(){return B(A(_iv,[[0,E(_iw),_gs]]));}));}else{var _iz=E(_iy[1]),_iA=_iz[1],_iB=_iz[2];if(!B(A(_io,[_iA]))){return new F(function(){return A(_iv,[[0,E(_iw),[1,[0,E([1,_gp,new T(function(){return B(_if([1,_iA,_9],_gq));})])],_9]]]);});}else{var _iC=E(_iA);switch(E(_iC[1])){case 9:var _iD=[0,_iq,_ir,(_is+8|0)-B(_gt(_is-1|0,8))|0];break;case 10:var _iD=E([0,_iq,_ir+1|0,1]);break;default:var _iD=E([0,_iq,_ir,_is+1|0]);}var _iE=_iD,_iF=[0,E(_iE),_9],_iG=[0,_iB,E(_iE),E(_it)];return new F(function(){return A(_iu,[_iC,_iG,_iF]);});}}}]);});},_iH=function(_iI,_iJ){return E(_iI)[1]!=E(_iJ)[1];},_iK=function(_iL,_iM){return E(_iL)[1]==E(_iM)[1];},_iN=[0,_iK,_iH],_iO=new T(function(){return B(unCStr(" 	"));}),_iP=function(_iQ){return new F(function(){return _9r(_iN,_iQ,_iO);});},_iR=function(_iS,_iT){return E(_iT);},_iU=function(_iV){return new F(function(){return err(_iV);});},_iW=function(_iX){return E(_iX);},_iY=[0,_gm,_iR,_iW,_iU],_iZ=function(_j0){return E(E(_j0)[3]);},_j1=function(_j2,_j3){var _j4=E(_j3);return _j4[0]==0?B(A(_iZ,[_j2,_4O])):B(A(_iZ,[_j2,[1,[0,_j4[1],_j4[2]]]]));},_j5=function(_j6){return new F(function(){return _j1(_iY,_j6);});},_j7=function(_j8,_j9,_ja,_jb,_jc){var _jd=E(_j8),_je=E(_jd[2]);return new F(function(){return _il(_gm,_j5,_iP,_jd[1],_je[1],_je[2],_je[3],_jd[3],_j9,_jc);});},_jf=function(_jg){return [2,E(E(_jg))];},_jh=function(_ji,_jj){switch(E(_ji)[0]){case 0:switch(E(_jj)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_jj)[0]==1?false:true;case 2:return E(_jj)[0]==2?false:true;default:return E(_jj)[0]==3?false:true;}},_jk=[2,E(_9)],_jl=function(_jm){return new F(function(){return _jh(_jk,_jm);});},_jn=function(_jo,_jp,_jq){var _jr=E(_jq);if(!_jr[0]){return [0,_jo,[1,_jk,new T(function(){return B(_8T(_jl,_jp));})]];}else{var _js=_jr[1],_jt=E(_jr[2]);if(!_jt[0]){var _ju=new T(function(){return [2,E(E(_js))];});return [0,_jo,[1,_ju,new T(function(){return B(_8T(function(_jm){return new F(function(){return _jh(_ju,_jm);});},_jp));})]];}else{var _jv=new T(function(){return [2,E(E(_js))];}),_jw=function(_jx){var _jy=E(_jx);if(!_jy[0]){return [0,_jo,[1,_jv,new T(function(){return B(_8T(function(_jm){return new F(function(){return _jh(_jv,_jm);});},_jp));})]];}else{var _jz=B(_jw(_jy[2]));return [0,_jz[1],[1,new T(function(){return B(_jf(_jy[1]));}),_jz[2]]];}};return new F(function(){return (function(_jA,_jB){var _jC=B(_jw(_jB));return [0,_jC[1],[1,new T(function(){return B(_jf(_jA));}),_jC[2]]];})(_jt[1],_jt[2]);});}}},_jD=function(_jE,_jF){var _jG=E(_jE),_jH=B(_jn(_jG[1],_jG[2],_jF));return [0,E(_jH[1]),_jH[2]];},_jI=function(_jJ,_jK,_jL,_jM,_jN,_jO,_jP){return new F(function(){return A(_jJ,[_jL,_jM,_jN,function(_jQ,_jR,_jS){return new F(function(){return A(_jO,[_jQ,_jR,new T(function(){var _jT=E(_jS),_jU=E(_jT[2]);if(!_jU[0]){var _jV=E(_jT);}else{var _jW=B(_jn(_jT[1],_jU,_jK)),_jV=[0,E(_jW[1]),_jW[2]];}var _jX=_jV;return _jX;})]);});},function(_jY){return new F(function(){return A(_jP,[new T(function(){return B(_jD(_jY,_jK));})]);});}]);});},_jZ=new T(function(){return B(unCStr("digit"));}),_k0=[1,_jZ,_9],_k1=function(_k2){return new F(function(){return _j1(_iY,_k2);});},_k3=function(_k4){var _k5=E(_k4)[1];return _k5<48?false:_k5<=57;},_k6=function(_k7,_k8,_k9,_ka,_kb){var _kc=E(_k7),_kd=E(_kc[2]);return new F(function(){return _il(_gm,_k1,_k3,_kc[1],_kd[1],_kd[2],_kd[3],_kc[3],_k8,_kb);});},_ke=function(_kf,_kg,_kh,_ki,_kj){return new F(function(){return _jI(_k6,_k0,_kf,_kg,_kh,_ki,_kj);});},_kk=function(_kl,_km,_kn,_ko,_kp){return new F(function(){return _e8(_ke,_kl,_km,_kn,_ko,_kp);});},_kq=function(_kr){return [0,_kr,function(_jm){return new F(function(){return _j1(_kr,_jm);});}];},_ks=new T(function(){return B(_kq(_iY));}),_kt=function(_ku,_kv){return function(_kw,_kx,_ky,_kz,_kA){return new F(function(){return _jI(function(_kB,_kC,_kD,_kE,_kF){var _kG=E(_ku),_kH=E(_kB),_kI=E(_kH[2]);return new F(function(){return _il(E(_kG[1])[1],_kG[2],function(_kJ){return new F(function(){return _iK(_kJ,_kv);});},_kH[1],_kI[1],_kI[2],_kI[3],_kH[3],_kC,_kF);});},[1,[1,_gp,new T(function(){return B(_if([1,_kv,_9],_gq));})],_9],_kw,_kx,_ky,_kz,_kA);});};},_kK=[0,44],_kL=new T(function(){return B(_kt(_ks,_kK));}),_kM=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_kN=new T(function(){return B(err(_kM));}),_kO=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kP=new T(function(){return B(err(_kO));}),_kQ=new T(function(){return B(_2L("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_kR=function(_kS,_kT){while(1){var _kU=(function(_kV,_kW){var _kX=E(_kV);switch(_kX[0]){case 0:var _kY=E(_kW);if(!_kY[0]){return [0];}else{_kS=B(A(_kX[1],[_kY[1]]));_kT=_kY[2];return null;}break;case 1:var _kZ=B(A(_kX[1],[_kW])),_l0=_kW;_kS=_kZ;_kT=_l0;return null;case 2:return [0];case 3:return [1,[0,_kX[1],_kW],new T(function(){return B(_kR(_kX[2],_kW));})];default:return E(_kX[1]);}})(_kS,_kT);if(_kU!=null){return _kU;}}},_l1=function(_l2,_l3){var _l4=function(_l5){var _l6=E(_l3);if(_l6[0]==3){return [3,_l6[1],new T(function(){return B(_l1(_l2,_l6[2]));})];}else{var _l7=E(_l2);if(_l7[0]==2){return E(_l6);}else{var _l8=E(_l6);if(_l8[0]==2){return E(_l7);}else{var _l9=function(_la){var _lb=E(_l8);if(_lb[0]==4){return [1,function(_lc){return [4,new T(function(){return B(_e(B(_kR(_l7,_lc)),_lb[1]));})];}];}else{var _ld=E(_l7);if(_ld[0]==1){var _le=_ld[1],_lf=E(_lb);return _lf[0]==0?[1,function(_lg){return new F(function(){return _l1(B(A(_le,[_lg])),_lf);});}]:[1,function(_lh){return new F(function(){return _l1(B(A(_le,[_lh])),new T(function(){return B(A(_lf[1],[_lh]));}));});}];}else{var _li=E(_lb);return _li[0]==0?E(_kQ):[1,function(_lj){return new F(function(){return _l1(_ld,new T(function(){return B(A(_li[1],[_lj]));}));});}];}}},_lk=E(_l7);switch(_lk[0]){case 1:var _ll=E(_l8);if(_ll[0]==4){return [1,function(_lm){return [4,new T(function(){return B(_e(B(_kR(B(A(_lk[1],[_lm])),_lm)),_ll[1]));})];}];}else{return new F(function(){return _l9(_);});}break;case 4:var _ln=_lk[1],_lo=E(_l8);switch(_lo[0]){case 0:return [1,function(_lp){return [4,new T(function(){return B(_e(_ln,new T(function(){return B(_kR(_lo,_lp));},1)));})];}];case 1:return [1,function(_lq){return [4,new T(function(){return B(_e(_ln,new T(function(){return B(_kR(B(A(_lo[1],[_lq])),_lq));},1)));})];}];default:return [4,new T(function(){return B(_e(_ln,_lo[1]));})];}break;default:return new F(function(){return _l9(_);});}}}}},_lr=E(_l2);switch(_lr[0]){case 0:var _ls=E(_l3);if(!_ls[0]){return [0,function(_lt){return new F(function(){return _l1(B(A(_lr[1],[_lt])),new T(function(){return B(A(_ls[1],[_lt]));}));});}];}else{return new F(function(){return _l4(_);});}break;case 3:return [3,_lr[1],new T(function(){return B(_l1(_lr[2],_l3));})];default:return new F(function(){return _l4(_);});}},_lu=[0,41],_lv=[1,_lu,_9],_lw=[0,40],_lx=[1,_lw,_9],_ly=function(_lz,_lA){var _lB=E(_lz);switch(_lB[0]){case 0:return [0,function(_lC){return new F(function(){return _ly(B(A(_lB[1],[_lC])),_lA);});}];case 1:return [1,function(_lD){return new F(function(){return _ly(B(A(_lB[1],[_lD])),_lA);});}];case 2:return [2];case 3:return new F(function(){return _l1(B(A(_lA,[_lB[1]])),new T(function(){return B(_ly(_lB[2],_lA));}));});break;default:var _lE=function(_lF){var _lG=E(_lF);if(!_lG[0]){return [0];}else{var _lH=E(_lG[1]);return new F(function(){return _e(B(_kR(B(A(_lA,[_lH[1]])),_lH[2])),new T(function(){return B(_lE(_lG[2]));},1));});}},_lI=B(_lE(_lB[1]));return _lI[0]==0?[2]:[4,_lI];}},_lJ=[2],_lK=function(_lL){return [3,_lL,_lJ];},_lM=function(_lN,_lO){var _lP=E(_lN);if(!_lP){return new F(function(){return A(_lO,[_6B]);});}else{return [0,function(_lQ){return E(new T(function(){return B(_lM(_lP-1|0,_lO));}));}];}},_lR=function(_lS,_lT,_lU){return function(_lV){return new F(function(){return A(function(_lW,_lX,_lY){while(1){var _lZ=(function(_m0,_m1,_m2){var _m3=E(_m0);switch(_m3[0]){case 0:var _m4=E(_m1);if(!_m4[0]){return E(_lT);}else{_lW=B(A(_m3[1],[_m4[1]]));_lX=_m4[2];var _m5=_m2+1|0;_lY=_m5;return null;}break;case 1:var _m6=B(A(_m3[1],[_m1])),_m7=_m1,_m5=_m2;_lW=_m6;_lX=_m7;_lY=_m5;return null;case 2:return E(_lT);case 3:return function(_m8){return new F(function(){return _lM(_m2,function(_m9){return E(new T(function(){return B(_ly(_m3,_m8));}));});});};default:return function(_ma){return new F(function(){return _ly(_m3,_ma);});};}})(_lW,_lX,_lY);if(_lZ!=null){return _lZ;}}},[new T(function(){return B(A(_lS,[_lK]));}),_lV,0,_lU]);});};},_mb=function(_mc){return new F(function(){return A(_mc,[_9]);});},_md=function(_me,_mf){var _mg=function(_mh){var _mi=E(_mh);if(!_mi[0]){return E(_mb);}else{var _mj=_mi[1];return !B(A(_me,[_mj]))?E(_mb):function(_mk){return [0,function(_ml){return E(new T(function(){return B(A(new T(function(){return B(_mg(_mi[2]));}),[function(_mm){return new F(function(){return A(_mk,[[1,_mj,_mm]]);});}]));}));}];};}};return function(_mn){return new F(function(){return A(_mg,[_mn,_mf]);});};},_mo=[6],_mp=new T(function(){return B(unCStr("valDig: Bad base"));}),_mq=new T(function(){return B(err(_mp));}),_mr=function(_ms,_mt){var _mu=function(_mv,_mw){var _mx=E(_mv);if(!_mx[0]){return function(_my){return new F(function(){return A(_my,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{var _mz=E(_mx[1])[1],_mA=function(_mB){return function(_mC){return [0,function(_mD){return E(new T(function(){return B(A(new T(function(){return B(_mu(_mx[2],function(_mE){return new F(function(){return A(_mw,[[1,_mB,_mE]]);});}));}),[_mC]));}));}];};};switch(E(E(_ms)[1])){case 8:if(48>_mz){return function(_mF){return new F(function(){return A(_mF,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>55){return function(_mG){return new F(function(){return A(_mG,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,_mz-48|0]);});}}break;case 10:if(48>_mz){return function(_mH){return new F(function(){return A(_mH,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>57){return function(_mI){return new F(function(){return A(_mI,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,_mz-48|0]);});}}break;case 16:if(48>_mz){if(97>_mz){if(65>_mz){return function(_mJ){return new F(function(){return A(_mJ,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mK){return new F(function(){return A(_mK,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{if(_mz>102){if(65>_mz){return function(_mL){return new F(function(){return A(_mL,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mM){return new F(function(){return A(_mM,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{return new F(function(){return _mA([0,(_mz-97|0)+10|0]);});}}}else{if(_mz>57){if(97>_mz){if(65>_mz){return function(_mN){return new F(function(){return A(_mN,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mO){return new F(function(){return A(_mO,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{if(_mz>102){if(65>_mz){return function(_mP){return new F(function(){return A(_mP,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mQ){return new F(function(){return A(_mQ,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{return new F(function(){return _mA([0,(_mz-97|0)+10|0]);});}}}else{return new F(function(){return _mA([0,_mz-48|0]);});}}break;default:return E(_mq);}}};return function(_mR){return new F(function(){return A(_mu,[_mR,_6P,function(_mS){var _mT=E(_mS);return _mT[0]==0?[2]:B(A(_mt,[_mT]));}]);});};},_mU=[0,10],_mV=[0,1],_mW=[0,2147483647],_mX=function(_mY,_mZ){while(1){var _n0=E(_mY);if(!_n0[0]){var _n1=_n0[1],_n2=E(_mZ);if(!_n2[0]){var _n3=_n2[1],_n4=addC(_n1,_n3);if(!E(_n4[2])){return [0,_n4[1]];}else{_mY=[1,I_fromInt(_n1)];_mZ=[1,I_fromInt(_n3)];continue;}}else{_mY=[1,I_fromInt(_n1)];_mZ=_n2;continue;}}else{var _n5=E(_mZ);if(!_n5[0]){_mY=_n0;_mZ=[1,I_fromInt(_n5[1])];continue;}else{return [1,I_add(_n0[1],_n5[1])];}}}},_n6=new T(function(){return B(_mX(_mW,_mV));}),_n7=function(_n8){var _n9=E(_n8);if(!_n9[0]){var _na=E(_n9[1]);return _na==(-2147483648)?E(_n6):[0, -_na];}else{return [1,I_negate(_n9[1])];}},_nb=[0,10],_nc=[0,0],_nd=function(_ne){return [0,_ne];},_nf=function(_ng,_nh){while(1){var _ni=E(_ng);if(!_ni[0]){var _nj=_ni[1],_nk=E(_nh);if(!_nk[0]){var _nl=_nk[1];if(!(imul(_nj,_nl)|0)){return [0,imul(_nj,_nl)|0];}else{_ng=[1,I_fromInt(_nj)];_nh=[1,I_fromInt(_nl)];continue;}}else{_ng=[1,I_fromInt(_nj)];_nh=_nk;continue;}}else{var _nm=E(_nh);if(!_nm[0]){_ng=_ni;_nh=[1,I_fromInt(_nm[1])];continue;}else{return [1,I_mul(_ni[1],_nm[1])];}}}},_nn=function(_no,_np,_nq){while(1){var _nr=E(_nq);if(!_nr[0]){return E(_np);}else{var _ns=B(_mX(B(_nf(_np,_no)),B(_nd(E(_nr[1])[1]))));_nq=_nr[2];_np=_ns;continue;}}},_nt=function(_nu){var _nv=new T(function(){return B(_l1(B(_l1([0,function(_nw){return E(E(_nw)[1])==45?[1,B(_mr(_mU,function(_nx){return new F(function(){return A(_nu,[[1,new T(function(){return B(_n7(B(_nn(_nb,_nc,_nx))));})]]);});}))]:[2];}],[0,function(_ny){return E(E(_ny)[1])==43?[1,B(_mr(_mU,function(_nz){return new F(function(){return A(_nu,[[1,new T(function(){return B(_nn(_nb,_nc,_nz));})]]);});}))]:[2];}])),new T(function(){return [1,B(_mr(_mU,function(_nA){return new F(function(){return A(_nu,[[1,new T(function(){return B(_nn(_nb,_nc,_nA));})]]);});}))];})));});return new F(function(){return _l1([0,function(_nB){return E(E(_nB)[1])==101?E(_nv):[2];}],[0,function(_nC){return E(E(_nC)[1])==69?E(_nv):[2];}]);});},_nD=function(_nE){return new F(function(){return A(_nE,[_4O]);});},_nF=function(_nG){return new F(function(){return A(_nG,[_4O]);});},_nH=function(_nI){return function(_nJ){return E(E(_nJ)[1])==46?[1,B(_mr(_mU,function(_nK){return new F(function(){return A(_nI,[[1,_nK]]);});}))]:[2];};},_nL=function(_nM){return [0,B(_nH(_nM))];},_nN=function(_nO){return new F(function(){return _mr(_mU,function(_nP){return [1,B(_lR(_nL,_nD,function(_nQ){return [1,B(_lR(_nt,_nF,function(_nR){return new F(function(){return A(_nO,[[5,[1,_nP,_nQ,_nR]]]);});}))];}))];});});},_nS=function(_nT){return [1,B(_nN(_nT))];},_nU=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_nV=function(_nW){return new F(function(){return _9r(_iN,_nW,_nU);});},_nX=[0,8],_nY=[0,16],_nZ=function(_o0){var _o1=function(_o2){return new F(function(){return A(_o0,[[5,[0,_nX,_o2]]]);});},_o3=function(_o4){return new F(function(){return A(_o0,[[5,[0,_nY,_o4]]]);});};return function(_o5){return E(E(_o5)[1])==48?E([0,function(_o6){switch(E(E(_o6)[1])){case 79:return [1,B(_mr(_nX,_o1))];case 88:return [1,B(_mr(_nY,_o3))];case 111:return [1,B(_mr(_nX,_o1))];case 120:return [1,B(_mr(_nY,_o3))];default:return [2];}}]):[2];};},_o7=function(_o8){return [0,B(_nZ(_o8))];},_o9=true,_oa=function(_ob){var _oc=new T(function(){return B(A(_ob,[_nX]));}),_od=new T(function(){return B(A(_ob,[_nY]));});return function(_oe){switch(E(E(_oe)[1])){case 79:return E(_oc);case 88:return E(_od);case 111:return E(_oc);case 120:return E(_od);default:return [2];}};},_of=function(_og){return [0,B(_oa(_og))];},_oh=[0,92],_oi=function(_oj){return new F(function(){return A(_oj,[_mU]);});},_ok=function(_ol){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_ol,_9));}))));});},_om=function(_on){var _oo=E(_on);return _oo[0]==0?E(_oo[1]):I_toInt(_oo[1]);},_op=function(_oq,_or){var _os=E(_oq);if(!_os[0]){var _ot=_os[1],_ou=E(_or);return _ou[0]==0?_ot<=_ou[1]:I_compareInt(_ou[1],_ot)>=0;}else{var _ov=_os[1],_ow=E(_or);return _ow[0]==0?I_compareInt(_ov,_ow[1])<=0:I_compare(_ov,_ow[1])<=0;}},_ox=function(_oy){return [2];},_oz=function(_oA){var _oB=E(_oA);if(!_oB[0]){return E(_ox);}else{var _oC=_oB[1],_oD=E(_oB[2]);return _oD[0]==0?E(_oC):function(_oE){return new F(function(){return _l1(B(A(_oC,[_oE])),new T(function(){return B(A(new T(function(){return B(_oz(_oD));}),[_oE]));}));});};}},_oF=function(_oG){return [2];},_oH=function(_oI,_oJ){var _oK=function(_oL,_oM){var _oN=E(_oL);if(!_oN[0]){return function(_oO){return new F(function(){return A(_oO,[_oI]);});};}else{var _oP=E(_oM);return _oP[0]==0?E(_oF):E(_oN[1])[1]!=E(_oP[1])[1]?E(_oF):function(_oQ){return [0,function(_oR){return E(new T(function(){return B(A(new T(function(){return B(_oK(_oN[2],_oP[2]));}),[_oQ]));}));}];};}};return function(_oS){return new F(function(){return A(_oK,[_oI,_oS,_oJ]);});};},_oT=new T(function(){return B(unCStr("SOH"));}),_oU=[0,1],_oV=function(_oW){return [1,B(_oH(_oT,function(_oX){return E(new T(function(){return B(A(_oW,[_oU]));}));}))];},_oY=new T(function(){return B(unCStr("SO"));}),_oZ=[0,14],_p0=function(_p1){return [1,B(_oH(_oY,function(_p2){return E(new T(function(){return B(A(_p1,[_oZ]));}));}))];},_p3=function(_p4){return [1,B(_lR(_oV,_p0,_p4))];},_p5=new T(function(){return B(unCStr("NUL"));}),_p6=[0,0],_p7=function(_p8){return [1,B(_oH(_p5,function(_p9){return E(new T(function(){return B(A(_p8,[_p6]));}));}))];},_pa=new T(function(){return B(unCStr("STX"));}),_pb=[0,2],_pc=function(_pd){return [1,B(_oH(_pa,function(_pe){return E(new T(function(){return B(A(_pd,[_pb]));}));}))];},_pf=new T(function(){return B(unCStr("ETX"));}),_pg=[0,3],_ph=function(_pi){return [1,B(_oH(_pf,function(_pj){return E(new T(function(){return B(A(_pi,[_pg]));}));}))];},_pk=new T(function(){return B(unCStr("EOT"));}),_pl=[0,4],_pm=function(_pn){return [1,B(_oH(_pk,function(_po){return E(new T(function(){return B(A(_pn,[_pl]));}));}))];},_pp=new T(function(){return B(unCStr("ENQ"));}),_pq=[0,5],_pr=function(_ps){return [1,B(_oH(_pp,function(_pt){return E(new T(function(){return B(A(_ps,[_pq]));}));}))];},_pu=new T(function(){return B(unCStr("ACK"));}),_pv=[0,6],_pw=function(_px){return [1,B(_oH(_pu,function(_py){return E(new T(function(){return B(A(_px,[_pv]));}));}))];},_pz=new T(function(){return B(unCStr("BEL"));}),_pA=[0,7],_pB=function(_pC){return [1,B(_oH(_pz,function(_pD){return E(new T(function(){return B(A(_pC,[_pA]));}));}))];},_pE=new T(function(){return B(unCStr("BS"));}),_pF=[0,8],_pG=function(_pH){return [1,B(_oH(_pE,function(_pI){return E(new T(function(){return B(A(_pH,[_pF]));}));}))];},_pJ=new T(function(){return B(unCStr("HT"));}),_pK=[0,9],_pL=function(_pM){return [1,B(_oH(_pJ,function(_pN){return E(new T(function(){return B(A(_pM,[_pK]));}));}))];},_pO=new T(function(){return B(unCStr("LF"));}),_pP=[0,10],_pQ=function(_pR){return [1,B(_oH(_pO,function(_pS){return E(new T(function(){return B(A(_pR,[_pP]));}));}))];},_pT=new T(function(){return B(unCStr("VT"));}),_pU=[0,11],_pV=function(_pW){return [1,B(_oH(_pT,function(_pX){return E(new T(function(){return B(A(_pW,[_pU]));}));}))];},_pY=new T(function(){return B(unCStr("FF"));}),_pZ=[0,12],_q0=function(_q1){return [1,B(_oH(_pY,function(_q2){return E(new T(function(){return B(A(_q1,[_pZ]));}));}))];},_q3=new T(function(){return B(unCStr("CR"));}),_q4=[0,13],_q5=function(_q6){return [1,B(_oH(_q3,function(_q7){return E(new T(function(){return B(A(_q6,[_q4]));}));}))];},_q8=new T(function(){return B(unCStr("SI"));}),_q9=[0,15],_qa=function(_qb){return [1,B(_oH(_q8,function(_qc){return E(new T(function(){return B(A(_qb,[_q9]));}));}))];},_qd=new T(function(){return B(unCStr("DLE"));}),_qe=[0,16],_qf=function(_qg){return [1,B(_oH(_qd,function(_qh){return E(new T(function(){return B(A(_qg,[_qe]));}));}))];},_qi=new T(function(){return B(unCStr("DC1"));}),_qj=[0,17],_qk=function(_ql){return [1,B(_oH(_qi,function(_qm){return E(new T(function(){return B(A(_ql,[_qj]));}));}))];},_qn=new T(function(){return B(unCStr("DC2"));}),_qo=[0,18],_qp=function(_qq){return [1,B(_oH(_qn,function(_qr){return E(new T(function(){return B(A(_qq,[_qo]));}));}))];},_qs=new T(function(){return B(unCStr("DC3"));}),_qt=[0,19],_qu=function(_qv){return [1,B(_oH(_qs,function(_qw){return E(new T(function(){return B(A(_qv,[_qt]));}));}))];},_qx=new T(function(){return B(unCStr("DC4"));}),_qy=[0,20],_qz=function(_qA){return [1,B(_oH(_qx,function(_qB){return E(new T(function(){return B(A(_qA,[_qy]));}));}))];},_qC=new T(function(){return B(unCStr("NAK"));}),_qD=[0,21],_qE=function(_qF){return [1,B(_oH(_qC,function(_qG){return E(new T(function(){return B(A(_qF,[_qD]));}));}))];},_qH=new T(function(){return B(unCStr("SYN"));}),_qI=[0,22],_qJ=function(_qK){return [1,B(_oH(_qH,function(_qL){return E(new T(function(){return B(A(_qK,[_qI]));}));}))];},_qM=new T(function(){return B(unCStr("ETB"));}),_qN=[0,23],_qO=function(_qP){return [1,B(_oH(_qM,function(_qQ){return E(new T(function(){return B(A(_qP,[_qN]));}));}))];},_qR=new T(function(){return B(unCStr("CAN"));}),_qS=[0,24],_qT=function(_qU){return [1,B(_oH(_qR,function(_qV){return E(new T(function(){return B(A(_qU,[_qS]));}));}))];},_qW=new T(function(){return B(unCStr("EM"));}),_qX=[0,25],_qY=function(_qZ){return [1,B(_oH(_qW,function(_r0){return E(new T(function(){return B(A(_qZ,[_qX]));}));}))];},_r1=new T(function(){return B(unCStr("SUB"));}),_r2=[0,26],_r3=function(_r4){return [1,B(_oH(_r1,function(_r5){return E(new T(function(){return B(A(_r4,[_r2]));}));}))];},_r6=new T(function(){return B(unCStr("ESC"));}),_r7=[0,27],_r8=function(_r9){return [1,B(_oH(_r6,function(_ra){return E(new T(function(){return B(A(_r9,[_r7]));}));}))];},_rb=new T(function(){return B(unCStr("FS"));}),_rc=[0,28],_rd=function(_re){return [1,B(_oH(_rb,function(_rf){return E(new T(function(){return B(A(_re,[_rc]));}));}))];},_rg=new T(function(){return B(unCStr("GS"));}),_rh=[0,29],_ri=function(_rj){return [1,B(_oH(_rg,function(_rk){return E(new T(function(){return B(A(_rj,[_rh]));}));}))];},_rl=new T(function(){return B(unCStr("RS"));}),_rm=[0,30],_rn=function(_ro){return [1,B(_oH(_rl,function(_rp){return E(new T(function(){return B(A(_ro,[_rm]));}));}))];},_rq=new T(function(){return B(unCStr("US"));}),_rr=[0,31],_rs=function(_rt){return [1,B(_oH(_rq,function(_ru){return E(new T(function(){return B(A(_rt,[_rr]));}));}))];},_rv=new T(function(){return B(unCStr("SP"));}),_rw=[0,32],_rx=function(_ry){return [1,B(_oH(_rv,function(_rz){return E(new T(function(){return B(A(_ry,[_rw]));}));}))];},_rA=new T(function(){return B(unCStr("DEL"));}),_rB=[0,127],_rC=function(_rD){return [1,B(_oH(_rA,function(_rE){return E(new T(function(){return B(A(_rD,[_rB]));}));}))];},_rF=[1,_rC,_9],_rG=[1,_rx,_rF],_rH=[1,_rs,_rG],_rI=[1,_rn,_rH],_rJ=[1,_ri,_rI],_rK=[1,_rd,_rJ],_rL=[1,_r8,_rK],_rM=[1,_r3,_rL],_rN=[1,_qY,_rM],_rO=[1,_qT,_rN],_rP=[1,_qO,_rO],_rQ=[1,_qJ,_rP],_rR=[1,_qE,_rQ],_rS=[1,_qz,_rR],_rT=[1,_qu,_rS],_rU=[1,_qp,_rT],_rV=[1,_qk,_rU],_rW=[1,_qf,_rV],_rX=[1,_qa,_rW],_rY=[1,_q5,_rX],_rZ=[1,_q0,_rY],_s0=[1,_pV,_rZ],_s1=[1,_pQ,_s0],_s2=[1,_pL,_s1],_s3=[1,_pG,_s2],_s4=[1,_pB,_s3],_s5=[1,_pw,_s4],_s6=[1,_pr,_s5],_s7=[1,_pm,_s6],_s8=[1,_ph,_s7],_s9=[1,_pc,_s8],_sa=[1,_p7,_s9],_sb=[1,_p3,_sa],_sc=new T(function(){return B(_oz(_sb));}),_sd=[0,1114111],_se=[0,34],_sf=[0,39],_sg=function(_sh){var _si=new T(function(){return B(A(_sh,[_pA]));}),_sj=new T(function(){return B(A(_sh,[_pF]));}),_sk=new T(function(){return B(A(_sh,[_pK]));}),_sl=new T(function(){return B(A(_sh,[_pP]));}),_sm=new T(function(){return B(A(_sh,[_pU]));}),_sn=new T(function(){return B(A(_sh,[_pZ]));}),_so=new T(function(){return B(A(_sh,[_q4]));});return new F(function(){return _l1([0,function(_sp){switch(E(E(_sp)[1])){case 34:return E(new T(function(){return B(A(_sh,[_se]));}));case 39:return E(new T(function(){return B(A(_sh,[_sf]));}));case 92:return E(new T(function(){return B(A(_sh,[_oh]));}));case 97:return E(_si);case 98:return E(_sj);case 102:return E(_sn);case 110:return E(_sl);case 114:return E(_so);case 116:return E(_sk);case 118:return E(_sm);default:return [2];}}],new T(function(){return B(_l1([1,B(_lR(_of,_oi,function(_sq){return [1,B(_mr(_sq,function(_sr){var _ss=B(_nn(new T(function(){return B(_nd(E(_sq)[1]));}),_nc,_sr));return !B(_op(_ss,_sd))?[2]:B(A(_sh,[new T(function(){var _st=B(_om(_ss));if(_st>>>0>1114111){var _su=B(_ok(_st));}else{var _su=[0,_st];}var _sv=_su,_sw=_sv,_sx=_sw;return _sx;})]));}))];}))],new T(function(){return B(_l1([0,function(_sy){return E(E(_sy)[1])==94?E([0,function(_sz){switch(E(E(_sz)[1])){case 64:return E(new T(function(){return B(A(_sh,[_p6]));}));case 65:return E(new T(function(){return B(A(_sh,[_oU]));}));case 66:return E(new T(function(){return B(A(_sh,[_pb]));}));case 67:return E(new T(function(){return B(A(_sh,[_pg]));}));case 68:return E(new T(function(){return B(A(_sh,[_pl]));}));case 69:return E(new T(function(){return B(A(_sh,[_pq]));}));case 70:return E(new T(function(){return B(A(_sh,[_pv]));}));case 71:return E(_si);case 72:return E(_sj);case 73:return E(_sk);case 74:return E(_sl);case 75:return E(_sm);case 76:return E(_sn);case 77:return E(_so);case 78:return E(new T(function(){return B(A(_sh,[_oZ]));}));case 79:return E(new T(function(){return B(A(_sh,[_q9]));}));case 80:return E(new T(function(){return B(A(_sh,[_qe]));}));case 81:return E(new T(function(){return B(A(_sh,[_qj]));}));case 82:return E(new T(function(){return B(A(_sh,[_qo]));}));case 83:return E(new T(function(){return B(A(_sh,[_qt]));}));case 84:return E(new T(function(){return B(A(_sh,[_qy]));}));case 85:return E(new T(function(){return B(A(_sh,[_qD]));}));case 86:return E(new T(function(){return B(A(_sh,[_qI]));}));case 87:return E(new T(function(){return B(A(_sh,[_qN]));}));case 88:return E(new T(function(){return B(A(_sh,[_qS]));}));case 89:return E(new T(function(){return B(A(_sh,[_qX]));}));case 90:return E(new T(function(){return B(A(_sh,[_r2]));}));case 91:return E(new T(function(){return B(A(_sh,[_r7]));}));case 92:return E(new T(function(){return B(A(_sh,[_rc]));}));case 93:return E(new T(function(){return B(A(_sh,[_rh]));}));case 94:return E(new T(function(){return B(A(_sh,[_rm]));}));case 95:return E(new T(function(){return B(A(_sh,[_rr]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_sc,[_sh]));})));})));}));});},_sA=function(_sB){return new F(function(){return A(_sB,[_6B]);});},_sC=function(_sD){var _sE=E(_sD);if(!_sE[0]){return E(_sA);}else{var _sF=_sE[2],_sG=E(E(_sE[1])[1]);switch(_sG){case 9:return function(_sH){return [0,function(_sI){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sH]));}));}];};case 10:return function(_sJ){return [0,function(_sK){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sJ]));}));}];};case 11:return function(_sL){return [0,function(_sM){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sL]));}));}];};case 12:return function(_sN){return [0,function(_sO){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sN]));}));}];};case 13:return function(_sP){return [0,function(_sQ){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sP]));}));}];};case 32:return function(_sR){return [0,function(_sS){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sR]));}));}];};case 160:return function(_sT){return [0,function(_sU){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sT]));}));}];};default:var _sV=u_iswspace(_sG),_sW=_sV;return E(_sW)==0?E(_sA):function(_sX){return [0,function(_sY){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sX]));}));}];};}}},_sZ=function(_t0){var _t1=new T(function(){return B(_sZ(_t0));}),_t2=[1,function(_t3){return new F(function(){return A(_sC,[_t3,function(_t4){return E([0,function(_t5){return E(E(_t5)[1])==92?E(_t1):[2];}]);}]);});}];return new F(function(){return _l1([0,function(_t6){return E(E(_t6)[1])==92?E([0,function(_t7){var _t8=E(E(_t7)[1]);switch(_t8){case 9:return E(_t2);case 10:return E(_t2);case 11:return E(_t2);case 12:return E(_t2);case 13:return E(_t2);case 32:return E(_t2);case 38:return E(_t1);case 160:return E(_t2);default:var _t9=u_iswspace(_t8),_ta=_t9;return E(_ta)==0?[2]:E(_t2);}}]):[2];}],[0,function(_tb){var _tc=E(_tb);return E(_tc[1])==92?E(new T(function(){return B(_sg(function(_td){return new F(function(){return A(_t0,[[0,_td,_o9]]);});}));})):B(A(_t0,[[0,_tc,_4y]]));}]);});},_te=function(_tf,_tg){return new F(function(){return _sZ(function(_th){var _ti=E(_th),_tj=E(_ti[1]);if(E(_tj[1])==34){if(!E(_ti[2])){return E(new T(function(){return B(A(_tg,[[1,new T(function(){return B(A(_tf,[_9]));})]]));}));}else{return new F(function(){return _te(function(_tk){return new F(function(){return A(_tf,[[1,_tj,_tk]]);});},_tg);});}}else{return new F(function(){return _te(function(_tl){return new F(function(){return A(_tf,[[1,_tj,_tl]]);});},_tg);});}});});},_tm=new T(function(){return B(unCStr("_\'"));}),_tn=function(_to){var _tp=u_iswalnum(_to),_tq=_tp;return E(_tq)==0?B(_9r(_iN,[0,_to],_tm)):true;},_tr=function(_ts){return new F(function(){return _tn(E(_ts)[1]);});},_tt=new T(function(){return B(unCStr(",;()[]{}`"));}),_tu=new T(function(){return B(unCStr(".."));}),_tv=new T(function(){return B(unCStr("::"));}),_tw=new T(function(){return B(unCStr("->"));}),_tx=[0,64],_ty=[1,_tx,_9],_tz=[0,126],_tA=[1,_tz,_9],_tB=new T(function(){return B(unCStr("=>"));}),_tC=[1,_tB,_9],_tD=[1,_tA,_tC],_tE=[1,_ty,_tD],_tF=[1,_tw,_tE],_tG=new T(function(){return B(unCStr("<-"));}),_tH=[1,_tG,_tF],_tI=[0,124],_tJ=[1,_tI,_9],_tK=[1,_tJ,_tH],_tL=[1,_oh,_9],_tM=[1,_tL,_tK],_tN=[0,61],_tO=[1,_tN,_9],_tP=[1,_tO,_tM],_tQ=[1,_tv,_tP],_tR=[1,_tu,_tQ],_tS=function(_tT){return new F(function(){return _l1([1,function(_tU){return E(_tU)[0]==0?E(new T(function(){return B(A(_tT,[_mo]));})):[2];}],new T(function(){return B(_l1([0,function(_tV){return E(E(_tV)[1])==39?E([0,function(_tW){var _tX=E(_tW);switch(E(_tX[1])){case 39:return [2];case 92:return E(new T(function(){return B(_sg(function(_tY){return [0,function(_tZ){return E(E(_tZ)[1])==39?E(new T(function(){return B(A(_tT,[[0,_tY]]));})):[2];}];}));}));default:return [0,function(_u0){return E(E(_u0)[1])==39?E(new T(function(){return B(A(_tT,[[0,_tX]]));})):[2];}];}}]):[2];}],new T(function(){return B(_l1([0,function(_u1){return E(E(_u1)[1])==34?E(new T(function(){return B(_te(_6P,_tT));})):[2];}],new T(function(){return B(_l1([0,function(_u2){return !B(_9r(_iN,_u2,_tt))?[2]:B(A(_tT,[[2,[1,_u2,_9]]]));}],new T(function(){return B(_l1([0,function(_u3){return !B(_9r(_iN,_u3,_nU))?[2]:[1,B(_md(_nV,function(_u4){var _u5=[1,_u3,_u4];return !B(_9r(_8H,_u5,_tR))?B(A(_tT,[[4,_u5]])):B(A(_tT,[[2,_u5]]));}))];}],new T(function(){return B(_l1([0,function(_u6){var _u7=E(_u6),_u8=_u7[1],_u9=u_iswalpha(_u8),_ua=_u9;return E(_ua)==0?E(_u8)==95?[1,B(_md(_tr,function(_ub){return new F(function(){return A(_tT,[[3,[1,_u7,_ub]]]);});}))]:[2]:[1,B(_md(_tr,function(_uc){return new F(function(){return A(_tT,[[3,[1,_u7,_uc]]]);});}))];}],new T(function(){return [1,B(_lR(_o7,_nS,_tT))];})));})));})));})));})));}));});},_ud=[0,0],_ue=function(_uf,_ug){return function(_uh){return new F(function(){return A(_sC,[_uh,function(_ui){return E(new T(function(){return B(_tS(function(_uj){var _uk=E(_uj);return _uk[0]==2?!B(_3x(_uk[1],_lx))?[2]:E(new T(function(){return B(A(_uf,[_ud,function(_ul){return [1,function(_um){return new F(function(){return A(_sC,[_um,function(_un){return E(new T(function(){return B(_tS(function(_uo){var _up=E(_uo);return _up[0]==2?!B(_3x(_up[1],_lv))?[2]:E(new T(function(){return B(A(_ug,[_ul]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_uq=function(_ur,_us,_ut){var _uu=function(_uv,_uw){return new F(function(){return _l1([1,function(_ux){return new F(function(){return A(_sC,[_ux,function(_uy){return E(new T(function(){return B(_tS(function(_uz){var _uA=E(_uz);if(_uA[0]==4){var _uB=E(_uA[1]);if(!_uB[0]){return new F(function(){return A(_ur,[_uA,_uv,_uw]);});}else{return E(E(_uB[1])[1])==45?E(_uB[2])[0]==0?E([1,function(_uC){return new F(function(){return A(_sC,[_uC,function(_uD){return E(new T(function(){return B(_tS(function(_uE){return new F(function(){return A(_ur,[_uE,_uv,function(_uF){return new F(function(){return A(_uw,[new T(function(){return [0, -E(_uF)[1]];})]);});}]);});}));}));}]);});}]):B(A(_ur,[_uA,_uv,_uw])):B(A(_ur,[_uA,_uv,_uw]));}}else{return new F(function(){return A(_ur,[_uA,_uv,_uw]);});}}));}));}]);});}],new T(function(){return [1,B(_ue(_uu,_uw))];}));});};return new F(function(){return _uu(_us,_ut);});},_uG=function(_uH,_uI){return [2];},_uJ=function(_uK){var _uL=E(_uK);return _uL[0]==0?[1,new T(function(){return B(_nn(new T(function(){return B(_nd(E(_uL[1])[1]));}),_nc,_uL[2]));})]:E(_uL[2])[0]==0?E(_uL[3])[0]==0?[1,new T(function(){return B(_nn(_nb,_nc,_uL[1]));})]:[0]:[0];},_uM=function(_uN){var _uO=E(_uN);if(_uO[0]==5){var _uP=B(_uJ(_uO[1]));return _uP[0]==0?E(_uG):function(_uQ,_uR){return new F(function(){return A(_uR,[new T(function(){return [0,B(_om(_uP[1]))];})]);});};}else{return E(_uG);}},_uS=function(_uT){return [1,function(_uU){return new F(function(){return A(_sC,[_uU,function(_uV){return E([3,_uT,_lJ]);}]);});}];},_uW=new T(function(){return B(_uq(_uM,_ud,_uS));}),_uX=function(_uY){while(1){var _uZ=(function(_v0){var _v1=E(_v0);if(!_v1[0]){return [0];}else{var _v2=_v1[2],_v3=E(_v1[1]);if(!E(_v3[2])[0]){return [1,_v3[1],new T(function(){return B(_uX(_v2));})];}else{_uY=_v2;return null;}}})(_uY);if(_uZ!=null){return _uZ;}}},_v4=function(_v5){var _v6=B(_uX(B(_kR(_uW,_v5))));return _v6[0]==0?E(_kN):E(_v6[2])[0]==0?E(_v6[1]):E(_kP);},_v7=function(_v8,_v9,_va,_vb,_vc){var _vd=function(_ve,_vf,_vg){var _vh=function(_vi,_vj,_vk){return new F(function(){return A(_vg,[[0,_v8,new T(function(){return B(_3d(_v4,_vi));})],_vj,new T(function(){var _vl=E(E(_vj)[2]),_vm=E(_vk),_vn=E(_vm[1]),_vo=B(_db(_vn[1],_vn[2],_vn[3],_vm[2],_vl[1],_vl[2],_vl[3],_9));return [0,E(_vo[1]),_vo[2]];})]);});},_vp=function(_vq){return new F(function(){return _vh(_9,_ve,new T(function(){var _vr=E(E(_ve)[2]),_vs=E(_vq),_vt=E(_vs[1]),_vu=B(_db(_vt[1],_vt[2],_vt[3],_vs[2],_vr[1],_vr[2],_vr[3],_9));return [0,E(_vu[1]),_vu[2]];},1));});};return new F(function(){return _fb(_kk,_kL,_ve,function(_vv,_vw,_vx){return new F(function(){return A(_vf,[[0,_v8,new T(function(){return B(_3d(_v4,_vv));})],_vw,new T(function(){var _vy=E(E(_vw)[2]),_vz=E(_vx),_vA=E(_vz[1]),_vB=B(_db(_vA[1],_vA[2],_vA[3],_vz[2],_vy[1],_vy[2],_vy[3],_9));return [0,E(_vB[1]),_vB[2]];})]);});},_vp,_vh,_vp);});};return new F(function(){return _eL(_j7,_v9,function(_vC,_vD,_vE){return new F(function(){return _vd(_vD,_va,function(_vF,_vG,_vH){return new F(function(){return A(_va,[_vF,_vG,new T(function(){return B(_e0(_vE,_vH));})]);});});});},_vb,function(_vI,_vJ,_vK){return new F(function(){return _vd(_vJ,_va,function(_vL,_vM,_vN){return new F(function(){return A(_vc,[_vL,_vM,new T(function(){return B(_e0(_vK,_vN));})]);});});});});});},_vO=new T(function(){return B(unCStr("letter or digit"));}),_vP=[1,_vO,_9],_vQ=function(_vR){var _vS=u_iswalnum(E(_vR)[1]),_vT=_vS;return E(_vT)==0?false:true;},_vU=function(_vV,_vW,_vX,_vY,_vZ){var _w0=E(_vV),_w1=E(_w0[2]);return new F(function(){return _il(_gm,_k1,_vQ,_w0[1],_w1[1],_w1[2],_w1[3],_w0[3],_vW,_vZ);});},_w2=function(_w3,_w4,_w5,_w6,_w7){return new F(function(){return _jI(_vU,_vP,_w3,_w4,_w5,_w6,_w7);});},_w8=function(_w9,_wa,_wb,_wc,_wd){return new F(function(){return _e8(_w2,_w9,function(_we,_wf,_wg){return new F(function(){return _v7(_we,_wf,_wa,_wb,function(_wh,_wi,_wj){return new F(function(){return A(_wa,[_wh,_wi,new T(function(){return B(_e0(_wg,_wj));})]);});});});},_wd,function(_wk,_wl,_wm){return new F(function(){return _v7(_wk,_wl,_wa,_wb,function(_wn,_wo,_wp){return new F(function(){return A(_wc,[_wn,_wo,new T(function(){return B(_e0(_wm,_wp));})]);});});});},_wd);});},_wq=new T(function(){return B(unCStr("SHOW"));}),_wr=[0,_wq,_9],_ws=function(_wt,_wu,_wv,_ww){var _wx=function(_wy){return new F(function(){return A(_ww,[[0,_wt,_wr],_wu,new T(function(){var _wz=E(E(_wu)[2]),_wA=_wz[1],_wB=_wz[2],_wC=_wz[3],_wD=E(_wy),_wE=E(_wD[1]),_wF=B(_db(_wE[1],_wE[2],_wE[3],_wD[2],_wA,_wB,_wC,_9)),_wG=E(_wF[1]),_wH=B(_db(_wG[1],_wG[2],_wG[3],_wF[2],_wA,_wB,_wC,_9));return [0,E(_wH[1]),_wH[2]];})]);});};return new F(function(){return _w8(_wu,function(_wI,_wJ,_wK){return new F(function(){return A(_wv,[[0,_wt,_wI],_wJ,new T(function(){var _wL=E(E(_wJ)[2]),_wM=E(_wK),_wN=E(_wM[1]),_wO=B(_db(_wN[1],_wN[2],_wN[3],_wM[2],_wL[1],_wL[2],_wL[3],_9));return [0,E(_wO[1]),_wO[2]];})]);});},_wx,function(_wP,_wQ,_wR){return new F(function(){return A(_ww,[[0,_wt,_wP],_wQ,new T(function(){var _wS=E(E(_wQ)[2]),_wT=E(_wR),_wU=E(_wT[1]),_wV=B(_db(_wU[1],_wU[2],_wU[3],_wT[2],_wS[1],_wS[2],_wS[3],_9));return [0,E(_wV[1]),_wV[2]];})]);});},_wx);});},_wW=new T(function(){return B(unCStr("sS"));}),_wX=new T(function(){return B(_kq(_iY));}),_wY=[0,58],_wZ=new T(function(){return B(_kt(_wX,_wY));}),_x0=[1,_vO,_9],_x1=function(_x2,_x3,_x4,_x5,_x6,_x7,_x8,_x9,_xa){var _xb=function(_xc,_xd){var _xe=new T(function(){var _xf=B(_jn(_xc,_xd,_x0));return [0,E(_xf[1]),_xf[2]];});return new F(function(){return A(_wZ,[[0,_x2,E([0,_x3,_x4,_x5]),E(_x6)],_x7,_x8,function(_xg,_xh,_xi){return new F(function(){return A(_x9,[_xg,_xh,new T(function(){return B(_e0(_xe,_xi));})]);});},function(_xj){return new F(function(){return A(_xa,[new T(function(){return B(_e0(_xe,_xj));})]);});}]);});},_xk=E(_x2);if(!_xk[0]){return new F(function(){return _xb([0,_x3,_x4,_x5],_gs);});}else{var _xl=_xk[2],_xm=E(_xk[1]),_xn=_xm[1],_xo=u_iswalnum(_xn),_xp=_xo;if(!E(_xp)){return new F(function(){return _xb([0,_x3,_x4,_x5],[1,[0,E([1,_gp,new T(function(){return B(_if([1,_xm,_9],_gq));})])],_9]);});}else{switch(E(_xn)){case 9:var _xq=[0,_x3,_x4,(_x5+8|0)-B(_gt(_x5-1|0,8))|0];break;case 10:var _xq=[0,_x3,_x4+1|0,1];break;default:var _xq=[0,_x3,_x4,_x5+1|0];}var _xr=_xq,_xs=[0,E(_xr),_9],_xt=[0,_xl,E(_xr),E(_x6)];return new F(function(){return A(_x7,[_xm,_xt,_xs]);});}}},_xu=function(_xv,_xw,_xx,_xy,_xz){var _xA=E(_xv),_xB=E(_xA[2]);return new F(function(){return _x1(_xA[1],_xB[1],_xB[2],_xB[3],_xA[3],_xw,_xx,_xy,_xz);});},_xC=[0,10],_xD=new T(function(){return B(unCStr("lf new-line"));}),_xE=[1,_xD,_9],_xF=function(_xG){return function(_xH,_xI,_xJ,_xK,_xL){return new F(function(){return _jI(new T(function(){return B(_kt(_xG,_xC));}),_xE,_xH,_xI,_xJ,_xK,_xL);});};},_xM=new T(function(){return B(_xF(_wX));}),_xN=function(_xO,_xP,_xQ,_xR,_xS,_xT,_xU){var _xV=function(_xW,_xX,_xY,_xZ,_y0,_y1){return new F(function(){return _y2(_xX,function(_y3,_y4,_y5){return new F(function(){return A(_xY,[[1,_xW,_y3],_y4,new T(function(){var _y6=E(E(_y4)[2]),_y7=E(_y5),_y8=E(_y7[1]),_y9=B(_db(_y8[1],_y8[2],_y8[3],_y7[2],_y6[1],_y6[2],_y6[3],_9));return [0,E(_y9[1]),_y9[2]];})]);});},_xZ,function(_ya,_yb,_yc){return new F(function(){return A(_y0,[[1,_xW,_ya],_yb,new T(function(){var _yd=E(E(_yb)[2]),_ye=E(_yc),_yf=E(_ye[1]),_yg=B(_db(_yf[1],_yf[2],_yf[3],_ye[2],_yd[1],_yd[2],_yd[3],_9));return [0,E(_yg[1]),_yg[2]];})]);});},_y1);});},_y2=function(_yh,_yi,_yj,_yk,_yl){return new F(function(){return A(_xP,[_yh,function(_ym,_yn,_yo){return new F(function(){return A(_yi,[_9,_yn,new T(function(){var _yp=E(E(_yn)[2]),_yq=E(_yo),_yr=E(_yq[1]),_ys=B(_db(_yr[1],_yr[2],_yr[3],_yq[2],_yp[1],_yp[2],_yp[3],_9));return [0,E(_ys[1]),_ys[2]];})]);});},_yj,function(_yt,_yu,_yv){return new F(function(){return A(_yk,[_9,_yu,new T(function(){var _yw=E(E(_yu)[2]),_yx=E(_yv),_yy=E(_yx[1]),_yz=B(_db(_yy[1],_yy[2],_yy[3],_yx[2],_yw[1],_yw[2],_yw[3],_9));return [0,E(_yz[1]),_yz[2]];})]);});},function(_yA){return new F(function(){return A(_xO,[_yh,function(_yB,_yC,_yD){return new F(function(){return _xV(_yB,_yC,_yi,_yj,function(_yE,_yF,_yG){return new F(function(){return A(_yi,[_yE,_yF,new T(function(){return B(_e0(_yD,_yG));})]);});},function(_yH){return new F(function(){return A(_yj,[new T(function(){return B(_e0(_yD,_yH));})]);});});});},_yj,function(_yI,_yJ,_yK){return new F(function(){return _xV(_yI,_yJ,_yi,_yj,function(_yL,_yM,_yN){return new F(function(){return A(_yk,[_yL,_yM,new T(function(){var _yO=E(_yA),_yP=E(_yO[1]),_yQ=E(_yK),_yR=E(_yQ[1]),_yS=E(_yN),_yT=E(_yS[1]),_yU=B(_db(_yR[1],_yR[2],_yR[3],_yQ[2],_yT[1],_yT[2],_yT[3],_yS[2])),_yV=E(_yU[1]),_yW=B(_db(_yP[1],_yP[2],_yP[3],_yO[2],_yV[1],_yV[2],_yV[3],_yU[2]));return [0,E(_yW[1]),_yW[2]];})]);});},function(_yX){return new F(function(){return A(_yl,[new T(function(){var _yY=E(_yA),_yZ=E(_yY[1]),_z0=E(_yK),_z1=E(_z0[1]),_z2=E(_yX),_z3=E(_z2[1]),_z4=B(_db(_z1[1],_z1[2],_z1[3],_z0[2],_z3[1],_z3[2],_z3[3],_z2[2])),_z5=E(_z4[1]),_z6=B(_db(_yZ[1],_yZ[2],_yZ[3],_yY[2],_z5[1],_z5[2],_z5[3],_z4[2]));return [0,E(_z6[1]),_z6[2]];})]);});});});},function(_z7){return new F(function(){return A(_yl,[new T(function(){return B(_e0(_yA,_z7));})]);});}]);});}]);});};return new F(function(){return _y2(_xQ,_xR,_xS,_xT,_xU);});},_z8=new T(function(){return B(unCStr("tab"));}),_z9=[1,_z8,_9],_za=[0,9],_zb=function(_zc){return function(_zd,_ze,_zf,_zg,_zh){return new F(function(){return _jI(new T(function(){return B(_kt(_zc,_za));}),_z9,_zd,_ze,_zf,_zg,_zh);});};},_zi=new T(function(){return B(_zb(_wX));}),_zj=[0,39],_zk=[1,_zj,_9],_zl=new T(function(){return B(unCStr("\'\\\'\'"));}),_zm=function(_zn){var _zo=E(E(_zn)[1]);return _zo==39?E(_zl):[1,_zj,new T(function(){return B(_hY(_zo,_zk));})];},_zp=function(_zq,_zr){return [1,_gp,new T(function(){return B(_if(_zq,[1,_gp,_zr]));})];},_zs=function(_zt){return new F(function(){return _e(_zl,_zt);});},_zu=function(_zv,_zw){var _zx=E(E(_zw)[1]);return _zx==39?E(_zs):function(_zy){return [1,_zj,new T(function(){return B(_hY(_zx,[1,_zj,_zy]));})];};},_zz=[0,_zu,_zm,_zp],_zA=function(_zB,_zC,_zD,_zE,_zF){var _zG=new T(function(){return B(_bT(_zB));}),_zH=function(_zI){return new F(function(){return A(_zE,[_6B,_zD,new T(function(){var _zJ=E(E(_zD)[2]),_zK=E(_zI),_zL=E(_zK[1]),_zM=B(_db(_zL[1],_zL[2],_zL[3],_zK[2],_zJ[1],_zJ[2],_zJ[3],_9));return [0,E(_zM[1]),_zM[2]];})]);});};return new F(function(){return A(_zC,[_zD,function(_zN,_zO,_zP){return new F(function(){return A(_zF,[new T(function(){var _zQ=E(E(_zO)[2]),_zR=E(_zP),_zS=E(_zR[1]),_zT=B(_db(_zS[1],_zS[2],_zS[3],_zR[2],_zQ[1],_zQ[2],_zQ[3],[1,new T(function(){return [1,E(B(A(_zG,[_zN])))];}),_9]));return [0,E(_zT[1]),_zT[2]];})]);});},_zH,function(_zU,_zV,_zW){return new F(function(){return A(_zE,[_6B,_zD,new T(function(){var _zX=E(E(_zD)[2]),_zY=E(E(_zV)[2]),_zZ=E(_zW),_A0=E(_zZ[1]),_A1=B(_db(_A0[1],_A0[2],_A0[3],_zZ[2],_zY[1],_zY[2],_zY[3],[1,new T(function(){return [1,E(B(A(_zG,[_zU])))];}),_9])),_A2=E(_A1[1]),_A3=B(_db(_A2[1],_A2[2],_A2[3],_A1[2],_zX[1],_zX[2],_zX[3],_9));return [0,E(_A3[1]),_A3[2]];})]);});},_zH]);});},_A4=function(_A5,_A6,_A7){return new F(function(){return _zA(_zz,_zi,_A5,function(_A8,_A9,_Aa){return new F(function(){return A(_A6,[_6B,_A9,new T(function(){var _Ab=E(E(_A9)[2]),_Ac=E(_Aa),_Ad=E(_Ac[1]),_Ae=B(_db(_Ad[1],_Ad[2],_Ad[3],_Ac[2],_Ab[1],_Ab[2],_Ab[3],_9));return [0,E(_Ae[1]),_Ae[2]];})]);});},_A7);});},_Af=function(_Ag,_Ah,_Ai,_Aj,_Ak){return new F(function(){return A(_xM,[_Ag,function(_Al,_Am,_An){return new F(function(){return _A4(_Am,function(_Ao,_Ap,_Aq){return new F(function(){return A(_Ah,[_Ao,_Ap,new T(function(){return B(_e0(_An,_Aq));})]);});},function(_Ar){return new F(function(){return A(_Ai,[new T(function(){return B(_e0(_An,_Ar));})]);});});});},_Ai,function(_As,_At,_Au){return new F(function(){return _A4(_At,function(_Av,_Aw,_Ax){return new F(function(){return A(_Aj,[_Av,_Aw,new T(function(){return B(_e0(_Au,_Ax));})]);});},function(_Ay){return new F(function(){return A(_Ak,[new T(function(){return B(_e0(_Au,_Ay));})]);});});});},_Ak]);});},_Az=[0,E(_9)],_AA=[1,_Az,_9],_AB=function(_AC,_AD,_AE,_AF,_AG,_AH,_AI){return new F(function(){return A(_AC,[new T(function(){return B(A(_AD,[_AE]));}),function(_AJ){var _AK=E(_AJ);if(!_AK[0]){return E(new T(function(){return B(A(_AI,[[0,E(_AF),_AA]]));}));}else{var _AL=E(_AK[1]);return new F(function(){return A(_AH,[_AL[1],[0,_AL[2],E(_AF),E(_AG)],[0,E(_AF),_9]]);});}}]);});},_AM=new T(function(){return B(unCStr("end of input"));}),_AN=[1,_AM,_9],_AO=function(_AP,_AQ,_AR,_AS,_AT,_AU,_AV,_AW){return new F(function(){return _jI(function(_AX,_AY,_AZ,_B0,_B1){return new F(function(){return _zA(_AR,function(_B2,_B3,_B4,_B5,_B6){var _B7=E(_B2);return new F(function(){return _AB(_AP,_AQ,_B7[1],_B7[2],_B7[3],_B3,_B6);});},_AX,_B0,_B1);});},_AN,_AS,_AT,_AU,_AV,_AW);});},_B8=function(_B9,_Ba,_Bb,_Bc,_Bd){return new F(function(){return _dy(_xM,_B9,function(_Be,_Bf,_Bg){return new F(function(){return _AO(_gm,_j5,_zz,_Bf,_Ba,_Bb,function(_Bh,_Bi,_Bj){return new F(function(){return A(_Ba,[_Bh,_Bi,new T(function(){return B(_e0(_Bg,_Bj));})]);});},function(_Bk){return new F(function(){return A(_Bb,[new T(function(){return B(_e0(_Bg,_Bk));})]);});});});},_Bb,function(_Bl,_Bm,_Bn){return new F(function(){return _AO(_gm,_j5,_zz,_Bm,_Ba,_Bb,function(_Bo,_Bp,_Bq){return new F(function(){return A(_Bc,[_Bo,_Bp,new T(function(){return B(_e0(_Bn,_Bq));})]);});},function(_Br){return new F(function(){return A(_Bd,[new T(function(){return B(_e0(_Bn,_Br));})]);});});});});});},_Bs=function(_Bt,_Bu,_Bv,_Bw){var _Bx=function(_By){var _Bz=function(_BA){return new F(function(){return A(_Bw,[new T(function(){return B(_e0(_By,_BA));})]);});};return new F(function(){return _Af(_Bt,_Bu,_Bz,function(_BB,_BC,_BD){return new F(function(){return A(_Bv,[_BB,_BC,new T(function(){return B(_e0(_By,_BD));})]);});},_Bz);});};return new F(function(){return _B8(_Bt,_Bu,_Bx,_Bv,_Bx);});},_BE=function(_BF,_BG,_BH,_BI,_BJ){return new F(function(){return _Bs(_BF,_BG,_BI,_BJ);});},_BK=function(_BL){return true;},_BM=function(_BN,_BO,_BP,_BQ,_BR){var _BS=E(_BN),_BT=E(_BS[2]);return new F(function(){return _il(_gm,_j5,_BK,_BS[1],_BT[1],_BT[2],_BT[3],_BS[3],_BO,_BR);});},_BU=function(_BV,_BW,_BX,_BY,_BZ){return new F(function(){return A(_zi,[_BV,function(_C0,_C1,_C2){return new F(function(){return _xN(_BM,_BE,_C1,_BW,_BX,function(_C3,_C4,_C5){return new F(function(){return A(_BW,[_C3,_C4,new T(function(){return B(_e0(_C2,_C5));})]);});},function(_C6){return new F(function(){return A(_BX,[new T(function(){return B(_e0(_C2,_C6));})]);});});});},_BX,function(_C7,_C8,_C9){return new F(function(){return _xN(_BM,_BE,_C8,_BW,_BX,function(_Ca,_Cb,_Cc){return new F(function(){return A(_BY,[_Ca,_Cb,new T(function(){return B(_e0(_C9,_Cc));})]);});},function(_Cd){return new F(function(){return A(_BZ,[new T(function(){return B(_e0(_C9,_Cd));})]);});});});},_BZ]);});},_Ce=[0,_wq,_9],_Cf=[0,_9,1,1],_Cg=function(_Ch){return E(_Ch);},_Ci=function(_Cj){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_Cj));}))));});},_Ck=new T(function(){return B(_Ci("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_Cl=new T(function(){return B(_Ci("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_Cm=[0,_gm,_Cl,_Cg,_Ck],_Cn=function(_Co){return new F(function(){return unAppCStr("string error",new T(function(){return B(_bh(_Co));}));});},_Cp=function(_Cq,_Cr,_Cs,_Ct,_Cu){return new F(function(){return A(_zi,[_Cr,function(_Cv,_Cw,_Cx){return new F(function(){return A(_Cs,[_Cq,_Cw,new T(function(){var _Cy=E(E(_Cw)[2]),_Cz=E(_Cx),_CA=E(_Cz[1]),_CB=B(_db(_CA[1],_CA[2],_CA[3],_Cz[2],_Cy[1],_Cy[2],_Cy[3],_9));return [0,E(_CB[1]),_CB[2]];})]);});},_Cu,function(_CC,_CD,_CE){return new F(function(){return A(_Ct,[_Cq,_CD,new T(function(){var _CF=E(E(_CD)[2]),_CG=E(_CE),_CH=E(_CG[1]),_CI=B(_db(_CH[1],_CH[2],_CH[3],_CG[2],_CF[1],_CF[2],_CF[3],_9));return [0,E(_CI[1]),_CI[2]];})]);});},_Cu]);});},_CJ=function(_CK,_CL,_CM,_CN,_CO){return new F(function(){return A(_xM,[_CK,function(_CP,_CQ,_CR){return new F(function(){return _Cp(_CP,_CQ,_CL,function(_CS,_CT,_CU){return new F(function(){return A(_CL,[_CS,_CT,new T(function(){return B(_e0(_CR,_CU));})]);});},function(_CV){return new F(function(){return A(_CM,[new T(function(){return B(_e0(_CR,_CV));})]);});});});},_CM,function(_CW,_CX,_CY){return new F(function(){return _Cp(_CW,_CX,_CL,function(_CZ,_D0,_D1){return new F(function(){return A(_CN,[_CZ,_D0,new T(function(){return B(_e0(_CY,_D1));})]);});},function(_D2){return new F(function(){return A(_CO,[new T(function(){return B(_e0(_CY,_D2));})]);});});});},_CO]);});},_D3=function(_D4,_D5,_D6,_D7,_D8){return new F(function(){return _CJ(_D4,_D5,_D6,_D7,function(_D9){var _Da=E(_D4),_Db=E(_Da[2]),_Dc=E(_Da[1]);return _Dc[0]==0?B(A(_D8,[new T(function(){var _Dd=E(_D9),_De=E(_Dd[1]),_Df=B(_db(_De[1],_De[2],_De[3],_Dd[2],_Db[1],_Db[2],_Db[3],_AA));return [0,E(_Df[1]),_Df[2]];})])):B(A(_D5,[_Dc[1],[0,_Dc[2],E(_Db),E(_Da[3])],[0,E(_Db),_9]]));});});},_Dg=function(_Dh,_Di,_Dj,_Dk,_Dl){return new F(function(){return _dy(_D3,_Dh,_Di,_Dj,_Dk);});},_Dm=function(_Dn,_Do,_Dp){return [0,_Dn,E(E(_Do)),_Dp];},_Dq=function(_Dr,_Ds,_Dt){var _Du=new T(function(){return B(_iZ(_Dr));}),_Dv=new T(function(){return B(_iZ(_Dr));});return new F(function(){return A(_Ds,[_Dt,function(_Dw,_Dx,_Dy){return new F(function(){return A(_Du,[[0,new T(function(){return B(A(_Dv,[new T(function(){return B(_Dm(_Dw,_Dx,_Dy));})]));})]]);});},function(_Dz){return new F(function(){return A(_Du,[[0,new T(function(){return B(A(_Dv,[[1,_Dz]]));})]]);});},function(_DA,_DB,_DC){return new F(function(){return A(_Du,[new T(function(){return [1,E(B(A(_Dv,[new T(function(){return B(_Dm(_DA,_DB,_DC));})])))];})]);});},function(_DD){return new F(function(){return A(_Du,[new T(function(){return [1,E(B(A(_Dv,[[1,_DD]])))];})]);});}]);});},_DE=function(_DF){return function(_DG,_DH,_DI,_DJ,_DK){return new F(function(){return A(_DJ,[new T(function(){var _DL=B(_Dq(_Cm,_DM,[0,new T(function(){var _DN=B(_Dq(_Cm,_Dg,[0,_DF,E(_Cf),E(_6B)]));if(!_DN[0]){var _DO=E(_DN[1]),_DP=_DO[0]==0?E(_DO[1]):B(_Cn(_DO[1]));}else{var _DQ=E(_DN[1]),_DP=_DQ[0]==0?E(_DQ[1]):B(_Cn(_DQ[1]));}return _DP;}),E(_Cf),E(_6B)]));if(!_DL[0]){var _DR=E(_DL[1]),_DS=_DR[0]==0?E(_DR[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_DR[1]));})));})],_9],_9],_Ce];}else{var _DT=E(_DL[1]),_DS=_DT[0]==0?E(_DT[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_DT[1]));})));})],_9],_9],_Ce];}return _DS;}),_DG,new T(function(){return [0,E(E(_DG)[2]),_9];})]);});};},_DU=function(_DV,_DW,_DX,_DY,_DZ){return new F(function(){return _BU(_DV,function(_E0,_E1,_E2){return new F(function(){return A(_DE,[_E0,_E1,_DW,_DX,function(_E3,_E4,_E5){return new F(function(){return A(_DW,[_E3,_E4,new T(function(){return B(_e0(_E2,_E5));})]);});},function(_E6){return new F(function(){return A(_DX,[new T(function(){return B(_e0(_E2,_E6));})]);});}]);});},_DX,function(_E7,_E8,_E9){return new F(function(){return A(_DE,[_E7,_E8,_DW,_DX,function(_Ea,_Eb,_Ec){return new F(function(){return A(_DY,[_Ea,_Eb,new T(function(){return B(_e0(_E9,_Ec));})]);});},function(_Ed){return new F(function(){return A(_DZ,[new T(function(){return B(_e0(_E9,_Ed));})]);});}]);});},_DZ);});},_Ee=function(_Ef,_Eg,_Eh,_Ei,_Ej,_Ek){var _El=function(_Em,_En,_Eo,_Ep,_Eq){var _Er=function(_Es,_Et,_Eu,_Ev,_Ew){return new F(function(){return A(_Ep,[[0,[1,[0,_Ef,_Et,_Eu]],_Es],_Ev,new T(function(){var _Ex=E(_Ew),_Ey=E(_Ex[1]),_Ez=E(E(_Ev)[2]),_EA=B(_db(_Ey[1],_Ey[2],_Ey[3],_Ex[2],_Ez[1],_Ez[2],_Ez[3],_9));return [0,E(_EA[1]),_EA[2]];})]);});},_EB=function(_EC){return new F(function(){return _Er(_9,_wq,_9,_Em,new T(function(){var _ED=E(E(_Em)[2]),_EE=E(_EC),_EF=E(_EE[1]),_EG=B(_db(_EF[1],_EF[2],_EF[3],_EE[2],_ED[1],_ED[2],_ED[3],_9));return [0,E(_EG[1]),_EG[2]];}));});};return new F(function(){return _DU(_Em,function(_EH,_EI,_EJ){var _EK=E(_EH),_EL=E(_EK[2]);return new F(function(){return A(_En,[[0,[1,[0,_Ef,_EL[1],_EL[2]]],_EK[1]],_EI,new T(function(){var _EM=E(_EJ),_EN=E(_EM[1]),_EO=E(E(_EI)[2]),_EP=B(_db(_EN[1],_EN[2],_EN[3],_EM[2],_EO[1],_EO[2],_EO[3],_9));return [0,E(_EP[1]),_EP[2]];})]);});},_EB,function(_EQ,_ER,_ES){var _ET=E(_EQ),_EU=E(_ET[2]);return new F(function(){return _Er(_ET[1],_EU[1],_EU[2],_ER,_ES);});},_EB);});};return new F(function(){return A(_xM,[_Eg,function(_EV,_EW,_EX){return new F(function(){return _El(_EW,_Eh,_Ei,function(_EY,_EZ,_F0){return new F(function(){return A(_Eh,[_EY,_EZ,new T(function(){return B(_e0(_EX,_F0));})]);});},function(_F1){return new F(function(){return A(_Ei,[new T(function(){return B(_e0(_EX,_F1));})]);});});});},_Ei,function(_F2,_F3,_F4){return new F(function(){return _El(_F3,_Eh,_Ei,function(_F5,_F6,_F7){return new F(function(){return A(_Ej,[_F5,_F6,new T(function(){return B(_e0(_F4,_F7));})]);});},function(_F8){return new F(function(){return A(_Ek,[new T(function(){return B(_e0(_F4,_F8));})]);});});});},_Ek]);});},_F9=new T(function(){return B(unCStr(" associative operator"));}),_Fa=function(_Fb,_Fc){var _Fd=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_Fb,_F9));}))))];}),_9];return function(_Fe,_Ff,_Fg,_Fh,_Fi){return new F(function(){return A(_Fc,[_Fe,function(_Fj,_Fk,_Fl){return new F(function(){return A(_Fi,[new T(function(){var _Fm=E(E(_Fk)[2]),_Fn=E(_Fl),_Fo=E(_Fn[1]),_Fp=B(_db(_Fo[1],_Fo[2],_Fo[3],_Fn[2],_Fm[1],_Fm[2],_Fm[3],_Fd));return [0,E(_Fp[1]),_Fp[2]];})]);});},_Fi,function(_Fq,_Fr,_Fs){return new F(function(){return A(_Fi,[new T(function(){var _Ft=E(E(_Fr)[2]),_Fu=E(_Fs),_Fv=E(_Fu[1]),_Fw=B(_db(_Fv[1],_Fv[2],_Fv[3],_Fu[2],_Ft[1],_Ft[2],_Ft[3],_Fd));return [0,E(_Fw[1]),_Fw[2]];})]);});},_Fi]);});};},_Fx=function(_Fy,_Fz,_FA,_FB,_FC,_FD){var _FE=E(_Fy);if(!_FE[0]){return new F(function(){return A(_FD,[new T(function(){return [0,E(E(_Fz)[2]),_9];})]);});}else{return new F(function(){return A(_FE[1],[_Fz,_FA,_FB,_FC,function(_FF){return new F(function(){return _Fx(_FE[2],_Fz,_FA,_FB,function(_FG,_FH,_FI){return new F(function(){return A(_FC,[_FG,_FH,new T(function(){return B(_e0(_FF,_FI));})]);});},function(_FJ){return new F(function(){return A(_FD,[new T(function(){return B(_e0(_FF,_FJ));})]);});});});}]);});}},_FK=new T(function(){return B(unCStr("right"));}),_FL=new T(function(){return B(unCStr("left"));}),_FM=new T(function(){return B(unCStr("non"));}),_FN=new T(function(){return B(unCStr("operator"));}),_FO=[1,_FN,_9],_FP=[1,_9,_9],_FQ=function(_FR){var _FS=E(_FR);if(!_FS[0]){return [0,_9,_9,_9,_9,_9];}else{var _FT=_FS[2],_FU=E(_FS[1]);switch(_FU[0]){case 0:var _FV=_FU[1],_FW=B(_FQ(_FT)),_FX=_FW[1],_FY=_FW[2],_FZ=_FW[3],_G0=_FW[4],_G1=_FW[5];switch(E(_FU[2])){case 0:return [0,_FX,_FY,[1,_FV,_FZ],_G0,_G1];case 1:return [0,_FX,[1,_FV,_FY],_FZ,_G0,_G1];default:return [0,[1,_FV,_FX],_FY,_FZ,_G0,_G1];}break;case 1:var _G2=B(_FQ(_FT));return [0,_G2[1],_G2[2],_G2[3],[1,_FU[1],_G2[4]],_G2[5]];default:var _G3=B(_FQ(_FT));return [0,_G3[1],_G3[2],_G3[3],_G3[4],[1,_FU[1],_G3[5]]];}}},_G4=function(_G5,_G6){while(1){var _G7=(function(_G8,_G9){var _Ga=E(_G9);if(!_Ga[0]){return E(_G8);}else{var _Gb=new T(function(){var _Gc=B(_FQ(_Ga[1]));return [0,_Gc[1],_Gc[2],_Gc[3],_Gc[4],_Gc[5]];}),_Gd=new T(function(){return E(E(_Gb)[2]);}),_Ge=new T(function(){return B(_Fa(_FL,function(_Gf,_Gg,_Gh,_Gi,_Gj){return new F(function(){return _Fx(_Gd,_Gf,_Gg,_Gh,_Gi,_Gj);});}));}),_Gk=new T(function(){return E(E(_Gb)[1]);}),_Gl=new T(function(){return E(E(_Gb)[3]);}),_Gm=new T(function(){return B(_Fa(_FM,function(_Gn,_Go,_Gp,_Gq,_Gr){return new F(function(){return _Fx(_Gl,_Gn,_Go,_Gp,_Gq,_Gr);});}));}),_Gs=function(_Gt,_Gu,_Gv,_Gw,_Gx,_Gy){var _Gz=function(_GA,_GB,_GC,_GD,_GE){var _GF=new T(function(){return B(A(_Gt,[_GA]));});return new F(function(){return _Fx(new T(function(){return E(E(_Gb)[5]);}),_GB,function(_GG,_GH,_GI){return new F(function(){return A(_GC,[new T(function(){return B(A(_GG,[_GF]));}),_GH,new T(function(){var _GJ=E(E(_GH)[2]),_GK=E(_GI),_GL=E(_GK[1]),_GM=B(_db(_GL[1],_GL[2],_GL[3],_GK[2],_GJ[1],_GJ[2],_GJ[3],_9));return [0,E(_GM[1]),_GM[2]];})]);});},_GD,function(_GN,_GO,_GP){return new F(function(){return A(_GE,[new T(function(){return B(A(_GN,[_GF]));}),_GO,new T(function(){var _GQ=E(E(_GO)[2]),_GR=_GQ[1],_GS=_GQ[2],_GT=_GQ[3],_GU=E(_GP),_GV=E(_GU[1]),_GW=_GV[2],_GX=_GV[3],_GY=E(_GU[2]);if(!_GY[0]){switch(B(_d3(_GV[1],_GR))){case 0:var _GZ=[0,E(_GQ),_9];break;case 1:if(_GW>=_GS){if(_GW!=_GS){var _H0=[0,E(_GV),_9];}else{if(_GX>=_GT){var _H1=_GX!=_GT?[0,E(_GV),_9]:[0,E(_GV),_da];}else{var _H1=[0,E(_GQ),_9];}var _H2=_H1,_H0=_H2;}var _H3=_H0,_H4=_H3;}else{var _H4=[0,E(_GQ),_9];}var _H5=_H4,_GZ=_H5;break;default:var _GZ=[0,E(_GV),_9];}var _H6=_GZ;}else{var _H7=B(_jn(_GV,_GY,_FP)),_H8=E(_H7[1]),_H9=B(_db(_H8[1],_H8[2],_H8[3],_H7[2],_GR,_GS,_GT,_9)),_H6=[0,E(_H9[1]),_H9[2]];}var _Ha=_H6,_Hb=_Ha,_Hc=_Hb,_Hd=_Hc;return _Hd;})]);});},function(_He){return new F(function(){return A(_GE,[_GF,_GB,new T(function(){var _Hf=E(E(_GB)[2]),_Hg=_Hf[1],_Hh=_Hf[2],_Hi=_Hf[3],_Hj=E(_He),_Hk=B(_jn(_Hj[1],_Hj[2],_FP)),_Hl=E(_Hk[1]),_Hm=B(_db(_Hl[1],_Hl[2],_Hl[3],_Hk[2],_Hg,_Hh,_Hi,_9)),_Hn=E(_Hm[1]),_Ho=B(_db(_Hn[1],_Hn[2],_Hn[3],_Hm[2],_Hg,_Hh,_Hi,_9));return [0,E(_Ho[1]),_Ho[2]];})]);});});});};return new F(function(){return A(_G8,[_Gu,function(_Hp,_Hq,_Hr){return new F(function(){return _Gz(_Hp,_Hq,_Gv,_Gw,function(_Hs,_Ht,_Hu){return new F(function(){return A(_Gv,[_Hs,_Ht,new T(function(){return B(_e0(_Hr,_Hu));})]);});});});},_Gw,function(_Hv,_Hw,_Hx){return new F(function(){return _Gz(_Hv,_Hw,_Gv,_Gw,function(_Hy,_Hz,_HA){return new F(function(){return A(_Gx,[_Hy,_Hz,new T(function(){return B(_e0(_Hx,_HA));})]);});});});},_Gy]);});},_HB=function(_HC,_HD,_HE,_HF,_HG){var _HH=function(_HI,_HJ,_HK){return new F(function(){return _Gs(_HI,_HJ,_HD,_HE,function(_HL,_HM,_HN){return new F(function(){return A(_HF,[_HL,_HM,new T(function(){return B(_e0(_HK,_HN));})]);});},function(_HO){return new F(function(){return A(_HG,[new T(function(){return B(_e0(_HK,_HO));})]);});});});};return new F(function(){return _Fx(new T(function(){return E(E(_Gb)[4]);}),_HC,function(_HP,_HQ,_HR){return new F(function(){return _Gs(_HP,_HQ,_HD,_HE,function(_HS,_HT,_HU){return new F(function(){return A(_HD,[_HS,_HT,new T(function(){return B(_e0(_HR,_HU));})]);});},function(_HV){return new F(function(){return A(_HE,[new T(function(){return B(_e0(_HR,_HV));})]);});});});},_HE,function(_HW,_HX,_HY){return new F(function(){return _HH(_HW,_HX,new T(function(){var _HZ=E(_HY),_I0=E(_HZ[2]);if(!_I0[0]){var _I1=E(_HZ);}else{var _I2=B(_jn(_HZ[1],_I0,_FP)),_I1=[0,E(_I2[1]),_I2[2]];}var _I3=_I1;return _I3;}));});},function(_I4){return new F(function(){return _HH(_6P,_HC,new T(function(){var _I5=E(E(_HC)[2]),_I6=E(_I4),_I7=B(_jn(_I6[1],_I6[2],_FP)),_I8=E(_I7[1]),_I9=B(_db(_I8[1],_I8[2],_I8[3],_I7[2],_I5[1],_I5[2],_I5[3],_9));return [0,E(_I9[1]),_I9[2]];}));});});});},_Ia=function(_Ib,_Ic,_Id,_Ie,_If,_Ig){var _Ih=function(_Ii){return new F(function(){return A(_Ge,[_Ic,_Id,_Ie,function(_Ij,_Ik,_Il){return new F(function(){return A(_If,[_Ij,_Ik,new T(function(){return B(_e0(_Ii,_Il));})]);});},function(_Im){return new F(function(){return A(_Gm,[_Ic,_Id,_Ie,function(_In,_Io,_Ip){return new F(function(){return A(_If,[_In,_Io,new T(function(){var _Iq=E(_Ii),_Ir=E(_Iq[1]),_Is=E(_Im),_It=E(_Is[1]),_Iu=E(_Ip),_Iv=E(_Iu[1]),_Iw=B(_db(_It[1],_It[2],_It[3],_Is[2],_Iv[1],_Iv[2],_Iv[3],_Iu[2])),_Ix=E(_Iw[1]),_Iy=B(_db(_Ir[1],_Ir[2],_Ir[3],_Iq[2],_Ix[1],_Ix[2],_Ix[3],_Iw[2]));return [0,E(_Iy[1]),_Iy[2]];})]);});},function(_Iz){return new F(function(){return A(_Ig,[new T(function(){var _IA=E(_Ii),_IB=E(_IA[1]),_IC=E(_Im),_ID=E(_IC[1]),_IE=E(_Iz),_IF=E(_IE[1]),_IG=B(_db(_ID[1],_ID[2],_ID[3],_IC[2],_IF[1],_IF[2],_IF[3],_IE[2])),_IH=E(_IG[1]),_II=B(_db(_IB[1],_IB[2],_IB[3],_IA[2],_IH[1],_IH[2],_IH[3],_IG[2]));return [0,E(_II[1]),_II[2]];})]);});}]);});}]);});},_IJ=function(_IK,_IL,_IM,_IN,_IO,_IP){var _IQ=function(_IR,_IS,_IT){return new F(function(){return A(_IM,[new T(function(){return B(A(_IK,[_Ib,_IR]));}),_IS,new T(function(){var _IU=E(E(_IS)[2]),_IV=E(_IT),_IW=E(_IV[1]),_IX=B(_db(_IW[1],_IW[2],_IW[3],_IV[2],_IU[1],_IU[2],_IU[3],_9));return [0,E(_IX[1]),_IX[2]];})]);});};return new F(function(){return _HB(_IL,function(_IY,_IZ,_J0){return new F(function(){return _Ia(_IY,_IZ,_IQ,_IN,function(_J1,_J2,_J3){return new F(function(){return _IQ(_J1,_J2,new T(function(){var _J4=E(_J0),_J5=E(_J4[1]),_J6=E(_J3),_J7=E(_J6[1]),_J8=B(_db(_J5[1],_J5[2],_J5[3],_J4[2],_J7[1],_J7[2],_J7[3],_J6[2]));return [0,E(_J8[1]),_J8[2]];},1));});},function(_J9){return new F(function(){return _IQ(_IY,_IZ,new T(function(){var _Ja=E(E(_IZ)[2]),_Jb=E(_J0),_Jc=E(_Jb[1]),_Jd=E(_J9),_Je=E(_Jd[1]),_Jf=B(_db(_Je[1],_Je[2],_Je[3],_Jd[2],_Ja[1],_Ja[2],_Ja[3],_9)),_Jg=E(_Jf[1]),_Jh=B(_db(_Jc[1],_Jc[2],_Jc[3],_Jb[2],_Jg[1],_Jg[2],_Jg[3],_Jf[2]));return [0,E(_Jh[1]),_Jh[2]];},1));});});});},_IN,function(_Ji,_Jj,_Jk){var _Jl=function(_Jm,_Jn,_Jo){return new F(function(){return A(_IO,[new T(function(){return B(A(_IK,[_Ib,_Jm]));}),_Jn,new T(function(){var _Jp=E(E(_Jn)[2]),_Jq=E(_Jk),_Jr=E(_Jq[1]),_Js=E(_Jo),_Jt=E(_Js[1]),_Ju=B(_db(_Jr[1],_Jr[2],_Jr[3],_Jq[2],_Jt[1],_Jt[2],_Jt[3],_Js[2])),_Jv=E(_Ju[1]),_Jw=B(_db(_Jv[1],_Jv[2],_Jv[3],_Ju[2],_Jp[1],_Jp[2],_Jp[3],_9));return [0,E(_Jw[1]),_Jw[2]];})]);});};return new F(function(){return _Ia(_Ji,_Jj,_IQ,_IN,_Jl,function(_Jx){return new F(function(){return _Jl(_Ji,_Jj,new T(function(){var _Jy=E(E(_Jj)[2]),_Jz=E(_Jx),_JA=E(_Jz[1]),_JB=B(_db(_JA[1],_JA[2],_JA[3],_Jz[2],_Jy[1],_Jy[2],_Jy[3],_9));return [0,E(_JB[1]),_JB[2]];},1));});});});},_IP);});};return new F(function(){return _Fx(_Gk,_Ic,function(_JC,_JD,_JE){return new F(function(){return _IJ(_JC,_JD,_Id,_Ie,function(_JF,_JG,_JH){return new F(function(){return A(_Id,[_JF,_JG,new T(function(){return B(_e0(_JE,_JH));})]);});},function(_JI){return new F(function(){return A(_Ie,[new T(function(){return B(_e0(_JE,_JI));})]);});});});},_Ie,function(_JJ,_JK,_JL){return new F(function(){return _IJ(_JJ,_JK,_Id,_Ie,function(_JM,_JN,_JO){return new F(function(){return A(_If,[_JM,_JN,new T(function(){return B(_e0(_JL,_JO));})]);});},function(_JP){return new F(function(){return _Ih(new T(function(){return B(_e0(_JL,_JP));}));});});});},_Ih);});},_JQ=new T(function(){return B(_Fa(_FK,function(_JR,_JS,_JT,_JU,_JV){return new F(function(){return _Fx(_Gk,_JR,_JS,_JT,_JU,_JV);});}));}),_JW=function(_JX,_JY,_JZ,_K0,_K1,_K2){var _K3=function(_K4){return new F(function(){return A(_JQ,[_JY,_JZ,_K0,function(_K5,_K6,_K7){return new F(function(){return A(_K1,[_K5,_K6,new T(function(){return B(_e0(_K4,_K7));})]);});},function(_K8){return new F(function(){return A(_Gm,[_JY,_JZ,_K0,function(_K9,_Ka,_Kb){return new F(function(){return A(_K1,[_K9,_Ka,new T(function(){var _Kc=E(_K4),_Kd=E(_Kc[1]),_Ke=E(_K8),_Kf=E(_Ke[1]),_Kg=E(_Kb),_Kh=E(_Kg[1]),_Ki=B(_db(_Kf[1],_Kf[2],_Kf[3],_Ke[2],_Kh[1],_Kh[2],_Kh[3],_Kg[2])),_Kj=E(_Ki[1]),_Kk=B(_db(_Kd[1],_Kd[2],_Kd[3],_Kc[2],_Kj[1],_Kj[2],_Kj[3],_Ki[2]));return [0,E(_Kk[1]),_Kk[2]];})]);});},function(_Kl){return new F(function(){return A(_K2,[new T(function(){var _Km=E(_K4),_Kn=E(_Km[1]),_Ko=E(_K8),_Kp=E(_Ko[1]),_Kq=E(_Kl),_Kr=E(_Kq[1]),_Ks=B(_db(_Kp[1],_Kp[2],_Kp[3],_Ko[2],_Kr[1],_Kr[2],_Kr[3],_Kq[2])),_Kt=E(_Ks[1]),_Ku=B(_db(_Kn[1],_Kn[2],_Kn[3],_Km[2],_Kt[1],_Kt[2],_Kt[3],_Ks[2]));return [0,E(_Ku[1]),_Ku[2]];})]);});}]);});}]);});},_Kv=function(_Kw,_Kx,_Ky,_Kz,_KA,_KB){var _KC=function(_KD){var _KE=new T(function(){return B(A(_Kw,[_JX,_KD]));});return function(_KF,_KG,_KH,_KI,_KJ){return new F(function(){return _JW(_KE,_KF,_KG,_KH,_KI,function(_KK){return new F(function(){return A(_KI,[_KE,_KF,new T(function(){var _KL=E(E(_KF)[2]),_KM=E(_KK),_KN=E(_KM[1]),_KO=B(_db(_KN[1],_KN[2],_KN[3],_KM[2],_KL[1],_KL[2],_KL[3],_9));return [0,E(_KO[1]),_KO[2]];})]);});});});};};return new F(function(){return _HB(_Kx,function(_KP,_KQ,_KR){return new F(function(){return A(_KC,[_KP,_KQ,_Ky,_Kz,function(_KS,_KT,_KU){return new F(function(){return A(_Ky,[_KS,_KT,new T(function(){return B(_e0(_KR,_KU));})]);});},function(_KV){return new F(function(){return A(_Kz,[new T(function(){return B(_e0(_KR,_KV));})]);});}]);});},_Kz,function(_KW,_KX,_KY){return new F(function(){return A(_KC,[_KW,_KX,_Ky,_Kz,function(_KZ,_L0,_L1){return new F(function(){return A(_KA,[_KZ,_L0,new T(function(){return B(_e0(_KY,_L1));})]);});},function(_L2){return new F(function(){return A(_KB,[new T(function(){return B(_e0(_KY,_L2));})]);});}]);});},_KB);});};return new F(function(){return _Fx(_Gd,_JY,function(_L3,_L4,_L5){return new F(function(){return _Kv(_L3,_L4,_JZ,_K0,function(_L6,_L7,_L8){return new F(function(){return A(_JZ,[_L6,_L7,new T(function(){return B(_e0(_L5,_L8));})]);});},function(_L9){return new F(function(){return A(_K0,[new T(function(){return B(_e0(_L5,_L9));})]);});});});},_K0,function(_La,_Lb,_Lc){return new F(function(){return _Kv(_La,_Lb,_JZ,_K0,function(_Ld,_Le,_Lf){return new F(function(){return A(_K1,[_Ld,_Le,new T(function(){return B(_e0(_Lc,_Lf));})]);});},function(_Lg){return new F(function(){return _K3(new T(function(){return B(_e0(_Lc,_Lg));}));});});});},_K3);});},_Lh=function(_Li,_Lj,_Lk,_Ll,_Lm,_Ln){var _Lo=function(_Lp,_Lq,_Lr,_Ls,_Lt,_Lu){var _Lv=function(_Lw){return function(_Lx,_Ly,_Lz,_LA,_LB){return new F(function(){return A(_JQ,[_Lx,_Ly,_Lz,_LA,function(_LC){return new F(function(){return A(_Ge,[_Lx,_Ly,_Lz,function(_LD,_LE,_LF){return new F(function(){return A(_LA,[_LD,_LE,new T(function(){return B(_e0(_LC,_LF));})]);});},function(_LG){return new F(function(){return A(_Gm,[_Lx,_Ly,_Lz,function(_LH,_LI,_LJ){return new F(function(){return A(_LA,[_LH,_LI,new T(function(){var _LK=E(_LC),_LL=E(_LK[1]),_LM=E(_LG),_LN=E(_LM[1]),_LO=E(_LJ),_LP=E(_LO[1]),_LQ=B(_db(_LN[1],_LN[2],_LN[3],_LM[2],_LP[1],_LP[2],_LP[3],_LO[2])),_LR=E(_LQ[1]),_LS=B(_db(_LL[1],_LL[2],_LL[3],_LK[2],_LR[1],_LR[2],_LR[3],_LQ[2]));return [0,E(_LS[1]),_LS[2]];})]);});},function(_LT){return new F(function(){return A(_LA,[new T(function(){return B(A(_Lp,[_Li,_Lw]));}),_Lx,new T(function(){var _LU=E(E(_Lx)[2]),_LV=E(_LC),_LW=E(_LV[1]),_LX=E(_LG),_LY=E(_LX[1]),_LZ=E(_LT),_M0=E(_LZ[1]),_M1=B(_db(_M0[1],_M0[2],_M0[3],_LZ[2],_LU[1],_LU[2],_LU[3],_9)),_M2=E(_M1[1]),_M3=B(_db(_LY[1],_LY[2],_LY[3],_LX[2],_M2[1],_M2[2],_M2[3],_M1[2])),_M4=E(_M3[1]),_M5=B(_db(_LW[1],_LW[2],_LW[3],_LV[2],_M4[1],_M4[2],_M4[3],_M3[2]));return [0,E(_M5[1]),_M5[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _HB(_Lq,function(_M6,_M7,_M8){return new F(function(){return A(_Lv,[_M6,_M7,_Lr,_Ls,function(_M9,_Ma,_Mb){return new F(function(){return A(_Lr,[_M9,_Ma,new T(function(){return B(_e0(_M8,_Mb));})]);});},function(_Mc){return new F(function(){return A(_Ls,[new T(function(){return B(_e0(_M8,_Mc));})]);});}]);});},_Ls,function(_Md,_Me,_Mf){return new F(function(){return A(_Lv,[_Md,_Me,_Lr,_Ls,function(_Mg,_Mh,_Mi){return new F(function(){return A(_Lt,[_Mg,_Mh,new T(function(){return B(_e0(_Mf,_Mi));})]);});},function(_Mj){return new F(function(){return A(_Lu,[new T(function(){return B(_e0(_Mf,_Mj));})]);});}]);});},_Lu);});};return new F(function(){return _jI(function(_Mk,_Ml,_Mm,_Mn,_Mo){return new F(function(){return _Ia(_Li,_Mk,_Ml,_Mm,_Mn,function(_Mp){return new F(function(){return _JW(_Li,_Mk,_Ml,_Mm,function(_Mq,_Mr,_Ms){return new F(function(){return A(_Mn,[_Mq,_Mr,new T(function(){return B(_e0(_Mp,_Ms));})]);});},function(_Mt){var _Mu=function(_Mv){return new F(function(){return A(_Mn,[_Li,_Mk,new T(function(){var _Mw=E(E(_Mk)[2]),_Mx=E(_Mp),_My=E(_Mx[1]),_Mz=E(_Mt),_MA=E(_Mz[1]),_MB=E(_Mv),_MC=E(_MB[1]),_MD=B(_db(_MC[1],_MC[2],_MC[3],_MB[2],_Mw[1],_Mw[2],_Mw[3],_9)),_ME=E(_MD[1]),_MF=B(_db(_MA[1],_MA[2],_MA[3],_Mz[2],_ME[1],_ME[2],_ME[3],_MD[2])),_MG=E(_MF[1]),_MH=B(_db(_My[1],_My[2],_My[3],_Mx[2],_MG[1],_MG[2],_MG[3],_MF[2]));return [0,E(_MH[1]),_MH[2]];})]);});};return new F(function(){return _Fx(_Gl,_Mk,function(_MI,_MJ,_MK){return new F(function(){return _Lo(_MI,_MJ,_Ml,_Mm,function(_ML,_MM,_MN){return new F(function(){return A(_Ml,[_ML,_MM,new T(function(){return B(_e0(_MK,_MN));})]);});},function(_MO){return new F(function(){return A(_Mm,[new T(function(){return B(_e0(_MK,_MO));})]);});});});},_Mm,function(_MP,_MQ,_MR){return new F(function(){return _Lo(_MP,_MQ,_Ml,_Mm,function(_MS,_MT,_MU){return new F(function(){return A(_Mn,[_MS,_MT,new T(function(){var _MV=E(_Mp),_MW=E(_MV[1]),_MX=E(_Mt),_MY=E(_MX[1]),_MZ=E(_MR),_N0=E(_MZ[1]),_N1=E(_MU),_N2=E(_N1[1]),_N3=B(_db(_N0[1],_N0[2],_N0[3],_MZ[2],_N2[1],_N2[2],_N2[3],_N1[2])),_N4=E(_N3[1]),_N5=B(_db(_MY[1],_MY[2],_MY[3],_MX[2],_N4[1],_N4[2],_N4[3],_N3[2])),_N6=E(_N5[1]),_N7=B(_db(_MW[1],_MW[2],_MW[3],_MV[2],_N6[1],_N6[2],_N6[3],_N5[2]));return [0,E(_N7[1]),_N7[2]];})]);});},function(_N8){return new F(function(){return _Mu(new T(function(){var _N9=E(_MR),_Na=E(_N9[1]),_Nb=E(_N8),_Nc=E(_Nb[1]),_Nd=B(_db(_Na[1],_Na[2],_Na[3],_N9[2],_Nc[1],_Nc[2],_Nc[3],_Nb[2]));return [0,E(_Nd[1]),_Nd[2]];},1));});});});},_Mu);});});});});});},_FO,_Lj,_Lk,_Ll,_Lm,_Ln);});};_G5=function(_Ne,_Nf,_Ng,_Nh,_Ni){return new F(function(){return _HB(_Ne,function(_Nj,_Nk,_Nl){return new F(function(){return _Lh(_Nj,_Nk,_Nf,_Ng,function(_Nm,_Nn,_No){return new F(function(){return A(_Nf,[_Nm,_Nn,new T(function(){return B(_e0(_Nl,_No));})]);});},function(_Np){return new F(function(){return A(_Ng,[new T(function(){return B(_e0(_Nl,_Np));})]);});});});},_Ng,function(_Nq,_Nr,_Ns){return new F(function(){return _Lh(_Nq,_Nr,_Nf,_Ng,function(_Nt,_Nu,_Nv){return new F(function(){return A(_Nh,[_Nt,_Nu,new T(function(){return B(_e0(_Ns,_Nv));})]);});},function(_Nw){return new F(function(){return A(_Ni,[new T(function(){return B(_e0(_Ns,_Nw));})]);});});});},_Ni);});};_G6=_Ga[2];return null;}})(_G5,_G6);if(_G7!=null){return _G7;}}},_Nx=0,_Ny=[3,_],_Nz=function(_NA,_NB){return [5,_Ny,_NA,_NB];},_NC=new T(function(){return B(unCStr("=>"));}),_ND=function(_NE){return E(E(_NE)[1]);},_NF=function(_NG,_NH,_NI,_NJ){while(1){var _NK=E(_NJ);if(!_NK[0]){return [0,_NG,_NH,_NI];}else{var _NL=_NK[2];switch(E(E(_NK[1])[1])){case 9:var _NM=(_NI+8|0)-B(_gt(_NI-1|0,8))|0;_NJ=_NL;_NI=_NM;continue;case 10:var _NN=_NH+1|0;_NI=1;_NJ=_NL;_NH=_NN;continue;default:var _NM=_NI+1|0;_NJ=_NL;_NI=_NM;continue;}}}},_NO=function(_NP){return E(E(_NP)[1]);},_NQ=function(_NR){return E(E(_NR)[2]);},_NS=function(_NT){return [0,E(E(_NT)[2]),_9];},_NU=function(_NV,_NW,_NX,_NY,_NZ,_O0,_O1){var _O2=E(_NW);if(!_O2[0]){return new F(function(){return A(_O0,[_9,_NX,new T(function(){return B(_NS(_NX));})]);});}else{var _O3=E(_NX),_O4=E(_O3[2]),_O5=new T(function(){return B(_ND(_NV));}),_O6=[0,E(_O4),[1,[2,E([1,_gp,new T(function(){return B(_if(_O2,_gq));})])],_gs]],_O7=[2,E([1,_gp,new T(function(){return B(_if(_O2,_gq));})])],_O8=new T(function(){var _O9=B(_NF(_O4[1],_O4[2],_O4[3],_O2));return [0,_O9[1],_O9[2],_O9[3]];}),_Oa=function(_Ob,_Oc){var _Od=E(_Ob);if(!_Od[0]){return new F(function(){return A(_NY,[_O2,new T(function(){return [0,_Oc,E(E(_O8)),E(_O3[3])];}),new T(function(){return [0,E(E(_O8)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_NO(_O5));}),[new T(function(){return B(A(new T(function(){return B(_NQ(_NV));}),[_Oc]));}),function(_Oe){var _Of=E(_Oe);if(!_Of[0]){return E(new T(function(){return B(A(_NZ,[_O6]));}));}else{var _Og=E(_Of[1]),_Oh=E(_Og[1]);return E(_Od[1])[1]!=_Oh[1]?B(A(_NZ,[[0,E(_O4),[1,_O7,[1,[0,E([1,_gp,new T(function(){return B(_if([1,_Oh,_9],_gq));})])],_9]]]])):B(_Oa(_Od[2],_Og[2]));}}]);});}};return new F(function(){return A(_NO,[_O5,new T(function(){return B(A(_NQ,[_NV,_O3[1]]));}),function(_Oi){var _Oj=E(_Oi);if(!_Oj[0]){return E(new T(function(){return B(A(_O1,[_O6]));}));}else{var _Ok=E(_Oj[1]),_Ol=E(_Ok[1]);return E(_O2[1])[1]!=_Ol[1]?B(A(_O1,[[0,E(_O4),[1,_O7,[1,[0,E([1,_gp,new T(function(){return B(_if([1,_Ol,_9],_gq));})])],_9]]]])):B(_Oa(_O2[2],_Ok[2]));}}]);});}},_Om=function(_On,_Oo,_Op,_Oq,_Or){return new F(function(){return _NU(_ks,_NC,_On,function(_Os,_Ot,_Ou){return new F(function(){return A(_Oo,[_Nz,_Ot,new T(function(){var _Ov=E(E(_Ot)[2]),_Ow=E(_Ou),_Ox=E(_Ow[1]),_Oy=B(_db(_Ox[1],_Ox[2],_Ox[3],_Ow[2],_Ov[1],_Ov[2],_Ov[3],_9));return [0,E(_Oy[1]),_Oy[2]];})]);});},_Op,function(_Oz,_OA,_OB){return new F(function(){return A(_Oq,[_Nz,_OA,new T(function(){var _OC=E(E(_OA)[2]),_OD=E(_OB),_OE=E(_OD[1]),_OF=B(_db(_OE[1],_OE[2],_OE[3],_OD[2],_OC[1],_OC[2],_OC[3],_9));return [0,E(_OF[1]),_OF[2]];})]);});},_Or);});},_OG=[0,_Om,_Nx],_OH=[1,_OG,_9],_OI=[1,_OH,_9],_OJ=1,_OK=[2,_],_OL=function(_NA,_NB){return [5,_OK,_NA,_NB];},_OM=new T(function(){return B(unCStr("\\/"));}),_ON=function(_OO,_OP,_OQ,_OR,_OS){return new F(function(){return _NU(_ks,_OM,_OO,function(_OT,_OU,_OV){return new F(function(){return A(_OP,[_OL,_OU,new T(function(){var _OW=E(E(_OU)[2]),_OX=E(_OV),_OY=E(_OX[1]),_OZ=B(_db(_OY[1],_OY[2],_OY[3],_OX[2],_OW[1],_OW[2],_OW[3],_9));return [0,E(_OZ[1]),_OZ[2]];})]);});},_OQ,function(_P0,_P1,_P2){return new F(function(){return A(_OR,[_OL,_P1,new T(function(){var _P3=E(E(_P1)[2]),_P4=E(_P2),_P5=E(_P4[1]),_P6=B(_db(_P5[1],_P5[2],_P5[3],_P4[2],_P3[1],_P3[2],_P3[3],_9));return [0,E(_P6[1]),_P6[2]];})]);});},_OS);});},_P7=[0,_ON,_OJ],_P8=[1,_],_P9=function(_NA,_NB){return [5,_P8,_NA,_NB];},_Pa=new T(function(){return B(unCStr("/\\"));}),_Pb=function(_Pc,_Pd,_Pe,_Pf,_Pg){return new F(function(){return _NU(_ks,_Pa,_Pc,function(_Ph,_Pi,_Pj){return new F(function(){return A(_Pd,[_P9,_Pi,new T(function(){var _Pk=E(E(_Pi)[2]),_Pl=E(_Pj),_Pm=E(_Pl[1]),_Pn=B(_db(_Pm[1],_Pm[2],_Pm[3],_Pl[2],_Pk[1],_Pk[2],_Pk[3],_9));return [0,E(_Pn[1]),_Pn[2]];})]);});},_Pe,function(_Po,_Pp,_Pq){return new F(function(){return A(_Pf,[_P9,_Pp,new T(function(){var _Pr=E(E(_Pp)[2]),_Ps=E(_Pq),_Pt=E(_Ps[1]),_Pu=B(_db(_Pt[1],_Pt[2],_Pt[3],_Ps[2],_Pr[1],_Pr[2],_Pr[3],_9));return [0,E(_Pu[1]),_Pu[2]];})]);});},_Pg);});},_Pv=[0,_Pb,_OJ],_Pw=[1,_Pv,_9],_Px=[1,_P7,_Pw],_Py=[1,_Px,_OI],_Pz=[0,_],_PA=function(_NB){return [4,_Pz,_NB];},_PB=[0,45],_PC=[1,_PB,_9],_PD=function(_PE,_PF,_PG,_PH,_PI){return new F(function(){return _NU(_ks,_PC,_PE,function(_PJ,_PK,_PL){return new F(function(){return A(_PF,[_PA,_PK,new T(function(){var _PM=E(E(_PK)[2]),_PN=E(_PL),_PO=E(_PN[1]),_PP=B(_db(_PO[1],_PO[2],_PO[3],_PN[2],_PM[1],_PM[2],_PM[3],_9));return [0,E(_PP[1]),_PP[2]];})]);});},_PG,function(_PQ,_PR,_PS){return new F(function(){return A(_PH,[_PA,_PR,new T(function(){var _PT=E(E(_PR)[2]),_PU=E(_PS),_PV=E(_PU[1]),_PW=B(_db(_PV[1],_PV[2],_PV[3],_PU[2],_PT[1],_PT[2],_PT[3],_9));return [0,E(_PW[1]),_PW[2]];})]);});},_PI);});},_PX=[1,_PD],_PY=[1,_PX,_9],_PZ=[1,_PY,_Py],_Q0=new T(function(){return B(unCStr("number"));}),_Q1=[1,_Q0,_9],_Q2=new T(function(){return B(err(_kO));}),_Q3=new T(function(){return B(err(_kM));}),_Q4=new T(function(){return B(_uq(_uM,_ud,_uS));}),_Q5=function(_Q6){return function(_Q7,_Q8,_Q9,_Qa,_Qb){return new F(function(){return A(_Qa,[new T(function(){var _Qc=B(_uX(B(_kR(_Q4,_Q6))));return _Qc[0]==0?E(_Q3):E(_Qc[2])[0]==0?E(_Qc[1]):E(_Q2);}),_Q7,new T(function(){return [0,E(E(_Q7)[2]),_9];})]);});};},_Qd=function(_Qe,_Qf,_Qg,_Qh,_Qi){return new F(function(){return _e8(_ke,_Qe,function(_Qj,_Qk,_Ql){return new F(function(){return A(_Q5,[_Qj,_Qk,_Qf,_Qg,function(_Qm,_Qn,_Qo){return new F(function(){return A(_Qf,[_Qm,_Qn,new T(function(){return B(_e0(_Ql,_Qo));})]);});},function(_Qp){return new F(function(){return A(_Qg,[new T(function(){return B(_e0(_Ql,_Qp));})]);});}]);});},_Qg,function(_Qq,_Qr,_Qs){return new F(function(){return A(_Q5,[_Qq,_Qr,_Qf,_Qg,function(_Qt,_Qu,_Qv){return new F(function(){return A(_Qh,[_Qt,_Qu,new T(function(){return B(_e0(_Qs,_Qv));})]);});},function(_Qw){return new F(function(){return A(_Qi,[new T(function(){return B(_e0(_Qs,_Qw));})]);});}]);});},_Qi);});},_Qx=function(_Qy,_Qz,_QA,_QB,_QC){return new F(function(){return _Qd(_Qy,function(_QD,_QE,_QF){return new F(function(){return A(_Qz,[[1,[0,_,_QD]],_QE,new T(function(){var _QG=E(E(_QE)[2]),_QH=E(_QF),_QI=E(_QH[1]),_QJ=B(_db(_QI[1],_QI[2],_QI[3],_QH[2],_QG[1],_QG[2],_QG[3],_9));return [0,E(_QJ[1]),_QJ[2]];})]);});},_QA,function(_QK,_QL,_QM){return new F(function(){return A(_QB,[[1,[0,_,_QK]],_QL,new T(function(){var _QN=E(E(_QL)[2]),_QO=_QN[1],_QP=_QN[2],_QQ=_QN[3],_QR=E(_QM),_QS=E(_QR[1]),_QT=_QS[2],_QU=_QS[3],_QV=E(_QR[2]);if(!_QV[0]){switch(B(_d3(_QS[1],_QO))){case 0:var _QW=[0,E(_QN),_9];break;case 1:if(_QT>=_QP){if(_QT!=_QP){var _QX=[0,E(_QS),_9];}else{if(_QU>=_QQ){var _QY=_QU!=_QQ?[0,E(_QS),_9]:[0,E(_QS),_da];}else{var _QY=[0,E(_QN),_9];}var _QZ=_QY,_QX=_QZ;}var _R0=_QX,_R1=_R0;}else{var _R1=[0,E(_QN),_9];}var _R2=_R1,_QW=_R2;break;default:var _QW=[0,E(_QS),_9];}var _R3=_QW;}else{var _R4=B(_jn(_QS,_QV,_Q1)),_R5=E(_R4[1]),_R6=B(_db(_R5[1],_R5[2],_R5[3],_R4[2],_QO,_QP,_QQ,_9)),_R3=[0,E(_R6[1]),_R6[2]];}var _R7=_R3,_R8=_R7,_R9=_R8,_Ra=_R9;return _Ra;})]);});},function(_Rb){return new F(function(){return A(_QC,[new T(function(){var _Rc=E(_Rb),_Rd=B(_jn(_Rc[1],_Rc[2],_Q1));return [0,E(_Rd[1]),_Rd[2]];})]);});});});},_Re=new T(function(){return B(unCStr("P_"));}),_Rf=function(_Rg,_Rh,_Ri,_Rj,_Rk){return new F(function(){return _NU(_ks,_Re,_Rg,function(_Rl,_Rm,_Rn){return new F(function(){return _Qx(_Rm,_Rh,_Ri,function(_Ro,_Rp,_Rq){return new F(function(){return A(_Rh,[_Ro,_Rp,new T(function(){return B(_e0(_Rn,_Rq));})]);});},function(_Rr){return new F(function(){return A(_Ri,[new T(function(){return B(_e0(_Rn,_Rr));})]);});});});},_Ri,function(_Rs,_Rt,_Ru){return new F(function(){return _Qx(_Rt,_Rh,_Ri,function(_Rv,_Rw,_Rx){return new F(function(){return A(_Rj,[_Rv,_Rw,new T(function(){return B(_e0(_Ru,_Rx));})]);});},function(_Ry){return new F(function(){return A(_Rk,[new T(function(){return B(_e0(_Ru,_Ry));})]);});});});},_Rk);});},_Rz=[0,41],_RA=new T(function(){return B(_kt(_ks,_Rz));}),_RB=function(_RC,_RD,_RE,_RF,_RG,_RH){return new F(function(){return A(_RA,[_RD,function(_RI,_RJ,_RK){return new F(function(){return A(_RE,[_RC,_RJ,new T(function(){var _RL=E(E(_RJ)[2]),_RM=E(_RK),_RN=E(_RM[1]),_RO=B(_db(_RN[1],_RN[2],_RN[3],_RM[2],_RL[1],_RL[2],_RL[3],_9));return [0,E(_RO[1]),_RO[2]];})]);});},_RF,function(_RP,_RQ,_RR){return new F(function(){return A(_RG,[_RC,_RQ,new T(function(){var _RS=E(E(_RQ)[2]),_RT=E(_RR),_RU=E(_RT[1]),_RV=B(_db(_RU[1],_RU[2],_RU[3],_RT[2],_RS[1],_RS[2],_RS[3],_9));return [0,E(_RV[1]),_RV[2]];})]);});},_RH]);});},_RW=function(_RX,_RY,_RZ,_S0,_S1){return new F(function(){return A(_S2,[_RX,function(_S3,_S4,_S5){return new F(function(){return _RB(_S3,_S4,_RY,_RZ,function(_S6,_S7,_S8){return new F(function(){return A(_RY,[_S6,_S7,new T(function(){return B(_e0(_S5,_S8));})]);});},function(_S9){return new F(function(){return A(_RZ,[new T(function(){return B(_e0(_S5,_S9));})]);});});});},_RZ,function(_Sa,_Sb,_Sc){return new F(function(){return _RB(_Sa,_Sb,_RY,_RZ,function(_Sd,_Se,_Sf){return new F(function(){return A(_S0,[_Sd,_Se,new T(function(){return B(_e0(_Sc,_Sf));})]);});},function(_Sg){return new F(function(){return A(_S1,[new T(function(){return B(_e0(_Sc,_Sg));})]);});});});},_S1]);});},_Sh=[0,40],_Si=new T(function(){return B(_kt(_ks,_Sh));}),_Sj=function(_Sk,_Sl,_Sm,_Sn,_So){var _Sp=function(_Sq){return new F(function(){return _Rf(_Sk,_Sl,_Sm,function(_Sr,_Ss,_St){return new F(function(){return A(_Sn,[_Sr,_Ss,new T(function(){return B(_e0(_Sq,_St));})]);});},function(_Su){return new F(function(){return A(_So,[new T(function(){return B(_e0(_Sq,_Su));})]);});});});};return new F(function(){return A(_Si,[_Sk,function(_Sv,_Sw,_Sx){return new F(function(){return _RW(_Sw,_Sl,_Sm,function(_Sy,_Sz,_SA){return new F(function(){return A(_Sl,[_Sy,_Sz,new T(function(){return B(_e0(_Sx,_SA));})]);});},function(_SB){return new F(function(){return A(_Sm,[new T(function(){return B(_e0(_Sx,_SB));})]);});});});},_Sm,function(_SC,_SD,_SE){return new F(function(){return _RW(_SD,_Sl,_Sm,function(_SF,_SG,_SH){return new F(function(){return A(_Sn,[_SF,_SG,new T(function(){return B(_e0(_SE,_SH));})]);});},function(_SI){return new F(function(){return _Sp(new T(function(){return B(_e0(_SE,_SI));}));});});});},_Sp]);});},_S2=new T(function(){return B(_G4(_Sj,_PZ));}),_SJ=function(_SK,_SL,_SM,_SN,_SO){return new F(function(){return A(_S2,[_SK,function(_SP,_SQ,_SR){return new F(function(){return _Ee(_SP,_SQ,_SL,_SM,function(_SS,_ST,_SU){return new F(function(){return A(_SL,[_SS,_ST,new T(function(){return B(_e0(_SR,_SU));})]);});},function(_SV){return new F(function(){return A(_SM,[new T(function(){return B(_e0(_SR,_SV));})]);});});});},_SM,function(_SW,_SX,_SY){return new F(function(){return _Ee(_SW,_SX,_SL,_SM,function(_SZ,_T0,_T1){return new F(function(){return A(_SN,[_SZ,_T0,new T(function(){return B(_e0(_SY,_T1));})]);});},function(_T2){return new F(function(){return A(_SO,[new T(function(){return B(_e0(_SY,_T2));})]);});});});},_SO]);});},_T3=function(_T4,_T5,_T6,_T7,_T8){return new F(function(){return _eL(_j7,_T4,function(_T9,_Ta,_Tb){return new F(function(){return _SJ(_Ta,_T5,_T6,function(_Tc,_Td,_Te){return new F(function(){return A(_T5,[_Tc,_Td,new T(function(){return B(_e0(_Tb,_Te));})]);});},function(_Tf){return new F(function(){return A(_T6,[new T(function(){return B(_e0(_Tb,_Tf));})]);});});});},_T6,function(_Tg,_Th,_Ti){return new F(function(){return _SJ(_Th,_T5,_T6,function(_Tj,_Tk,_Tl){return new F(function(){return A(_T7,[_Tj,_Tk,new T(function(){return B(_e0(_Ti,_Tl));})]);});},function(_Tm){return new F(function(){return A(_T8,[new T(function(){return B(_e0(_Ti,_Tm));})]);});});});});});},_Tn=function(_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv){var _Tw=E(_To);if(!_Tw[0]){return new F(function(){return A(_Tv,[[0,E([0,_Tp,_Tq,_Tr]),_gs]]);});}else{var _Tx=_Tw[1];if(!B(_9r(_iN,_Tx,_wW))){return new F(function(){return A(_Tv,[[0,E([0,_Tp,_Tq,_Tr]),[1,[0,E([1,_gp,new T(function(){return B(_if([1,_Tx,_9],_gq));})])],_9]]]);});}else{var _Ty=function(_Tz,_TA,_TB,_TC){var _TD=[0,E([0,_Tz,_TA,_TB]),_9],_TE=[0,E([0,_Tz,_TA,_TB]),_da];return new F(function(){return _eL(_xu,[0,_Tw[2],E(_TC),E(_Ts)],function(_TF,_TG,_TH){return new F(function(){return _T3(_TG,_Tt,_Tu,function(_TI,_TJ,_TK){return new F(function(){return A(_Tt,[_TI,_TJ,new T(function(){return B(_e0(_TH,_TK));})]);});},function(_TL){return new F(function(){return A(_Tu,[new T(function(){return B(_e0(_TH,_TL));})]);});});});},_Tu,function(_TM,_TN,_TO){return new F(function(){return _T3(_TN,_Tt,_Tu,function(_TP,_TQ,_TR){return new F(function(){return A(_Tt,[_TP,_TQ,new T(function(){var _TS=E(_TO),_TT=E(_TS[1]),_TU=E(_TR),_TV=E(_TU[1]),_TW=B(_db(_TT[1],_TT[2],_TT[3],_TS[2],_TV[1],_TV[2],_TV[3],_TU[2])),_TX=E(_TW[1]),_TY=_TX[2],_TZ=_TX[3],_U0=E(_TW[2]);if(!_U0[0]){switch(B(_d3(_Tz,_TX[1]))){case 0:var _U1=[0,E(_TX),_9];break;case 1:if(_TA>=_TY){if(_TA!=_TY){var _U2=E(_TD);}else{if(_TB>=_TZ){var _U3=_TB!=_TZ?E(_TD):E(_TE);}else{var _U3=[0,E(_TX),_9];}var _U4=_U3,_U2=_U4;}var _U5=_U2,_U6=_U5;}else{var _U6=[0,E(_TX),_9];}var _U7=_U6,_U1=_U7;break;default:var _U1=E(_TD);}var _U8=_U1;}else{var _U8=[0,E(_TX),_U0];}var _U9=_U8,_Ua=_U9,_Ub=_Ua,_Uc=_Ub,_Ud=_Uc,_Ue=_Ud;return _Ue;})]);});},function(_Uf){return new F(function(){return A(_Tu,[new T(function(){var _Ug=E(_TO),_Uh=E(_Ug[1]),_Ui=E(_Uf),_Uj=E(_Ui[1]),_Uk=B(_db(_Uh[1],_Uh[2],_Uh[3],_Ug[2],_Uj[1],_Uj[2],_Uj[3],_Ui[2])),_Ul=E(_Uk[1]),_Um=_Ul[2],_Un=_Ul[3],_Uo=E(_Uk[2]);if(!_Uo[0]){switch(B(_d3(_Tz,_Ul[1]))){case 0:var _Up=[0,E(_Ul),_9];break;case 1:if(_TA>=_Um){if(_TA!=_Um){var _Uq=E(_TD);}else{if(_TB>=_Un){var _Ur=_TB!=_Un?E(_TD):E(_TE);}else{var _Ur=[0,E(_Ul),_9];}var _Us=_Ur,_Uq=_Us;}var _Ut=_Uq,_Uu=_Ut;}else{var _Uu=[0,E(_Ul),_9];}var _Uv=_Uu,_Up=_Uv;break;default:var _Up=E(_TD);}var _Uw=_Up;}else{var _Uw=[0,E(_Ul),_Uo];}var _Ux=_Uw,_Uy=_Ux,_Uz=_Uy,_UA=_Uz,_UB=_UA,_UC=_UB;return _UC;})]);});});});});});};switch(E(E(_Tx)[1])){case 9:var _UD=(_Tr+8|0)-B(_gt(_Tr-1|0,8))|0;return new F(function(){return _Ty(_Tp,_Tq,_UD,[0,_Tp,_Tq,_UD]);});break;case 10:var _UE=_Tq+1|0;return new F(function(){return _Ty(_Tp,_UE,1,[0,_Tp,_UE,1]);});break;default:var _UF=_Tr+1|0;return new F(function(){return _Ty(_Tp,_Tq,_UF,[0,_Tp,_Tq,_UF]);});}}}},_UG=function(_UH,_UI){return E(_1);},_UJ=function(_UK,_UL,_UM,_UN){var _UO=E(_UM);switch(_UO[0]){case 0:var _UP=E(_UN);return _UP[0]==0?E(_1):E(_UP[1]);case 1:return new F(function(){return A(_UK,[_UO[1],_9]);});break;case 2:return new F(function(){return A(_UL,[_UO[1],[1,new T(function(){return B(_UJ(_UK,_UL,_UO[2],_UN));}),_9]]);});break;default:return new F(function(){return A(_UL,[_UO[1],[1,new T(function(){return B(_UJ(_UK,_UL,_UO[2],_UN));}),[1,new T(function(){return B(_UJ(_UK,_UL,_UO[3],_UN));}),_9]]]);});}},_UQ=function(_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY){var _UZ=E(_UX);switch(_UZ[0]){case 0:return [0];case 1:return new F(function(){return A(_UU,[_UZ[1],_9]);});break;case 2:return new F(function(){return A(_UR,[_UZ[1],[1,new T(function(){return B(_UJ(_UU,_UV,_UZ[2],_UY));}),_9]]);});break;case 3:return new F(function(){return A(_UR,[_UZ[1],[1,new T(function(){return B(_UJ(_UU,_UV,_UZ[2],_UY));}),[1,new T(function(){return B(_UJ(_UU,_UV,_UZ[3],_UY));}),_9]]]);});break;case 4:return new F(function(){return A(_US,[_UZ[1],[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,_UZ[2],_UY));}),_9]]);});break;case 5:return new F(function(){return A(_US,[_UZ[1],[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,_UZ[2],_UY));}),[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,_UZ[3],_UY));}),_9]]]);});break;default:var _V0=_UZ[1],_V1=_UZ[2];return new F(function(){return A(_UT,[_V0,[1,new T(function(){return B(A(_UW,[new T(function(){return B(A(_V1,[_2V]));}),_V0]));}),[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,B(A(_V1,[_2V])),[1,new T(function(){return B(A(_UW,[new T(function(){return B(A(_V1,[_2V]));}),_V0]));}),_9]));}),_9]]]);});}},_V2=[0,95],_V3=[1,_V2,_9],_V4=[1,_V3,_9],_V5=function(_V6){var _V7=function(_V8){var _V9=E(new T(function(){var _Va=B(_Dq(_Cm,_S2,[0,_V6,E(_Cf),E(_6B)]));if(!_Va[0]){var _Vb=E(_Va[1]),_Vc=_Vb[0]==0?[1,_Vb[1]]:[0,_Vb[1]];}else{var _Vd=E(_Va[1]),_Vc=_Vd[0]==0?[1,_Vd[1]]:[0,_Vd[1]];}return _Vc;}));return _V9[0]==0?function(_Ve,_Vf,_Vg,_Vh,_Vi){return new F(function(){return A(_Vh,[[0,[0,new T(function(){var _Vj=E(_V9[1]),_Vk=E(_Vj[1]);return B(_bc(_Vk[1],_Vk[2],_Vk[3],_Vj[2]));})],_9],_Ve,new T(function(){return [0,E(E(_Ve)[2]),_9];})]);});}:function(_Vl,_Vm,_Vn,_Vo,_Vp){return new F(function(){return A(_Vo,[[0,[0,new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_V9[1],_V4));})],_9],_Vl,new T(function(){return [0,E(E(_Vl)[2]),_9];})]);});};};return function(_Vq,_Vr,_Vs,_Vt,_Vu){return new F(function(){return A(_xM,[_Vq,function(_Vv,_Vw,_Vx){return new F(function(){return A(_V7,[_,_Vw,_Vr,_Vs,function(_Vy,_Vz,_VA){return new F(function(){return A(_Vr,[_Vy,_Vz,new T(function(){return B(_e0(_Vx,_VA));})]);});},function(_VB){return new F(function(){return A(_Vs,[new T(function(){return B(_e0(_Vx,_VB));})]);});}]);});},_Vs,function(_VC,_VD,_VE){return new F(function(){return A(_V7,[_,_VD,_Vr,_Vs,function(_VF,_VG,_VH){return new F(function(){return A(_Vt,[_VF,_VG,new T(function(){return B(_e0(_VE,_VH));})]);});},function(_VI){return new F(function(){return A(_Vu,[new T(function(){return B(_e0(_VE,_VI));})]);});}]);});},_Vu]);});};},_VJ=function(_VK,_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT){return new F(function(){return _il(_VK,_VL,function(_VU){return !B(_9r(_iN,_VU,_VM))?true:false;},_VN,_VO,_VP,_VQ,_VR,_VS,_VT);});},_VV=[0,9],_VW=[1,_VV,_9],_VX=[0,10],_VY=[1,_VX,_VW],_VZ=function(_W0,_W1,_W2,_W3,_W4){var _W5=E(_W0),_W6=E(_W5[2]);return new F(function(){return _VJ(_gm,_j5,_VY,_W5[1],_W6[1],_W6[2],_W6[3],_W5[3],_W1,_W4);});},_W7=function(_W8,_W9,_Wa,_Wb,_Wc){return new F(function(){return _e8(_VZ,_W8,function(_Wd,_We,_Wf){return new F(function(){return A(_V5,[_Wd,_We,_W9,_Wa,function(_Wg,_Wh,_Wi){return new F(function(){return A(_W9,[_Wg,_Wh,new T(function(){return B(_e0(_Wf,_Wi));})]);});},function(_Wj){return new F(function(){return A(_Wa,[new T(function(){return B(_e0(_Wf,_Wj));})]);});}]);});},_Wa,function(_Wk,_Wl,_Wm){return new F(function(){return A(_V5,[_Wk,_Wl,_W9,_Wa,function(_Wn,_Wo,_Wp){return new F(function(){return A(_Wb,[_Wn,_Wo,new T(function(){return B(_e0(_Wm,_Wp));})]);});},function(_Wq){return new F(function(){return A(_Wc,[new T(function(){return B(_e0(_Wm,_Wq));})]);});}]);});},_Wc);});},_Wr=function(_Ws,_Wt,_Wu,_Wv,_Ww,_Wx){var _Wy=function(_Wz,_WA,_WB,_WC,_WD,_WE){var _WF=function(_WG){var _WH=[0,[1,[0,_Ws,_Wz,new T(function(){return B(_3d(_v4,_WG));})]],_9];return function(_WI,_WJ,_WK,_WL,_WM){return new F(function(){return A(_xM,[_WI,function(_WN,_WO,_WP){return new F(function(){return A(_WJ,[_WH,_WO,new T(function(){var _WQ=E(E(_WO)[2]),_WR=E(_WP),_WS=E(_WR[1]),_WT=B(_db(_WS[1],_WS[2],_WS[3],_WR[2],_WQ[1],_WQ[2],_WQ[3],_9));return [0,E(_WT[1]),_WT[2]];})]);});},_WK,function(_WU,_WV,_WW){return new F(function(){return A(_WL,[_WH,_WV,new T(function(){var _WX=E(E(_WV)[2]),_WY=E(_WW),_WZ=E(_WY[1]),_X0=B(_db(_WZ[1],_WZ[2],_WZ[3],_WY[2],_WX[1],_WX[2],_WX[3],_9));return [0,E(_X0[1]),_X0[2]];})]);});},_WM]);});};},_X1=function(_X2,_X3,_X4,_X5,_X6){var _X7=function(_X8,_X9,_Xa){return new F(function(){return A(_WF,[_X8,_X9,_X3,_X4,function(_Xb,_Xc,_Xd){return new F(function(){return A(_X5,[_Xb,_Xc,new T(function(){return B(_e0(_Xa,_Xd));})]);});},function(_Xe){return new F(function(){return A(_X6,[new T(function(){return B(_e0(_Xa,_Xe));})]);});}]);});},_Xf=function(_Xg){return new F(function(){return _X7(_9,_X2,new T(function(){var _Xh=E(E(_X2)[2]),_Xi=E(_Xg),_Xj=E(_Xi[1]),_Xk=B(_db(_Xj[1],_Xj[2],_Xj[3],_Xi[2],_Xh[1],_Xh[2],_Xh[3],_9));return [0,E(_Xk[1]),_Xk[2]];}));});};return new F(function(){return _fb(_kk,_kL,_X2,function(_Xl,_Xm,_Xn){return new F(function(){return A(_WF,[_Xl,_Xm,_X3,_X4,function(_Xo,_Xp,_Xq){return new F(function(){return A(_X3,[_Xo,_Xp,new T(function(){return B(_e0(_Xn,_Xq));})]);});},function(_Xr){return new F(function(){return A(_X4,[new T(function(){return B(_e0(_Xn,_Xr));})]);});}]);});},_Xf,_X7,_Xf);});};return new F(function(){return _eL(_j7,_WA,function(_Xs,_Xt,_Xu){return new F(function(){return _X1(_Xt,_WB,_WC,function(_Xv,_Xw,_Xx){return new F(function(){return A(_WB,[_Xv,_Xw,new T(function(){return B(_e0(_Xu,_Xx));})]);});},function(_Xy){return new F(function(){return A(_WC,[new T(function(){return B(_e0(_Xu,_Xy));})]);});});});},_WC,function(_Xz,_XA,_XB){return new F(function(){return _X1(_XA,_WB,_WC,function(_XC,_XD,_XE){return new F(function(){return A(_WD,[_XC,_XD,new T(function(){return B(_e0(_XB,_XE));})]);});},function(_XF){return new F(function(){return A(_WE,[new T(function(){return B(_e0(_XB,_XF));})]);});});});});});},_XG=function(_XH,_XI,_XJ,_XK,_XL){return new F(function(){return _e8(_w2,_XH,function(_XM,_XN,_XO){return new F(function(){return _Wy(_XM,_XN,_XI,_XJ,function(_XP,_XQ,_XR){return new F(function(){return A(_XI,[_XP,_XQ,new T(function(){return B(_e0(_XO,_XR));})]);});},function(_XS){return new F(function(){return A(_XJ,[new T(function(){return B(_e0(_XO,_XS));})]);});});});},_XL,function(_XT,_XU,_XV){return new F(function(){return _Wy(_XT,_XU,_XI,_XJ,function(_XW,_XX,_XY){return new F(function(){return A(_XK,[_XW,_XX,new T(function(){return B(_e0(_XV,_XY));})]);});},function(_XZ){return new F(function(){return A(_XL,[new T(function(){return B(_e0(_XV,_XZ));})]);});});});},_XL);});};return new F(function(){return _eL(_j7,_Wt,function(_Y0,_Y1,_Y2){return new F(function(){return _XG(_Y1,_Wu,_Wv,function(_Y3,_Y4,_Y5){return new F(function(){return A(_Wu,[_Y3,_Y4,new T(function(){return B(_e0(_Y2,_Y5));})]);});},function(_Y6){return new F(function(){return A(_Wv,[new T(function(){return B(_e0(_Y2,_Y6));})]);});});});},_Wv,function(_Y7,_Y8,_Y9){return new F(function(){return _XG(_Y8,_Wu,_Wv,function(_Ya,_Yb,_Yc){return new F(function(){return A(_Ww,[_Ya,_Yb,new T(function(){return B(_e0(_Y9,_Yc));})]);});},function(_Yd){return new F(function(){return A(_Wx,[new T(function(){return B(_e0(_Y9,_Yd));})]);});});});});});},_Ye=function(_Yf,_Yg,_Yh,_Yi,_Yj){return new F(function(){return A(_S2,[_Yf,function(_Yk,_Yl,_Ym){return new F(function(){return _Wr(_Yk,_Yl,_Yg,_Yh,function(_Yn,_Yo,_Yp){return new F(function(){return A(_Yg,[_Yn,_Yo,new T(function(){return B(_e0(_Ym,_Yp));})]);});},function(_Yq){return new F(function(){return A(_Yh,[new T(function(){return B(_e0(_Ym,_Yq));})]);});});});},_Yh,function(_Yr,_Ys,_Yt){return new F(function(){return _Wr(_Yr,_Ys,_Yg,_Yh,function(_Yu,_Yv,_Yw){return new F(function(){return A(_Yi,[_Yu,_Yv,new T(function(){return B(_e0(_Yt,_Yw));})]);});},function(_Yx){return new F(function(){return A(_Yj,[new T(function(){return B(_e0(_Yt,_Yx));})]);});});});},_Yj]);});},_Yy=function(_Yz,_YA,_YB,_YC){var _YD=function(_YE){var _YF=E(_Yz),_YG=E(_YF[2]),_YH=function(_YI){var _YJ=function(_YK){return new F(function(){return A(_YC,[new T(function(){var _YL=E(_YE),_YM=E(_YL[1]),_YN=E(_YI),_YO=E(_YN[1]),_YP=E(_YK),_YQ=E(_YP[1]),_YR=B(_db(_YO[1],_YO[2],_YO[3],_YN[2],_YQ[1],_YQ[2],_YQ[3],_YP[2])),_YS=E(_YR[1]),_YT=B(_db(_YM[1],_YM[2],_YM[3],_YL[2],_YS[1],_YS[2],_YS[3],_YR[2]));return [0,E(_YT[1]),_YT[2]];})]);});};return new F(function(){return _W7(_YF,_YA,_YJ,function(_YU,_YV,_YW){return new F(function(){return A(_YB,[_YU,_YV,new T(function(){var _YX=E(_YE),_YY=E(_YX[1]),_YZ=E(_YI),_Z0=E(_YZ[1]),_Z1=E(_YW),_Z2=E(_Z1[1]),_Z3=B(_db(_Z0[1],_Z0[2],_Z0[3],_YZ[2],_Z2[1],_Z2[2],_Z2[3],_Z1[2])),_Z4=E(_Z3[1]),_Z5=B(_db(_YY[1],_YY[2],_YY[3],_YX[2],_Z4[1],_Z4[2],_Z4[3],_Z3[2]));return [0,E(_Z5[1]),_Z5[2]];})]);});},_YJ);});};return new F(function(){return _Tn(_YF[1],_YG[1],_YG[2],_YG[3],_YF[3],_YA,_YH,_YH);});};return new F(function(){return _Ye(_Yz,_YA,_YD,_YB,_YD);});},_Z6=function(_Z7,_Z8,_Z9,_Za,_Zb){return new F(function(){return _Yy(_Z7,_Z8,_Za,_Zb);});},_DM=function(_Zc,_Zd,_Ze,_Zf,_Zg){return new F(function(){return _e8(_Z6,_Zc,function(_Zh,_Zi,_Zj){return new F(function(){return _ws(_Zh,_Zi,_Zd,function(_Zk,_Zl,_Zm){return new F(function(){return A(_Zd,[_Zk,_Zl,new T(function(){return B(_e0(_Zj,_Zm));})]);});});});},_Ze,function(_Zn,_Zo,_Zp){return new F(function(){return _ws(_Zn,_Zo,_Zd,function(_Zq,_Zr,_Zs){return new F(function(){return A(_Zf,[_Zq,_Zr,new T(function(){return B(_e0(_Zp,_Zs));})]);});});});},_Zg);});},_Zt=function(_Zu,_Zv,_Zw){while(1){var _Zx=E(_Zv);if(!_Zx[0]){return E(_Zw)[0]==0?true:false;}else{var _Zy=E(_Zw);if(!_Zy[0]){return false;}else{if(!B(A(_9p,[_Zu,_Zx[1],_Zy[1]]))){return false;}else{_Zv=_Zx[2];_Zw=_Zy[2];continue;}}}}},_Zz=function(_ZA,_ZB,_ZC){var _ZD=E(_ZB),_ZE=E(_ZC);return !B(_Zt(_ZA,_ZD[1],_ZE[1]))?true:!B(A(_9p,[_ZA,_ZD[2],_ZE[2]]))?true:false;},_ZF=function(_ZG,_ZH,_ZI,_ZJ,_ZK){return !B(_Zt(_ZG,_ZH,_ZJ))?false:B(A(_9p,[_ZG,_ZI,_ZK]));},_ZL=function(_ZM,_ZN,_ZO){var _ZP=E(_ZN),_ZQ=E(_ZO);return new F(function(){return _ZF(_ZM,_ZP[1],_ZP[2],_ZQ[1],_ZQ[2]);});},_ZR=function(_ZS){return [0,function(_ZT,_ZU){return new F(function(){return _ZL(_ZS,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _Zz(_ZS,_ZT,_ZU);});}];},_ZV=function(_ZW,_ZX,_ZY){var _ZZ=E(_ZX),_100=E(_ZY);return !B(_Zt(_ZW,_ZZ[1],_100[1]))?true:!B(A(_9p,[_ZW,_ZZ[2],_100[2]]))?true:false;},_101=function(_102,_103,_104){var _105=E(_103),_106=E(_104);return new F(function(){return _ZF(_102,_105[1],_105[2],_106[1],_106[2]);});},_107=function(_108){return [0,function(_ZT,_ZU){return new F(function(){return _101(_108,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _ZV(_108,_ZT,_ZU);});}];},_109=function(_10a,_10b,_10c){var _10d=E(_10a);switch(_10d[0]){case 0:var _10e=E(_10b);return _10e[0]==0?!B(_3x(_10d[3],_10e[3]))?[0]:[1,_10c]:[0];case 1:var _10f=E(_10b);return _10f[0]==1?!B(_3x(_10d[3],_10f[3]))?[0]:[1,_10c]:[0];case 2:var _10g=E(_10b);return _10g[0]==2?!B(_3x(_10d[3],_10g[3]))?[0]:[1,_10c]:[0];case 3:var _10h=E(_10b);return _10h[0]==3?!B(_3x(_10d[3],_10h[3]))?[0]:[1,_10c]:[0];case 4:var _10i=E(_10b);return _10i[0]==4?!B(_3x(_10d[3],_10i[3]))?[0]:[1,_10c]:[0];case 5:var _10j=E(_10b);return _10j[0]==5?!B(_3x(_10d[3],_10j[3]))?[0]:[1,_10c]:[0];case 6:var _10k=E(_10b);return _10k[0]==6?!B(_3x(_10d[3],_10k[3]))?[0]:[1,_10c]:[0];case 7:var _10l=E(_10b);return _10l[0]==7?!B(_3x(_10d[3],_10l[3]))?[0]:[1,_10c]:[0];case 8:var _10m=E(_10b);return _10m[0]==8?!B(_3x(_10d[3],_10m[3]))?[0]:[1,_10c]:[0];default:var _10n=E(_10b);return _10n[0]==9?!B(_3x(_10d[3],_10n[3]))?[0]:[1,_10c]:[0];}},_10o=new T(function(){return B(_2L("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_10p=function(_10q,_10r){return [3,_,_10q,_10r];},_10s=function(_10t,_10u,_10v){while(1){var _10w=E(_10v);if(!_10w[0]){return [0];}else{var _10x=E(_10w[1]),_10y=B(A(_10t,[_10u,_10x[2],_10x[3]]));if(!_10y[0]){_10v=_10w[2];continue;}else{return E(_10y);}}}},_10z=function(_10A,_10B){while(1){var _10C=(function(_10D,_10E){var _10F=E(_10E);switch(_10F[0]){case 2:var _10G=B(_10s(_109,_10F[2],_10D));if(!_10G[0]){return E(_10F);}else{var _10H=_10D;_10B=_10G[1];_10A=_10H;return null;}break;case 4:var _10I=_10F[3],_10J=B(_10s(_109,_10F[2],_10D));if(!_10J[0]){return E(_10F);}else{var _10K=E(_10J[1]);switch(_10K[0]){case 3:return E(_10K[3])[0]==0?B(_10p(_10K[2],_10I)):E(_10F);case 4:if(!E(_10K[3])[0]){var _10H=_10D;_10B=[4,_,_10K[2],_10I];_10A=_10H;return null;}else{return E(_10F);}break;default:return E(_10F);}}break;case 6:var _10L=_10F[3],_10M=_10F[4],_10N=B(_10s(_109,_10F[2],_10D));if(!_10N[0]){return E(_10F);}else{var _10O=E(_10N[1]);switch(_10O[0]){case 5:if(!E(_10O[3])[0]){if(!E(_10O[4])[0]){var _10H=_10D;_10B=[5,_,_10O[2],_10L,_10M];_10A=_10H;return null;}else{return E(_10F);}}else{return E(_10F);}break;case 6:if(!E(_10O[3])[0]){if(!E(_10O[4])[0]){var _10H=_10D;_10B=[6,_,_10O[2],_10L,_10M];_10A=_10H;return null;}else{return E(_10F);}}else{return E(_10F);}break;default:return E(_10F);}}break;case 7:return [7,_,_10F[2],new T(function(){return B(_10z(_10D,_10F[3]));})];case 8:var _10P=_10F[2],_10Q=_10F[3],_10R=B(_10s(_109,_10P,_10D));if(!_10R[0]){return [8,_,_10P,new T(function(){return B(_10z(_10D,_10Q));})];}else{var _10S=E(_10R[1]);switch(_10S[0]){case 7:return E(_10S[3])[0]==0?[7,_,_10S[2],new T(function(){return B(_10z(_10D,_10Q));})]:[8,_,_10P,new T(function(){return B(_10z(_10D,_10Q));})];case 8:if(!E(_10S[3])[0]){var _10H=_10D;_10B=[8,_,_10S[2],_10Q];_10A=_10H;return null;}else{return [8,_,_10P,new T(function(){return B(_10z(_10D,_10Q));})];}break;default:return [8,_,_10P,new T(function(){return B(_10z(_10D,_10Q));})];}}break;case 9:return [9,_,_10F[2],new T(function(){return B(_10z(_10D,_10F[3]));}),new T(function(){return B(_10z(_10D,_10F[4]));})];case 10:var _10T=_10F[2],_10U=_10F[3],_10V=_10F[4],_10W=B(_10s(_109,_10T,_10D));if(!_10W[0]){return [10,_,_10T,new T(function(){return B(_10z(_10D,_10U));}),new T(function(){return B(_10z(_10D,_10V));})];}else{var _10X=E(_10W[1]);switch(_10X[0]){case 9:return E(_10X[3])[0]==0?E(_10X[4])[0]==0?[9,_,_10X[2],new T(function(){return B(_10z(_10D,B(_10z(_10D,_10U))));}),new T(function(){return B(_10z(_10D,B(_10z(_10D,_10V))));})]:[10,_,_10T,new T(function(){return B(_10z(_10D,_10U));}),new T(function(){return B(_10z(_10D,_10V));})]:[10,_,_10T,new T(function(){return B(_10z(_10D,_10U));}),new T(function(){return B(_10z(_10D,_10V));})];case 10:if(!E(_10X[3])[0]){if(!E(_10X[4])[0]){var _10H=_10D;_10B=[10,_,_10X[2],_10U,_10V];_10A=_10H;return null;}else{return [10,_,_10T,new T(function(){return B(_10z(_10D,_10U));}),new T(function(){return B(_10z(_10D,_10V));})];}}else{return [10,_,_10T,new T(function(){return B(_10z(_10D,_10U));}),new T(function(){return B(_10z(_10D,_10V));})];}break;default:return [10,_,_10T,new T(function(){return B(_10z(_10D,_10U));}),new T(function(){return B(_10z(_10D,_10V));})];}}break;case 11:return [11,_,_10F[2],function(_10Y){return new F(function(){return _10z(_10D,B(A(_10F[3],[_10Y])));});}];case 12:var _10Z=_10F[2],_110=_10F[3],_111=B(_10s(_109,_10Z,_10D));if(!_111[0]){return [12,_,_10Z,function(_112){return new F(function(){return _10z(_10D,B(A(_110,[_112])));});}];}else{var _113=E(_111[1]);switch(_113[0]){case 11:return [11,_,_113[2],function(_114){return new F(function(){return _10z(_10D,B(A(_110,[_114])));});}];case 12:var _10H=_10D;_10B=[12,_,_113[2],_110];_10A=_10H;return null;default:return [12,_,_10Z,function(_115){return new F(function(){return _10z(_10D,B(A(_110,[_115])));});}];}}break;default:return E(_10F);}})(_10A,_10B);if(_10C!=null){return _10C;}}},_116=function(_117,_118){var _119=E(_118);if(!_119[0]){var _11a=B(_10s(_109,_119[1],_117));if(!_11a[0]){return E(_119);}else{var _11b=E(_11a[1]);return _11b[0]==0?E(_10o):[1,new T(function(){return B(_3d(function(_11c){return new F(function(){return _10z(_117,_11c);});},_11b[1]));})];}}else{return [1,new T(function(){return B(_3d(function(_11d){return new F(function(){return _10z(_117,_11d);});},_119[1]));})];}},_11e=function(_11f,_11g,_11h,_11i,_11j,_11k,_11l,_11m,_11n){var _11o=E(_11n);return [0,new T(function(){return B(_3d(function(_11p){return new F(function(){return _116(_11m,_11p);});},_11o[1]));}),new T(function(){return B(_116(_11m,_11o[2]));})];},_11q=function(_11r,_11s,_11t,_11u,_11v,_11w,_11x,_11y,_11z){var _11A=E(_11z);return [0,new T(function(){return B(_3d(function(_11B){return new F(function(){return _11e(_11r,_11s,_11t,_11u,_11v,_11w,_11x,_11y,_11B);});},_11A[1]));}),new T(function(){return B(_11e(_11r,_11s,_11t,_11u,_11v,_11w,_11x,_11y,_11A[2]));})];},_11C=function(_11D){return E(E(_11D)[1]);},_11E=function(_11F,_11G){var _11H=E(_11G);return new F(function(){return A(_11C,[_11H[1],E(_11F)[2],_11H[2]]);});},_11I=function(_11J,_11K,_11L){var _11M=E(_11L);if(!_11M[0]){return [0];}else{var _11N=_11M[1],_11O=_11M[2];return !B(A(_11J,[_11K,_11N]))?[1,_11N,new T(function(){return B(_11I(_11J,_11K,_11O));})]:E(_11O);}},_11P=function(_11Q,_11R,_11S){while(1){var _11T=E(_11S);if(!_11T[0]){return false;}else{if(!B(A(_11Q,[_11R,_11T[1]]))){_11S=_11T[2];continue;}else{return true;}}}},_11U=function(_11V,_11W){var _11X=function(_11Y,_11Z){while(1){var _120=(function(_121,_122){var _123=E(_121);if(!_123[0]){return [0];}else{var _124=_123[1],_125=_123[2];if(!B(_11P(_11V,_124,_122))){return [1,_124,new T(function(){return B(_11X(_125,[1,_124,_122]));})];}else{_11Y=_125;var _126=_122;_11Z=_126;return null;}}})(_11Y,_11Z);if(_120!=null){return _120;}}};return new F(function(){return _11X(_11W,_9);});},_127=function(_128,_129,_12a){return new F(function(){return _e(_129,new T(function(){return B((function(_12b,_12c){while(1){var _12d=E(_12c);if(!_12d[0]){return E(_12b);}else{var _12e=B(_11I(_128,_12d[1],_12b));_12c=_12d[2];_12b=_12e;continue;}}})(B(_11U(_128,_12a)),_129));},1));});},_12f=function(_12g,_12h){while(1){var _12i=(function(_12j,_12k){var _12l=E(_12k);switch(_12l[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12j,_12l[2]],_9];case 3:var _12m=_12j;_12h=_12l[3];_12g=_12m;return null;case 4:return new F(function(){return _127(_11E,[1,[0,_12j,_12l[2]],_9],new T(function(){return B(_12f(_12j,_12l[3]));},1));});break;case 5:return new F(function(){return _127(_11E,B(_12f(_12j,_12l[3])),new T(function(){return B(_12f(_12j,_12l[4]));},1));});break;default:return new F(function(){return _127(_11E,B(_127(_11E,[1,[0,_12j,_12l[2]],_9],new T(function(){return B(_12f(_12j,_12l[3]));},1))),new T(function(){return B(_12f(_12j,_12l[4]));},1));});}})(_12g,_12h);if(_12i!=null){return _12i;}}},_12n=function(_12o,_12p,_12q,_12r){while(1){var _12s=(function(_12t,_12u,_12v,_12w){var _12x=E(_12w);switch(_12x[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12t,_12x[2]],_9];case 3:return new F(function(){return _12f(_12t,_12x[3]);});break;case 4:return new F(function(){return _127(_11E,[1,[0,_12t,_12x[2]],_9],new T(function(){return B(_12f(_12t,_12x[3]));},1));});break;case 5:return new F(function(){return _127(_11E,B(_12f(_12t,_12x[3])),new T(function(){return B(_12f(_12t,_12x[4]));},1));});break;case 6:return new F(function(){return _127(_11E,B(_127(_11E,[1,[0,_12t,_12x[2]],_9],new T(function(){return B(_12f(_12t,_12x[3]));},1))),new T(function(){return B(_12f(_12t,_12x[4]));},1));});break;case 7:var _12y=_12t,_12z=_12u,_12A=_12v;_12r=_12x[3];_12o=_12y;_12p=_12z;_12q=_12A;return null;case 8:return new F(function(){return _127(_11E,[1,[0,_12t,_12x[2]],_9],new T(function(){return B(_12n(_12t,_12u,_12v,_12x[3]));},1));});break;case 9:return new F(function(){return _127(_11E,B(_12n(_12t,_12u,_12v,_12x[3])),new T(function(){return B(_12n(_12t,_12u,_12v,_12x[4]));},1));});break;case 10:return new F(function(){return _127(_11E,B(_127(_11E,[1,[0,_12t,_12x[2]],_9],new T(function(){return B(_12n(_12t,_12u,_12v,_12x[3]));},1))),new T(function(){return B(_12n(_12t,_12u,_12v,_12x[4]));},1));});break;case 11:var _12y=_12t,_12z=_12u,_12A=_12v;_12r=B(A(_12x[3],[_2V]));_12o=_12y;_12p=_12z;_12q=_12A;return null;default:return new F(function(){return _127(_11E,[1,[0,_12t,_12x[2]],_9],new T(function(){return B(_12n(_12t,_12u,_12v,B(A(_12x[3],[_2V]))));},1));});}})(_12o,_12p,_12q,_12r);if(_12s!=null){return _12s;}}},_12B=function(_12C,_12D,_12E,_12F,_12G){var _12H=function(_12I){return new F(function(){return _12n(_12C,_12D,_12E,_12I);});};return new F(function(){return _e(B(_8Q(B(_3d(function(_12J){var _12K=E(_12J);if(!_12K[0]){return [1,[0,_12C,_12K[1]],_9];}else{return new F(function(){return _8Q(B(_3d(_12H,_12K[1])));});}},_12F)))),new T(function(){var _12L=E(_12G);if(!_12L[0]){var _12M=[1,[0,_12C,_12L[1]],_9];}else{var _12M=B(_8Q(B(_3d(_12H,_12L[1]))));}return _12M;},1));});},_12N=function(_12O,_12P,_12Q,_12R,_12S,_12T,_12U,_12V,_12W){var _12X=E(_12W);return new F(function(){return _e(B(_8Q(B(_3d(function(_12Y){var _12Z=E(_12Y);return new F(function(){return _12B(_12O,_12S,_12T,_12Z[1],_12Z[2]);});},_12X[1])))),new T(function(){var _130=E(_12X[2]);return B(_12B(_12O,_12S,_12T,_130[1],_130[2]));},1));});},_131=function(_132,_133,_134,_135,_136,_137,_138,_139,_13a,_13b,_13c){return [0,_132,_133,_134,_135,function(_11B){return new F(function(){return _12N(_132,_136,_137,_138,_139,_13a,_13b,_13c,_11B);});},function(_13d,_11B){return new F(function(){return _11q(_136,_137,_138,_139,_13a,_13b,_13c,_13d,_11B);});}];},_13e=function(_13f){return E(E(_13f)[2]);},_13g=function(_13h){return E(E(_13h)[1]);},_13i=[0,_13g,_13e],_13j=[0,125],_13k=new T(function(){return B(unCStr("given = "));}),_13l=new T(function(){return B(unCStr(", "));}),_13m=new T(function(){return B(unCStr("needed = "));}),_13n=new T(function(){return B(unCStr("AbsRule {"));}),_13o=[0,0],_13p=function(_13q){return E(E(_13q)[3]);},_13r=function(_13s){return E(E(_13s)[1]);},_13t=function(_13u,_13v,_13w,_13x){var _13y=function(_13z){return new F(function(){return _e(_13n,new T(function(){return B(_e(_13m,new T(function(){return B(A(new T(function(){return B(A(_13p,[_13u,_13w]));}),[new T(function(){return B(_e(_13l,new T(function(){return B(_e(_13k,new T(function(){return B(A(new T(function(){return B(A(_13r,[_13u,_13o,_13x]));}),[[1,_13j,_13z]]));},1)));},1)));})]));},1)));},1));});};return _13v<11?E(_13y):function(_13A){return [1,_E,new T(function(){return B(_13y([1,_D,_13A]));})];};},_13B=function(_13C,_13D){var _13E=E(_13D);return new F(function(){return A(_13t,[_13C,0,_13E[1],_13E[2],_9]);});},_13F=function(_13G,_13H,_13I){return new F(function(){return _23(function(_13J){var _13K=E(_13J);return new F(function(){return _13t(_13G,0,_13K[1],_13K[2]);});},_13H,_13I);});},_13L=function(_13M,_13N,_13O){var _13P=E(_13O);return new F(function(){return _13t(_13M,E(_13N)[1],_13P[1],_13P[2]);});},_13Q=function(_13R){return [0,function(_ZT,_ZU){return new F(function(){return _13L(_13R,_ZT,_ZU);});},function(_ZU){return new F(function(){return _13B(_13R,_ZU);});},function(_ZT,_ZU){return new F(function(){return _13F(_13R,_ZT,_ZU);});}];},_13S=new T(function(){return B(unCStr("Sequent "));}),_13T=[0,11],_13U=[0,32],_13V=function(_13W,_13X,_13Y,_13Z){var _140=new T(function(){return B(A(_13r,[_13W,_13T,_13Z]));}),_141=new T(function(){return B(A(_13p,[_13W,_13Y]));});return _13X<11?function(_142){return new F(function(){return _e(_13S,new T(function(){return B(A(_141,[[1,_13U,new T(function(){return B(A(_140,[_142]));})]]));},1));});}:function(_143){return [1,_E,new T(function(){return B(_e(_13S,new T(function(){return B(A(_141,[[1,_13U,new T(function(){return B(A(_140,[[1,_D,_143]]));})]]));},1)));})];};},_144=function(_145,_146){var _147=E(_146);return new F(function(){return A(_13V,[_145,0,_147[1],_147[2],_9]);});},_148=function(_149,_14a,_14b){return new F(function(){return _23(function(_14c){var _14d=E(_14c);return new F(function(){return _13V(_149,0,_14d[1],_14d[2]);});},_14a,_14b);});},_14e=function(_14f,_14g,_14h){var _14i=E(_14h);return new F(function(){return _13V(_14f,E(_14g)[1],_14i[1],_14i[2]);});},_14j=function(_14k){return [0,function(_ZT,_ZU){return new F(function(){return _14e(_14k,_ZT,_ZU);});},function(_ZU){return new F(function(){return _144(_14k,_ZU);});},function(_ZT,_ZU){return new F(function(){return _148(_14k,_ZT,_ZU);});}];},_14l=function(_14m,_14n){return new F(function(){return _e(B(_1r(_14m)),_14n);});},_14o=function(_14p,_14q){return new F(function(){return _23(_14l,_14p,_14q);});},_14r=function(_14s,_14t,_14u){return new F(function(){return _e(B(_1r(_14t)),_14u);});},_14v=[0,_14r,_1r,_14o],_14w=function(_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H,_14I){var _14J=E(_14I);return new F(function(){return _12B(_14x,_14E,_14F,_14J[1],_14J[2]);});},_14K=function(_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_14V){return [0,_14L,_14M,_14N,_14O,function(_11B){return new F(function(){return _14w(_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_11B);});},function(_13d,_11B){return new F(function(){return _11e(_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_13d,_11B);});}];},_14W=function(_14X,_14Y){return [0];},_14Z=function(_150,_151,_152,_153,_154,_155,_156,_157,_158,_159,_15a,_15b,_15c,_15d){return [0,_150,_151,_14W,_1];},_15e=function(_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_15q){var _15r=E(_15q);if(!_15r[0]){return [1,[0,_15f,_15r[1]],_9];}else{return new F(function(){return _8Q(B(_3d(function(_15s){return new F(function(){return _12n(_15f,_15m,_15n,_15s);});},_15r[1])));});}},_15t=function(_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E){return [0,_15u,_15v,_15w,_15x,function(_11B){return new F(function(){return _15e(_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_11B);});},_116];},_15F=new T(function(){return B(_Ci("w_sAXG{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r156}\n                  sv{tv aABJ} [tv] quant{tv aABH} [tv]"));}),_15G=new T(function(){return B(_Ci("w_sAXF{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv aABH} [tv]"));}),_15H=new T(function(){return B(_Ci("w_sAXE{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv aABG} [tv]"));}),_15I=new T(function(){return B(_Ci("w_sAXD{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv aABJ} [tv]"));}),_15J=new T(function(){return B(_Ci("w_sAXC{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv aABF} [tv]"));}),_15K=new T(function(){return B(_Ci("w_sAXB{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv aABI} [tv]"));}),_15L=new T(function(){return B(_Ci("w_sAXH{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14g}\n                  sv{tv aABJ} [tv]"));}),_15M=new T(function(){return B(_Ci("w_sAXA{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aABH} [tv]"));}),_15N=new T(function(){return B(_Ci("w_sAXz{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv aABG} [tv]"));}),_15O=new T(function(){return B(_Ci("w_sAXy{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv aABJ} [tv]"));}),_15P=new T(function(){return B(_Ci("w_sAXx{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv aABF} [tv]"));}),_15Q=new T(function(){return B(_Ci("w_sAXw{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aABI} [tv]"));}),_15R=function(_15S,_15T){return function(_15U,_15V){var _15W=E(_15U);return _15W[0]==0?[1,[0,new T(function(){return B(_15X(_15S,_15T,_15Q,_15P,_15O,_15N,_15M,_15K,_15J,_15I,_15H,_15G,_15F,_15L));}),_15W[1],_15V]]:[0];};},_15Y=function(_15Z){return [0,E(_15Z)];},_15X=function(_160,_161,_162,_163,_164,_165,_166,_167,_168,_169,_16a,_16b,_16c,_16d){return [0,_160,_161,new T(function(){return B(_15R(_160,_161));}),_15Y];},_16e=[1,_9],_16f=function(_16g,_16h){while(1){var _16i=E(_16g);if(!_16i[0]){return E(_16h);}else{_16g=_16i[2];var _16j=_16h+1|0;_16h=_16j;continue;}}},_16k=[0,95],_16l=[1,_16k,_9],_16m=[1,_16l,_9],_16n=function(_16o,_16p,_16q){return !B(_3x(B(A(_16o,[_16p,_16m])),B(A(_16o,[_16q,_16m]))))?true:false;},_16r=function(_16s){return [0,function(_16t,_16u){return new F(function(){return _3x(B(A(_16s,[_16t,_16m])),B(A(_16s,[_16u,_16m])));});},function(_44,_45){return new F(function(){return _16n(_16s,_44,_45);});}];},_16v=function(_16w,_16x){return new F(function(){return _10z(_16w,_16x);});},_16y=function(_16z,_16A,_16B,_16C,_16D,_16E,_16F,_16G,_16H,_16I,_16J){return [0,_16z,_16A,_16B,_16C,function(_16K){return new F(function(){return _12n(_16z,_16G,_16H,_16K);});},_16v];},_16L=new T(function(){return B(_Ci("w_spLN{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r156}\n                  sv{tv amIY} [tv] quant{tv amIW} [tv]"));}),_16M=new T(function(){return B(_Ci("w_spLM{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv amIW} [tv]"));}),_16N=new T(function(){return B(_Ci("w_spLL{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv amIV} [tv]"));}),_16O=new T(function(){return B(_Ci("w_spLK{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv amIY} [tv]"));}),_16P=new T(function(){return B(_Ci("w_spLJ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv amIU} [tv]"));}),_16Q=new T(function(){return B(_Ci("w_spLI{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv amIX} [tv]"));}),_16R=new T(function(){return B(_Ci("w_spLO{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14g}\n                  sv{tv amIY} [tv]"));}),_16S=new T(function(){return B(_Ci("w_spLH{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv amIW} [tv]"));}),_16T=new T(function(){return B(_Ci("w_spLG{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv amIV} [tv]"));}),_16U=new T(function(){return B(_Ci("w_spLF{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv amIY} [tv]"));}),_16V=new T(function(){return B(_Ci("w_spLE{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv amIU} [tv]"));}),_16W=new T(function(){return B(_Ci("w_spLD{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv amIX} [tv]"));}),_16X=function(_16Y,_16Z,_170,_171){var _172=E(_170);switch(_172[0]){case 2:return [1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_172[2],_171]];case 4:var _174=_172[2];if(!E(_172[3])[0]){var _175=E(_171);switch(_175[0]){case 3:return E(_175[3])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_174,_175]]:[0];case 4:return E(_175[3])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_174,_175]]:[0];default:return [0];}}else{return [0];}break;case 6:var _176=_172[2];if(!E(_172[3])[0]){if(!E(_172[4])[0]){var _177=E(_171);switch(_177[0]){case 5:return E(_177[3])[0]==0?E(_177[4])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_176,_177]]:[0]:[0];case 6:return E(_177[3])[0]==0?E(_177[4])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_176,_177]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _178=_172[2];if(!E(_172[3])[0]){var _179=E(_171);switch(_179[0]){case 7:return E(_179[3])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_178,_179]]:[0];case 8:return E(_179[3])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_178,_179]]:[0];default:return [0];}}else{return [0];}break;case 10:var _17a=_172[2];if(!E(_172[3])[0]){if(!E(_172[4])[0]){var _17b=E(_171);switch(_17b[0]){case 9:return E(_17b[3])[0]==0?E(_17b[4])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_17a,_17b]]:[0]:[0];case 10:return E(_17b[3])[0]==0?E(_17b[4])[0]==0?[1,[0,new T(function(){return B(_173(_16Y,_16Z,_16W,_16V,_16U,_16T,_16S,_16Q,_16P,_16O,_16N,_16M,_16L,_16R));}),_17a,_17b]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_17c=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_17d=function(_17e){var _17f=E(_17e);switch(_17f[0]){case 3:return [2,_,_17f];case 4:return [4,_,_17f,_V];case 5:return [6,_,_17f,_V,_V];case 6:return [8,_,_17f,_S];case 7:return [10,_,_17f,_S,_S];default:return E(_17c);}},_173=function(_17g,_17h,_17i,_17j,_17k,_17l,_17m,_17n,_17o,_17p,_17q,_17r,_17s,_17t){return [0,_17g,_17h,function(_17u,_17v){return new F(function(){return _16X(_17g,_17h,_17u,_17v);});},_17d];},_17w=function(_17x,_17y,_17z){return new F(function(){return _23(function(_17A,_17B){return new F(function(){return _e(B(A(_17x,[_17A,_16m])),_17B);});},_17y,_17z);});},_17C=function(_17D){return [0,function(_17E,_17F,_17G){return new F(function(){return _e(B(A(_17D,[_17F,_16m])),_17G);});},function(_17H){return new F(function(){return A(_17D,[_17H,_16m]);});},function(_44,_45){return new F(function(){return _17w(_17D,_44,_45);});}];},_17I=[1,_9],_17J=function(_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V){var _17W=E(_17U);if(_17W[0]==2){return E(_17I);}else{var _17X=E(_17V);if(_17X[0]==2){return E(_17I);}else{var _17Y=function(_17Z){var _180=function(_181){var _182=function(_183){var _184=function(_185){var _186=function(_187){var _188=function(_189){var _18a=function(_18b){var _18c=function(_18d){var _18e=function(_18f){var _18g=function(_18h){var _18i=function(_18j){var _18k=function(_18l){var _18m=E(_17W);switch(_18m[0]){case 1:var _18n=E(_17X);return _18n[0]==1?!B(A(_17L,[_18m[2],_18n[2]]))?[0]:E(_17I):[0];case 3:var _18o=E(_17X);return _18o[0]==3?!B(A(_17K,[_18m[2],_18o[2]]))?[0]:E(_17I):[0];case 4:var _18p=_18m[2],_18q=E(_17X);switch(_18q[0]){case 3:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[4,_,_18p,_V],[3,_,_18q[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[4,_,_18p,_V],[4,_,_18q[2],_V]]));}),_9]];default:return [0];}break;case 5:var _18s=E(_17X);return _18s[0]==5?!B(A(_17K,[_18m[2],_18s[2]]))?[0]:E(_17I):[0];case 6:var _18t=_18m[2],_18u=E(_17X);switch(_18u[0]){case 5:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[6,_,_18t,_V,_V],[5,_,_18u[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[6,_,_18t,_V,_V],[6,_,_18u[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _18v=E(_17X);return _18v[0]==7?!B(A(_17M,[_18m[2],_18v[2]]))?[0]:[1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18m[3],_18v[3]]));}),_9]]:[0];case 8:var _18w=_18m[2],_18x=_18m[3],_18y=E(_17X);switch(_18y[0]){case 7:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[8,_,_18w,_S],[7,_,_18y[2],_S]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18x,_18y[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[8,_,_18w,_S],[8,_,_18y[2],_S]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18x,_18y[3]]));}),_9]]];default:return [0];}break;case 9:var _18z=E(_17X);return _18z[0]==9?!B(A(_17M,[_18m[2],_18z[2]]))?[0]:[1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18m[3],_18z[3]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18m[4],_18z[4]]));}),_9]]]:[0];case 10:var _18A=_18m[2],_18B=_18m[3],_18C=_18m[4],_18D=function(_18E){var _18F=E(_17X);switch(_18F[0]){case 9:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[10,_,_18A,_S,_S],[9,_,_18F[2],_S,_S]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18B,_18F[3]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18C,_18F[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,[10,_,_18A,_S,_S],[10,_,_18F[2],_S,_S]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18B,_18F[3]]));}),[1,new T(function(){return B(A(_18r,[_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_18C,_18F[4]]));}),_9]]]];default:return [0];}};return E(_18B)[0]==0?E(_18C)[0]==0?E(_17I):B(_18D(_)):B(_18D(_));default:return [0];}},_18G=E(_17X);return _18G[0]==10?E(_18G[3])[0]==0?E(_18G[4])[0]==0?E(_17I):B(_18k(_)):B(_18k(_)):B(_18k(_));},_18H=E(_17W);return _18H[0]==8?E(_18H[3])[0]==0?E(_17I):B(_18i(_)):B(_18i(_));},_18I=E(_17X);switch(_18I[0]){case 6:return E(_18I[3])[0]==0?E(_18I[4])[0]==0?E(_17I):B(_18g(_)):B(_18g(_));case 8:return E(_18I[3])[0]==0?E(_17I):B(_18g(_));default:return new F(function(){return _18g(_);});}},_18J=E(_17W);return _18J[0]==6?E(_18J[3])[0]==0?E(_18J[4])[0]==0?E(_17I):B(_18e(_)):B(_18e(_)):B(_18e(_));},_18K=E(_17X);return _18K[0]==4?E(_18K[3])[0]==0?E(_17I):B(_18c(_)):B(_18c(_));},_18L=E(_17W);switch(_18L[0]){case 4:return E(_18L[3])[0]==0?E(_17I):B(_18a(_));case 9:return E(_18L[3])[0]==0?E(_18L[4])[0]==0?E(_17I):B(_18a(_)):B(_18a(_));default:return new F(function(){return _18a(_);});}},_18M=E(_17X);return _18M[0]==9?E(_18M[3])[0]==0?E(_18M[4])[0]==0?E(_17I):B(_188(_)):B(_188(_)):B(_188(_));},_18N=E(_17W);return _18N[0]==7?E(_18N[3])[0]==0?E(_17I):B(_186(_)):B(_186(_));},_18O=E(_17X);switch(_18O[0]){case 5:return E(_18O[3])[0]==0?E(_18O[4])[0]==0?E(_17I):B(_184(_)):B(_184(_));case 7:return E(_18O[3])[0]==0?E(_17I):B(_184(_));default:return new F(function(){return _184(_);});}},_18P=E(_17W);return _18P[0]==5?E(_18P[3])[0]==0?E(_18P[4])[0]==0?E(_17I):B(_182(_)):B(_182(_)):B(_182(_));},_18Q=E(_17X);return _18Q[0]==3?E(_18Q[3])[0]==0?E(_17I):B(_180(_)):B(_180(_));},_18R=E(_17W);return _18R[0]==3?E(_18R[3])[0]==0?E(_17I):B(_17Y(_)):B(_17Y(_));}}},_18S=function(_18T,_18U,_18V){return [0,_18T,_18U,_18V];},_18W=new T(function(){return B(_Ci("w_spLW{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv amIj} [tv]"));}),_18X=new T(function(){return B(_Ci("w_spLS{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv amIk} [tv]"));}),_18Y=function(_18Z){return [0,function(_190,_191){return B(A(_18Z,[_190,_191,_1]))[0]==0?false:true;},function(_192,_193){return B(A(_18Z,[_192,_193,_1]))[0]==0?true:false;}];},_194=new T(function(){return B(_18Y(_109));}),_18r=function(_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d,_19e){var _19f=function(_19g,_19h){return new F(function(){return _2W(_199,_19b,_19c,_19a,_198,_19d,_19e,_19g);});};return function(_ma,_19i){return new F(function(){return _18S(new T(function(){return B(_173(function(_19j,_19k){return new F(function(){return _17J(_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d,_19e,_19j,_19k);});},new T(function(){return B(_16y(_194,_14v,new T(function(){return B(_16r(_19f));}),new T(function(){return B(_17C(_19f));}),_199,_19b,_19c,_198,_19a,_19d,_19e));}),_18X,_195,_196,_197,_18W,_198,_199,_19a,_19b,_19c,_19d,_19e));}),_ma,_19i);});};},_19l=function(_19m,_19n,_19o){var _19p=E(_19n);if(!_19p[0]){return [0];}else{var _19q=E(_19o);return _19q[0]==0?[0]:[1,new T(function(){return B(A(_19m,[_19p[1],_19q[1]]));}),new T(function(){return B(_19l(_19m,_19p[2],_19q[2]));})];}},_19r=function(_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_19C,_19D){var _19E=E(_19C);if(!_19E[0]){return E(_16e);}else{var _19F=_19E[1],_19G=E(_19D);if(!_19G[0]){return E(_16e);}else{var _19H=_19G[1];return B(_16f(_19F,0))!=B(_16f(_19H,0))?[0]:[1,new T(function(){return B(_19l(new T(function(){return B(_18r(_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B));}),_19F,_19H));})];}}},_19I=new T(function(){return B(_Ci("w_sAYr{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aABp} [tv]"));}),_19J=new T(function(){return B(_Ci("w_sAYv{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aABo} [tv]"));}),_19K=new T(function(){return B(_18Y(_109));}),_19L=function(_19M,_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U,_19V){var _19W=new T(function(){return B(_15X(function(_19X,_19Y){return new F(function(){return _19r(_19M,_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U,_19V,_19X,_19Y);});},new T(function(){return B(_15t(_19K,_14v,new T(function(){return B(_3W(_19Q,_19S,_19T,_19P,_19R,_19U,_19V));}),new T(function(){return B(_bI(_19Q,_19S,_19T,_19P,_19R,_19U,_19V));}),_19Q,_19S,_19T,_19P,_19R,_19U,_19V));}),_19I,_19M,_19N,_19O,_19J,_19P,_19Q,_19R,_19S,_19T,_19U,_19V));});return function(_19Z,_1a0){var _1a1=E(_19Z),_1a2=_1a1[1],_1a3=E(_1a0),_1a4=_1a3[1];return B(_16f(_1a2,0))!=B(_16f(_1a4,0))?[0]:[1,[1,[0,_19W,_1a1[2],_1a3[2]],new T(function(){return B(_19l(function(_13d,_11B){return [0,_19W,_13d,_11B];},_1a2,_1a4));})]];};},_1a5=new T(function(){return B(_Ci("w_sB13{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aAAW} [tv]"));}),_1a6=new T(function(){return B(_Ci("w_sB17{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aAAV} [tv]"));}),_1a7=function(_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag,_1ah){var _1ai=new T(function(){return B(_14Z(new T(function(){return B(_19L(_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag,_1ah));}),new T(function(){return B(_14K(_19K,_14v,new T(function(){return B(_107(new T(function(){return B(_3W(_1ac,_1ae,_1af,_1ab,_1ad,_1ag,_1ah));})));}),new T(function(){return B(_14j(new T(function(){return B(_bI(_1ac,_1ae,_1af,_1ab,_1ad,_1ag,_1ah));})));}),_1ac,_1ae,_1af,_1ab,_1ad,_1ag,_1ah));}),_1a5,_1a8,_1a9,_1aa,_1a6,_1ab,_1ac,_1ad,_1ae,_1af,_1ag,_1ah));});return function(_1aj,_1ak){var _1al=E(_1aj),_1am=_1al[1],_1an=E(_1ak),_1ao=_1an[1];return B(_16f(_1am,0))!=B(_16f(_1ao,0))?[0]:[1,[1,[0,_1ai,_1al[2],_1an[2]],new T(function(){return B(_19l(function(_13d,_11B){return [0,_1ai,_13d,_11B];},_1am,_1ao));})]];};},_1ap=function(_1aq,_1ar){while(1){var _1as=E(_1ar);if(!_1as[0]){return false;}else{var _1at=E(_1as[1]);if(!B(A(_11C,[_1at[1],_1aq,_1at[2]]))){_1ar=_1as[2];continue;}else{return true;}}}},_1au=[0,_9],_1av=function(_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC,_1aD,_1aE,_1aF,_1aG){var _1aH=E(_1az);return !B(A(_1aH[1],[new T(function(){return B(A(_1aE,[_1aF]));}),_1aG]))?!B(_1ap(_1aF,B(A(_1aB,[_1aG]))))?[0,[1,[0,[0,_1aw,[0,_1ax,_1ay,_1aH,_1aA,_1aB,_1aC],_1aD,_1aE],_1aF,_1aG],_9]]:[1,[1,_,[0,_1aw,[0,_1ax,_1ay,_1aH,_1aA,_1aB,_1aC],_1aD,_1aE],[3,_1ay,_1aA,_1aF,_1aG]]]:E(_1au);},_1aI=function(_1aJ){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(54,15)-(56,42)|case");});},_1aK=new T(function(){return B(_1aI(_));}),_1aL=new T(function(){return B(unCStr(": empty list"));}),_1aM=new T(function(){return B(unCStr("Prelude."));}),_1aN=function(_1aO){return new F(function(){return err(B(_e(_1aM,new T(function(){return B(_e(_1aO,_1aL));},1))));});},_1aP=new T(function(){return B(unCStr("head"));}),_1aQ=new T(function(){return B(_1aN(_1aP));}),_1aR=function(_1aS){return E(E(_1aS)[2]);},_1aT=function(_1aU,_1aV){while(1){var _1aW=E(_1aU);if(!_1aW){return E(_1aV);}else{var _1aX=E(_1aV);if(!_1aX[0]){return [0];}else{_1aU=_1aW-1|0;_1aV=_1aX[2];continue;}}}},_1aY=function(_1aZ,_1b0){var _1b1=E(_1aZ)[1];return _1b1>=0?B(_1aT(_1b1,_1b0)):E(_1b0);},_1b2=function(_1b3){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:96:31-64|function conc");});},_1b4=new T(function(){return B(_1b2(_));}),_1b5=function(_1b6){var _1b7=E(_1b6);switch(_1b7[0]){case 3:return [2,_,_1b7];case 4:return [4,_,_1b7,_V];case 5:return [6,_,_1b7,_V,_V];case 6:return [8,_,_1b7,_S];case 7:return [10,_,_1b7,_S,_S];default:return E(_17c);}},_1b8=function(_1b9){var _1ba=E(_1b9);if(!_1ba[0]){return [0];}else{var _1bb=E(_1ba[1]);if(!_1bb[0]){return [0];}else{return new F(function(){return _e(_1bb[1],new T(function(){return B(_1b8(_1ba[2]));},1));});}}},_1bc=function(_1bd){var _1be=E(_1bd);return [0,[1,[1,new T(function(){return B(_1b8(_1be[1]));})],_9],_1be[2]];},_1bf=function(_1bg,_1bh,_1bi){return !B(_9r(_1bg,_1bh,_1bi))?E(_1bi):[1,_1bh,new T(function(){return B(_8T(function(_1bj){return !B(A(_9p,[_1bg,_1bj,_1bh]))?true:false;},_1bi));})];},_1bk=function(_1bl,_1bm,_1bn,_1bo,_1bp,_1bq,_1br){return function(_1bs,_1bt){var _1bu=E(_1bs);if(!_1bu[0]){return new F(function(){return _1bc(_1bt);});}else{var _1bv=E(_1bt);return [0,[1,[1,new T(function(){return B(_1bf(new T(function(){return B(_16r(function(_1bw,_1bx){return new F(function(){return _2W(_1br,_1bq,_1bp,_1bn,_1bo,_1bl,_1bm,_1bw);});}));}),_1bu[1],B(_1b8(_1bv[1]))));})],_9],_1bv[2]];}};},_1by=new T(function(){return B(_18Y(_109));}),_1bz=function(_1bA){return E(E(_1bA)[1]);},_1bB=function(_1bC,_1bD){var _1bE=E(_1bC);if(!_1bE){return [0];}else{var _1bF=E(_1bD);return _1bF[0]==0?[0]:[1,_1bF[1],new T(function(){return B(_1bB(_1bE-1|0,_1bF[2]));})];}},_1bG=function(_1bH,_1bI){return _1bH<0?[0]:B(_1bB(_1bH,_1bI));},_1bJ=function(_1bK,_1bL){var _1bM=E(_1bK)[1];return _1bM>0?B(_1bG(_1bM,_1bL)):[0];},_1bN=function(_1bO,_1bP){return [1,_,_1bO,_1bP];},_1bQ=function(_1bR){return E(E(_1bR)[2]);},_1bS=function(_1bT){return E(E(_1bT)[4]);},_1bU=function(_1bV,_1bW,_1bX){var _1bY=E(_1bV),_1bZ=E(_1bY[2]);return new F(function(){return _1av(_1bY[1],_1bZ[1],_1bZ[2],_1bZ[3],_1bZ[4],_1bZ[5],_1bZ[6],_1bY[3],_1bY[4],_1bW,_1bX);});},_1c0=function(_1c1,_1c2,_1c3,_1c4,_1c5,_1c6){var _1c7=B(A(_1c3,[_1c5,_1c6]));if(!_1c7[0]){var _1c8=B(A(_1c3,[_1c6,_1c5]));if(!_1c8[0]){var _1c9=B(A(_1c1,[_1c5,_1c6]));if(!_1c9[0]){return [1,[0,new T(function(){return B(_1bS(_1c2));}),_1c5,_1c6]];}else{var _1ca=B(_1cb([0,_1c1,_1c2,_1c3,_1c4],_1c9[1]));return _1ca[0]==0?E(_1ca):[1,[2,new T(function(){return B(_1bS(_1c2));}),_1ca[1],_1c5,_1c6]];}}else{var _1cc=E(_1c8[1]);return new F(function(){return _1bU(_1cc[1],_1cc[2],_1cc[3]);});}}else{var _1cd=E(_1c7[1]);return new F(function(){return _1bU(_1cd[1],_1cd[2],_1cd[3]);});}},_1ce=function(_1cf){return E(E(_1cf)[6]);},_1cb=function(_1cg,_1ch){var _1ci=E(_1ch);if(!_1ci[0]){return E(_1au);}else{var _1cj=E(_1ci[1]),_1ck=E(_1cj[1]),_1cl=B(_1c0(_1ck[1],_1ck[2],_1ck[3],_1ck[4],_1cj[2],_1cj[3]));if(!_1cl[0]){var _1cm=_1cl[1],_1cn=B(_1cb(_1cg,B(_3d(function(_1co){var _1cp=E(_1co),_1cq=_1cp[1];return [0,_1cq,new T(function(){return B(A(_1ce,[B(_1bQ(_1cq)),_1cm,_1cp[2]]));}),new T(function(){return B(A(_1ce,[B(_1bQ(_1cq)),_1cm,_1cp[3]]));})];},_1ci[2]))));if(!_1cn[0]){var _1cr=_1cn[1];return [0,new T(function(){var _1cs=function(_1ct){var _1cu=E(_1ct);return _1cu[0]==0?E(_1cr):[1,new T(function(){var _1cv=E(_1cu[1]),_1cw=_1cv[1];return [0,_1cw,_1cv[2],new T(function(){return B(A(_1ce,[B(_1bQ(_1cw)),_1cr,_1cv[3]]));})];}),new T(function(){return B(_1cs(_1cu[2]));})];};return B(_1cs(_1cm));})];}else{return [1,new T(function(){return B(_1bN(_1cg,_1cn[1]));})];}}else{return [1,[1,_,_1ck,_1cl[1]]];}}},_1cx=function(_1cy,_1cz,_1cA,_1cB,_1cC,_1cD,_1cE,_1cF,_1cG,_1cH,_1cI,_1cJ){var _1cK=new T(function(){return B(_1aR(_1cJ));}),_1cL=function(_1cM,_1cN){return new F(function(){return _2W(_1cE,_1cD,_1cC,_1cA,_1cB,_1cy,_1cz,_1cM);});},_1cO=new T(function(){return B(_16y(_1by,_14v,new T(function(){return B(_16r(_1cL));}),new T(function(){return B(_17C(_1cL));}),_1cE,_1cD,_1cC,_1cB,_1cA,_1cy,_1cz));}),_1cP=function(_1cQ,_1cR){return new F(function(){return _17J(_1cI,_1cG,_1cH,_1cB,_1cE,_1cA,_1cD,_1cC,_1cy,_1cz,_1cQ,_1cR);});};return function(_1cS,_1cT,_1cU){var _1cV=new T(function(){return B(A(_1cF,[_1cU]));});return [0,new T(function(){return B(_19l(function(_1cW,_1cX){var _1cY=B(A(new T(function(){return B(_1bk(_1cy,_1cz,_1cA,_1cB,_1cC,_1cD,_1cE));}),[new T(function(){var _1cZ=E(E(_1cX)[1]);if(!_1cZ[0]){var _1d0=[0];}else{var _1d1=E(_1cZ[1]),_1d0=_1d1[0]==0?[0]:[1,new T(function(){var _1d2=E(_1d1[1]);return _1d2[0]==0?E(_1aQ):B(_10z(new T(function(){var _1d3=E(B(A(_1cK,[_1cS]))[2]);if(!_1d3[0]){var _1d4=E(_1b4);}else{var _1d5=E(_1d3[1]);if(!_1d5[0]){var _1d6=E(_1b4);}else{var _1d7=_1d5[1];if(!E(_1d5[2])[0]){var _1d8=B(_16X(_1cP,_1cO,_1d7,_1cV));if(!_1d8[0]){var _1d9=B(_16X(_1cP,_1cO,_1cV,_1d7));if(!_1d9[0]){var _1da=B(_1cP(_1d7,_1cV));if(!_1da[0]){var _1db=[0];}else{var _1dc=B(_1cb([0,_1cP,_1cO,function(_1dd,_1de){return new F(function(){return _16X(_1cP,_1cO,_1dd,_1de);});},_1b5],_1da[1])),_1db=_1dc[0]==0?E(_1dc[1]):[0];}var _1df=_1db;}else{var _1dg=E(_1d9[1]),_1dh=E(_1dg[1]),_1di=E(_1dh[2]),_1dj=B(_1av(_1dh[1],_1di[1],_1di[2],_1di[3],_1di[4],_1di[5],_1di[6],_1dh[3],_1dh[4],_1dg[2],_1dg[3])),_1df=_1dj[0]==0?E(_1dj[1]):[0];}var _1dk=_1df;}else{var _1dl=E(_1d8[1]),_1dm=E(_1dl[1]),_1dn=E(_1dm[2]),_1do=B(_1av(_1dm[1],_1dn[1],_1dn[2],_1dn[3],_1dn[4],_1dn[5],_1dn[6],_1dm[3],_1dm[4],_1dl[2],_1dl[3])),_1dk=_1do[0]==0?E(_1do[1]):[0];}var _1dp=_1dk;}else{var _1dp=E(_1b4);}var _1d6=_1dp;}var _1d4=_1d6;}var _1dq=_1d4;return _1dq;}),_1d2[1]));})];}var _1dr=_1d0;return _1dr;}),_1cW])),_1ds=_1cY[2],_1dt=E(E(_1cX)[1]);if(!_1dt[0]){return E(_1aK);}else{var _1du=E(_1dt[1]);if(!_1du[0]){return E(_1dt[2])[0]==0?E(_1cY):E(_1aK);}else{var _1dv=E(_1cY[1]);if(!_1dv[0]){return [0,_9,_1ds];}else{var _1dw=E(_1dv[1]);if(!_1dw[0]){return E(_1cY);}else{var _1dx=_1dw[1],_1dy=new T(function(){return [0,B(_16f(_1du[1],0))];});return [0,[1,[1,new T(function(){return B(_1bJ(_1dy,_1dx));})],[1,[1,new T(function(){return B(_1aY(_1dy,_1dx));})],_1dv[2]]],_1ds];}}}}},_1cT,new T(function(){return B(A(new T(function(){return B(_1bz(_1cJ));}),[_1cS]));},1)));}),[0,new T(function(){return E(B(A(_1cK,[_1cS]))[1]);}),[1,[1,_1cV,_9]]]];};},_1dz=function(_1dA,_1dB){return [0];},_1dC=function(_1dD,_1dE,_1dF,_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM,_1dN){var _1dO=new T(function(){return B(_1cx(_1dD,_1dE,_1dF,_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM,_1dN,_13i));}),_1dP=new T(function(){return B(_1a7(_1dN,_1dL,_1dM,_1dG,_1dJ,_1dF,_1dI,_1dH,_1dD,_1dE));}),_1dQ=[0,_1dP,new T(function(){return B(_131(_1by,_14v,new T(function(){return B(_ZR(new T(function(){return B(_107(new T(function(){return B(_3W(_1dJ,_1dI,_1dH,_1dG,_1dF,_1dD,_1dE));})));})));}),new T(function(){return B(_13Q(new T(function(){return B(_14j(new T(function(){return B(_bI(_1dJ,_1dI,_1dH,_1dG,_1dF,_1dD,_1dE));})));})));}),_1dJ,_1dI,_1dH,_1dG,_1dF,_1dD,_1dE));}),_1dz,_1];return function(_1dR,_1dS,_1dT){var _1dU=B(_8T(function(_1dV){var _1dW=B(A(_1dP,[new T(function(){return B(A(_1dO,[_1dV,_1dS,_1dT]));}),_1dV]));return _1dW[0]==0?false:B(_1cb(_1dQ,_1dW[1]))[0]==0?true:false;},E(_1dR)[1]));if(!_1dU[0]){return [0];}else{var _1dX=_1dU[1],_1dY=new T(function(){return B(A(_1dO,[_1dX,_1dS,_1dT]));}),_1dZ=B(A(_1dP,[_1dX,_1dY]));if(!_1dZ[0]){return [0];}else{var _1e0=B(_1cb(_1dQ,_1dZ[1]));if(!_1e0[0]){var _1e1=_1e0[1];return [1,new T(function(){var _1e2=E(E(_1dY)[2]);return [0,new T(function(){return B(_3d(function(_1e3){return new F(function(){return _116(_1e1,_1e3);});},_1e2[1]));}),new T(function(){return B(_116(_1e1,_1e2[2]));})];})];}else{return [0];}}}};},_1e4=[1],_1e5=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1e6=function(_1e7){return new F(function(){return err(_1e5);});},_1e8=new T(function(){return B(_1e6(_));}),_1e9=function(_1ea,_1eb,_1ec){var _1ed=E(_1ec);if(!_1ed[0]){var _1ee=_1ed[1],_1ef=E(_1eb);if(!_1ef[0]){var _1eg=_1ef[1],_1eh=_1ef[2];if(_1eg<=(imul(3,_1ee)|0)){return [0,(1+_1eg|0)+_1ee|0,E(E(_1ea)),E(_1ef),E(_1ed)];}else{var _1ei=E(_1ef[3]);if(!_1ei[0]){var _1ej=_1ei[1],_1ek=E(_1ef[4]);if(!_1ek[0]){var _1el=_1ek[1],_1em=_1ek[2],_1en=_1ek[3];if(_1el>=(imul(2,_1ej)|0)){var _1eo=function(_1ep){var _1eq=E(_1ek[4]);return _1eq[0]==0?[0,(1+_1eg|0)+_1ee|0,E(_1em),E([0,(1+_1ej|0)+_1ep|0,E(_1eh),E(_1ei),E(_1en)]),E([0,(1+_1ee|0)+_1eq[1]|0,E(E(_1ea)),E(_1eq),E(_1ed)])]:[0,(1+_1eg|0)+_1ee|0,E(_1em),E([0,(1+_1ej|0)+_1ep|0,E(_1eh),E(_1ei),E(_1en)]),E([0,1+_1ee|0,E(E(_1ea)),E(_1e4),E(_1ed)])];},_1er=E(_1en);return _1er[0]==0?B(_1eo(_1er[1])):B(_1eo(0));}else{return [0,(1+_1eg|0)+_1ee|0,E(_1eh),E(_1ei),E([0,(1+_1ee|0)+_1el|0,E(E(_1ea)),E(_1ek),E(_1ed)])];}}else{return E(_1e8);}}else{return E(_1e8);}}}else{return [0,1+_1ee|0,E(E(_1ea)),E(_1e4),E(_1ed)];}}else{var _1es=E(_1eb);if(!_1es[0]){var _1et=_1es[1],_1eu=_1es[2],_1ev=_1es[4],_1ew=E(_1es[3]);if(!_1ew[0]){var _1ex=_1ew[1],_1ey=E(_1ev);if(!_1ey[0]){var _1ez=_1ey[1],_1eA=_1ey[2],_1eB=_1ey[3];if(_1ez>=(imul(2,_1ex)|0)){var _1eC=function(_1eD){var _1eE=E(_1ey[4]);return _1eE[0]==0?[0,1+_1et|0,E(_1eA),E([0,(1+_1ex|0)+_1eD|0,E(_1eu),E(_1ew),E(_1eB)]),E([0,1+_1eE[1]|0,E(E(_1ea)),E(_1eE),E(_1e4)])]:[0,1+_1et|0,E(_1eA),E([0,(1+_1ex|0)+_1eD|0,E(_1eu),E(_1ew),E(_1eB)]),E([0,1,E(E(_1ea)),E(_1e4),E(_1e4)])];},_1eF=E(_1eB);return _1eF[0]==0?B(_1eC(_1eF[1])):B(_1eC(0));}else{return [0,1+_1et|0,E(_1eu),E(_1ew),E([0,1+_1ez|0,E(E(_1ea)),E(_1ey),E(_1e4)])];}}else{return [0,3,E(_1eu),E(_1ew),E([0,1,E(E(_1ea)),E(_1e4),E(_1e4)])];}}else{var _1eG=E(_1ev);return _1eG[0]==0?[0,3,E(_1eG[2]),E([0,1,E(_1eu),E(_1e4),E(_1e4)]),E([0,1,E(E(_1ea)),E(_1e4),E(_1e4)])]:[0,2,E(E(_1ea)),E(_1es),E(_1e4)];}}else{return [0,1,E(E(_1ea)),E(_1e4),E(_1e4)];}}},_1eH=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_1eI=function(_1eJ){return new F(function(){return err(_1eH);});},_1eK=new T(function(){return B(_1eI(_));}),_1eL=function(_1eM,_1eN,_1eO){var _1eP=E(_1eN);if(!_1eP[0]){var _1eQ=_1eP[1],_1eR=E(_1eO);if(!_1eR[0]){var _1eS=_1eR[1],_1eT=_1eR[2];if(_1eS<=(imul(3,_1eQ)|0)){return [0,(1+_1eQ|0)+_1eS|0,E(E(_1eM)),E(_1eP),E(_1eR)];}else{var _1eU=E(_1eR[3]);if(!_1eU[0]){var _1eV=_1eU[1],_1eW=_1eU[2],_1eX=_1eU[3],_1eY=E(_1eR[4]);if(!_1eY[0]){var _1eZ=_1eY[1];if(_1eV>=(imul(2,_1eZ)|0)){var _1f0=function(_1f1){var _1f2=E(_1eM),_1f3=E(_1eU[4]);return _1f3[0]==0?[0,(1+_1eQ|0)+_1eS|0,E(_1eW),E([0,(1+_1eQ|0)+_1f1|0,E(_1f2),E(_1eP),E(_1eX)]),E([0,(1+_1eZ|0)+_1f3[1]|0,E(_1eT),E(_1f3),E(_1eY)])]:[0,(1+_1eQ|0)+_1eS|0,E(_1eW),E([0,(1+_1eQ|0)+_1f1|0,E(_1f2),E(_1eP),E(_1eX)]),E([0,1+_1eZ|0,E(_1eT),E(_1e4),E(_1eY)])];},_1f4=E(_1eX);return _1f4[0]==0?B(_1f0(_1f4[1])):B(_1f0(0));}else{return [0,(1+_1eQ|0)+_1eS|0,E(_1eT),E([0,(1+_1eQ|0)+_1eV|0,E(E(_1eM)),E(_1eP),E(_1eU)]),E(_1eY)];}}else{return E(_1eK);}}else{return E(_1eK);}}}else{return [0,1+_1eQ|0,E(E(_1eM)),E(_1eP),E(_1e4)];}}else{var _1f5=E(_1eO);if(!_1f5[0]){var _1f6=_1f5[1],_1f7=_1f5[2],_1f8=_1f5[4],_1f9=E(_1f5[3]);if(!_1f9[0]){var _1fa=_1f9[1],_1fb=_1f9[2],_1fc=_1f9[3],_1fd=E(_1f8);if(!_1fd[0]){var _1fe=_1fd[1];if(_1fa>=(imul(2,_1fe)|0)){var _1ff=function(_1fg){var _1fh=E(_1eM),_1fi=E(_1f9[4]);return _1fi[0]==0?[0,1+_1f6|0,E(_1fb),E([0,1+_1fg|0,E(_1fh),E(_1e4),E(_1fc)]),E([0,(1+_1fe|0)+_1fi[1]|0,E(_1f7),E(_1fi),E(_1fd)])]:[0,1+_1f6|0,E(_1fb),E([0,1+_1fg|0,E(_1fh),E(_1e4),E(_1fc)]),E([0,1+_1fe|0,E(_1f7),E(_1e4),E(_1fd)])];},_1fj=E(_1fc);return _1fj[0]==0?B(_1ff(_1fj[1])):B(_1ff(0));}else{return [0,1+_1f6|0,E(_1f7),E([0,1+_1fa|0,E(E(_1eM)),E(_1e4),E(_1f9)]),E(_1fd)];}}else{return [0,3,E(_1fb),E([0,1,E(E(_1eM)),E(_1e4),E(_1e4)]),E([0,1,E(_1f7),E(_1e4),E(_1e4)])];}}else{var _1fk=E(_1f8);return _1fk[0]==0?[0,3,E(_1f7),E([0,1,E(E(_1eM)),E(_1e4),E(_1e4)]),E(_1fk)]:[0,2,E(E(_1eM)),E(_1e4),E(_1f5)];}}else{return [0,1,E(E(_1eM)),E(_1e4),E(_1e4)];}}},_1fl=function(_1fm){return [0,1,E(E(_1fm)),E(_1e4),E(_1e4)];},_1fn=function(_1fo,_1fp){var _1fq=E(_1fp);if(!_1fq[0]){return new F(function(){return _1e9(_1fq[2],B(_1fn(_1fo,_1fq[3])),_1fq[4]);});}else{return new F(function(){return _1fl(_1fo);});}},_1fr=function(_1fs,_1ft){var _1fu=E(_1ft);if(!_1fu[0]){return new F(function(){return _1eL(_1fu[2],_1fu[3],B(_1fr(_1fs,_1fu[4])));});}else{return new F(function(){return _1fl(_1fs);});}},_1fv=function(_1fw,_1fx,_1fy,_1fz,_1fA){return new F(function(){return _1eL(_1fy,_1fz,B(_1fr(_1fw,_1fA)));});},_1fB=function(_1fC,_1fD,_1fE,_1fF,_1fG){return new F(function(){return _1e9(_1fE,B(_1fn(_1fC,_1fF)),_1fG);});},_1fH=function(_1fI,_1fJ,_1fK,_1fL,_1fM,_1fN){var _1fO=E(_1fJ);if(!_1fO[0]){var _1fP=_1fO[1],_1fQ=_1fO[2],_1fR=_1fO[3],_1fS=_1fO[4];if((imul(3,_1fP)|0)>=_1fK){if((imul(3,_1fK)|0)>=_1fP){return [0,(_1fP+_1fK|0)+1|0,E(E(_1fI)),E(_1fO),E([0,_1fK,E(_1fL),E(_1fM),E(_1fN)])];}else{return new F(function(){return _1eL(_1fQ,_1fR,B(_1fH(_1fI,_1fS,_1fK,_1fL,_1fM,_1fN)));});}}else{return new F(function(){return _1e9(_1fL,B(_1fT(_1fI,_1fP,_1fQ,_1fR,_1fS,_1fM)),_1fN);});}}else{return new F(function(){return _1fB(_1fI,_1fK,_1fL,_1fM,_1fN);});}},_1fT=function(_1fU,_1fV,_1fW,_1fX,_1fY,_1fZ){var _1g0=E(_1fZ);if(!_1g0[0]){var _1g1=_1g0[1],_1g2=_1g0[2],_1g3=_1g0[3],_1g4=_1g0[4];if((imul(3,_1fV)|0)>=_1g1){if((imul(3,_1g1)|0)>=_1fV){return [0,(_1fV+_1g1|0)+1|0,E(E(_1fU)),E([0,_1fV,E(_1fW),E(_1fX),E(_1fY)]),E(_1g0)];}else{return new F(function(){return _1eL(_1fW,_1fX,B(_1fH(_1fU,_1fY,_1g1,_1g2,_1g3,_1g4)));});}}else{return new F(function(){return _1e9(_1g2,B(_1fT(_1fU,_1fV,_1fW,_1fX,_1fY,_1g3)),_1g4);});}}else{return new F(function(){return _1fv(_1fU,_1fV,_1fW,_1fX,_1fY);});}},_1g5=function(_1g6,_1g7,_1g8){var _1g9=E(_1g7);if(!_1g9[0]){var _1ga=_1g9[1],_1gb=_1g9[2],_1gc=_1g9[3],_1gd=_1g9[4],_1ge=E(_1g8);if(!_1ge[0]){var _1gf=_1ge[1],_1gg=_1ge[2],_1gh=_1ge[3],_1gi=_1ge[4];if((imul(3,_1ga)|0)>=_1gf){if((imul(3,_1gf)|0)>=_1ga){return [0,(_1ga+_1gf|0)+1|0,E(E(_1g6)),E(_1g9),E(_1ge)];}else{return new F(function(){return _1eL(_1gb,_1gc,B(_1fH(_1g6,_1gd,_1gf,_1gg,_1gh,_1gi)));});}}else{return new F(function(){return _1e9(_1gg,B(_1fT(_1g6,_1ga,_1gb,_1gc,_1gd,_1gh)),_1gi);});}}else{return new F(function(){return _1fv(_1g6,_1ga,_1gb,_1gc,_1gd);});}}else{return new F(function(){return _1fn(_1g6,_1g8);});}},_1gj=function(_1gk,_1gl,_1gm,_1gn){var _1go=E(_1gn);if(!_1go[0]){var _1gp=new T(function(){var _1gq=B(_1gj(_1go[1],_1go[2],_1go[3],_1go[4]));return [0,_1gq[1],_1gq[2]];});return [0,new T(function(){return E(E(_1gp)[1]);}),new T(function(){return B(_1e9(_1gl,_1gm,E(_1gp)[2]));})];}else{return [0,_1gl,_1gm];}},_1gr=function(_1gs,_1gt,_1gu,_1gv){var _1gw=E(_1gu);if(!_1gw[0]){var _1gx=new T(function(){var _1gy=B(_1gr(_1gw[1],_1gw[2],_1gw[3],_1gw[4]));return [0,_1gy[1],_1gy[2]];});return [0,new T(function(){return E(E(_1gx)[1]);}),new T(function(){return B(_1eL(_1gt,E(_1gx)[2],_1gv));})];}else{return [0,_1gt,_1gv];}},_1gz=function(_1gA,_1gB){var _1gC=E(_1gA);if(!_1gC[0]){var _1gD=_1gC[1],_1gE=E(_1gB);if(!_1gE[0]){var _1gF=_1gE[1];if(_1gD<=_1gF){var _1gG=B(_1gr(_1gF,_1gE[2],_1gE[3],_1gE[4]));return new F(function(){return _1e9(_1gG[1],_1gC,_1gG[2]);});}else{var _1gH=B(_1gj(_1gD,_1gC[2],_1gC[3],_1gC[4]));return new F(function(){return _1eL(_1gH[1],_1gH[2],_1gE);});}}else{return E(_1gC);}}else{return E(_1gB);}},_1gI=function(_1gJ,_1gK,_1gL,_1gM,_1gN){var _1gO=E(_1gJ);if(!_1gO[0]){var _1gP=_1gO[1],_1gQ=_1gO[2],_1gR=_1gO[3],_1gS=_1gO[4];if((imul(3,_1gP)|0)>=_1gK){if((imul(3,_1gK)|0)>=_1gP){return new F(function(){return _1gz(_1gO,[0,_1gK,E(_1gL),E(_1gM),E(_1gN)]);});}else{return new F(function(){return _1eL(_1gQ,_1gR,B(_1gI(_1gS,_1gK,_1gL,_1gM,_1gN)));});}}else{return new F(function(){return _1e9(_1gL,B(_1gT(_1gP,_1gQ,_1gR,_1gS,_1gM)),_1gN);});}}else{return [0,_1gK,E(_1gL),E(_1gM),E(_1gN)];}},_1gT=function(_1gU,_1gV,_1gW,_1gX,_1gY){var _1gZ=E(_1gY);if(!_1gZ[0]){var _1h0=_1gZ[1],_1h1=_1gZ[2],_1h2=_1gZ[3],_1h3=_1gZ[4];if((imul(3,_1gU)|0)>=_1h0){if((imul(3,_1h0)|0)>=_1gU){return new F(function(){return _1gz([0,_1gU,E(_1gV),E(_1gW),E(_1gX)],_1gZ);});}else{return new F(function(){return _1eL(_1gV,_1gW,B(_1gI(_1gX,_1h0,_1h1,_1h2,_1h3)));});}}else{return new F(function(){return _1e9(_1h1,B(_1gT(_1gU,_1gV,_1gW,_1gX,_1h2)),_1h3);});}}else{return [0,_1gU,E(_1gV),E(_1gW),E(_1gX)];}},_1h4=function(_1h5,_1h6){var _1h7=E(_1h5);if(!_1h7[0]){var _1h8=_1h7[1],_1h9=_1h7[2],_1ha=_1h7[3],_1hb=_1h7[4],_1hc=E(_1h6);if(!_1hc[0]){var _1hd=_1hc[1],_1he=_1hc[2],_1hf=_1hc[3],_1hg=_1hc[4];if((imul(3,_1h8)|0)>=_1hd){if((imul(3,_1hd)|0)>=_1h8){return new F(function(){return _1gz(_1h7,_1hc);});}else{return new F(function(){return _1eL(_1h9,_1ha,B(_1gI(_1hb,_1hd,_1he,_1hf,_1hg)));});}}else{return new F(function(){return _1e9(_1he,B(_1gT(_1h8,_1h9,_1ha,_1hb,_1hf)),_1hg);});}}else{return E(_1h7);}}else{return E(_1h6);}},_1hh=function(_1hi,_1hj){var _1hk=E(_1hj);if(!_1hk[0]){var _1hl=_1hk[2],_1hm=_1hk[3],_1hn=_1hk[4];if(!B(A(_1hi,[_1hl]))){return new F(function(){return _1h4(B(_1hh(_1hi,_1hm)),B(_1hh(_1hi,_1hn)));});}else{return new F(function(){return _1g5(_1hl,B(_1hh(_1hi,_1hm)),B(_1hh(_1hi,_1hn)));});}}else{return [1];}},_1ho=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_1hp=new T(function(){return B(err(_1ho));}),_1hq=function(_1hr,_1hs,_1ht,_1hu){while(1){var _1hv=E(_1ht);if(!_1hv[0]){_1hr=_1hv[1];_1hs=_1hv[2];_1ht=_1hv[3];_1hu=_1hv[4];continue;}else{return E(_1hs);}}},_1hw=function(_1hx,_1hy){var _1hz=B(_1hh(function(_1hA){return new F(function(){return _3x(E(_1hA)[2],_1hx);});},_1hy));if(!_1hz[0]){var _1hB=E(_1hz[3]);return _1hB[0]==0?B(_1hq(_1hB[1],_1hB[2],_1hB[3],_1hB[4])):E(_1hz[2]);}else{return E(_1hp);}},_1hC=[1,_9],_1hD=function(_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ,_1hK,_1hL,_1hM,_1hN,_1hO,_1hP,_1hQ,_1hR){var _1hS=E(_1hR);if(!_1hS[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_1hL,[_1hQ]));}),_9]],_9],[1,[1,new T(function(){return B(A(_1hL,[_1hQ]));}),_9]]]];}else{var _1hT=function(_1hU){var _1hV=E(_1hU);if(!_1hV[0]){return E(_1hC);}else{var _1hW=E(_1hV[1]),_1hX=B(_1hD(_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ,_1hK,_1hL,_1hM,_1hN,_1hO,_1hP,_1hW[1],_1hW[2]));if(!_1hX[0]){return [0];}else{var _1hY=B(_1hT(_1hV[2]));return _1hY[0]==0?[0]:[1,[1,_1hX[1],_1hY[1]]];}}},_1hZ=B(_1hT(_1hS[2]));return _1hZ[0]==0?[0]:B(A(_1dC,[_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ,_1hK,_1hL,_1hM,_1hN,_1hO,new T(function(){return B(_1hw(_1hS[1],_1hP));}),_1hZ[1],_1hQ]));}},_1i0=function(_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9,_1ia,_1ib,_1ic,_1id,_1ie,_1if){var _1ig=E(_1if);return new F(function(){return _1hD(_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9,_1ic,_1id,_1ie,_1ig[1],_1ig[2]);});},_1ih=new T(function(){return B(unCStr("div"));}),_1ii=function(_1ij,_1ik,_1il,_){var _1im=jsCreateElem(toJSStr(E(_1ih))),_1in=_1im,_1io=jsAppendChild(_1in,E(_1il)[1]),_1ip=[0,_1in],_1iq=B(A(_1ij,[_1ik,_1ip,_])),_1ir=_1iq;return _1ip;},_1is=function(_1it){return new F(function(){return _dq(_1it,_9);});},_1iu=function(_1iv,_1iw,_1ix){var _1iy=function(_1iz){return _1iz<=B(_16f(_1ix,0))?[1,[0,new T(function(){var _1iA=_1iv-1|0;if(_1iA>=0){var _1iB=B(_gE(B(_1is(_1ix)),_1iA));}else{var _1iB=E(_gB);}var _1iC=_1iB,_1iD=_1iC;return _1iD;}),new T(function(){var _1iE=_1iw-1|0;if(_1iE>=0){var _1iF=B(_gE(B(_1is(_1ix)),_1iE));}else{var _1iF=E(_gB);}var _1iG=_1iF,_1iH=_1iG;return _1iH;})]]:[0];};return _1iv>_1iw?B(_1iy(_1iv)):B(_1iy(_1iw));},_1iI=new T(function(){return B(unCStr("is unavailable"));}),_1iJ=function(_1iK,_1iL,_1iM,_1iN,_1iO,_1iP){var _1iQ=B(_1iu(_1iL,_1iM,_1iP));if(!_1iQ[0]){return [0,[1,new T(function(){return B(unAppCStr("one of ",new T(function(){return B(_e(B(_F(0,_1iL,_9)),new T(function(){return B(unAppCStr(" or ",new T(function(){return B(_e(B(_F(0,_1iM,_9)),_1iI));})));},1)));})));}),_1iO],[1,_4O,_1iP]];}else{var _1iR=E(_1iQ[1]),_1iS=_1iR[2],_1iT=E(_1iR[1]);if(!_1iT[0]){return E(_1iS)[0]==0?[0,[1,new T(function(){return B(unAppCStr("depends on unjustified lines ",new T(function(){return B(_e(B(_F(0,_1iL,_9)),new T(function(){return B(unAppCStr(", ",new T(function(){return B(_F(0,_1iM,_9));})));},1)));})));}),_1iO],[1,_4O,_1iP]]:[0,[1,new T(function(){return B(unAppCStr("depends on unjustified line ",new T(function(){return B(_F(0,_1iL,_9));})));}),_1iO],[1,_4O,_1iP]];}else{var _1iU=E(_1iS);return _1iU[0]==0?[0,[1,new T(function(){return B(unAppCStr("depends on unjustified line ",new T(function(){return B(_F(0,_1iM,_9));})));}),_1iO],[1,_4O,_1iP]]:[0,[1,_9,_1iO],[1,[1,[0,_1iK,[1,_1iN,[1,_1iT[1],[1,_1iU[1],_9]]]]],_1iP]];}}},_1iV=function(_1iW,_1iX){return _1iW<=B(_16f(_1iX,0))?[1,new T(function(){var _1iY=_1iW-1|0;if(_1iY>=0){var _1iZ=B(_gE(B(_1is(_1iX)),_1iY));}else{var _1iZ=E(_gB);}var _1j0=_1iZ,_1j1=_1j0;return _1j1;})]:[0];},_1j2=function(_1j3,_1j4,_1j5,_1j6,_1j7){var _1j8=B(_1iV(_1j4,_1j7));if(!_1j8[0]){return [0,[1,new T(function(){return B(unAppCStr("line",new T(function(){return B(_e(B(_F(0,_1j4,_9)),_1iI));})));}),_1j6],[1,_4O,_1j7]];}else{var _1j9=E(_1j8[1]);return _1j9[0]==0?[0,[1,new T(function(){return B(unAppCStr("depends on an unjustified line ",new T(function(){return B(_F(0,_1j4,_9));})));}),_1j6],[1,_4O,_1j7]]:[0,[1,_9,_1j6],[1,[1,[0,_1j3,[1,_1j5,[1,_1j9[1],_9]]]],_1j7]];}},_1ja=[0],_1jb=new T(function(){return B(unCStr("PR"));}),_1jc=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1jd=new T(function(){return B(unCStr("wrong number of premises"));}),_1je=new T(function(){return B(unCStr("Impossible Error 1"));}),_1jf=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1jg=function(_1jh,_1ji,_1jj,_1jk,_1jl,_1jm){var _1jn=function(_1jo){var _1jp=B(A(_1jk,[_1ji]));if(!_1jp[0]){return [0,[1,_1jf,_1jl],[1,_4O,_1jm]];}else{var _1jq=E(_1jp[1]);if(!_1jq[0]){switch(E(E(_1jq[1])[1])){case 1:var _1jr=E(_1jj);if(!_1jr[0]){return [0,[1,_1jd,_1jl],[1,_4O,_1jm]];}else{if(!E(_1jr[2])[0]){return new F(function(){return _1j2(_1jh,E(_1jr[1])[1],_1ji,_1jl,_1jm);});}else{return [0,[1,_1jd,_1jl],[1,_4O,_1jm]];}}break;case 2:var _1js=E(_1jj);if(!_1js[0]){return [0,[1,_1jd,_1jl],[1,_4O,_1jm]];}else{var _1jt=E(_1js[2]);if(!_1jt[0]){return [0,[1,_1jd,_1jl],[1,_4O,_1jm]];}else{if(!E(_1jt[2])[0]){return new F(function(){return _1iJ(_1jh,E(_1js[1])[1],E(_1jt[1])[1],_1ji,_1jl,_1jm);});}else{return [0,[1,_1jd,_1jl],[1,_4O,_1jm]];}}}break;default:return [0,[1,_1je,_1jl],[1,_4O,_1jm]];}}else{return [0,[1,_1jc,_1jl],[1,_4O,_1jm]];}}};return !B(_3x(_1ji,_1jb))?B(_1jn(_)):E(_1jj)[0]==0?[0,[1,_9,_1jl],[1,[1,[0,_1jh,_1ja]],_1jm]]:B(_1jn(_));},_1ju=new T(function(){return B(unCStr(" is unavailable"));}),_1jv=function(_1jw,_1jx,_1jy,_1jz){return E(B(_1jA(_1jw,_1jx,[1,_9,_1jy],[1,_4O,_1jz]))[2]);},_1jB=function(_1jC,_1jD,_1jE,_1jF,_1jG,_1jH,_1jI,_1jJ){var _1jK=B(_1iu(_1jF,_1jG,B(_1jv(_1jC,_1jD,_1jI,_1jJ))));if(!_1jK[0]){return new F(function(){return _1jA(_1jC,_1jD,[1,new T(function(){return B(unAppCStr("one of the lines ",new T(function(){return B(_e(B(_F(0,_1jF,_9)),new T(function(){return B(unAppCStr(" or ",new T(function(){return B(_e(B(_F(0,_1jG,_9)),_1ju));})));},1)));})));}),_1jI],[1,_4O,_1jJ]);});}else{var _1jL=E(_1jK[1]),_1jM=_1jL[2],_1jN=E(_1jL[1]);if(!_1jN[0]){return E(_1jM)[0]==0?B(_1jA(_1jC,_1jD,[1,new T(function(){return B(unAppCStr("depends on an unjustified lines ",new T(function(){return B(_e(B(_F(0,_1jG,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_F(0,_1jG,_9));})));},1)));})));}),_1jI],[1,_4O,_1jJ])):B(_1jA(_1jC,_1jD,[1,new T(function(){return B(unAppCStr("depends on unjustified line ",new T(function(){return B(_F(0,_1jF,_9));})));}),_1jI],[1,_4O,_1jJ]));}else{var _1jO=E(_1jM);return _1jO[0]==0?B(_1jA(_1jC,_1jD,[1,new T(function(){return B(unAppCStr("depends on unjustified line ",new T(function(){return B(_F(0,_1jG,_9));})));}),_1jI],[1,_4O,_1jJ])):B(_1jA(_1jC,_1jD,[1,_9,_1jI],[1,[1,[0,_1jE,[1,_1jH,[1,_1jN[1],[1,_1jO[1],_9]]]]],_1jJ]));}}},_1jP=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1jQ=function(_1jR,_1jS,_1jT,_1jU,_1jV,_1jW,_1jX){var _1jY=E(_1jV);if(!_1jY[0]){return new F(function(){return _1jA(_1jR,_1jS,[1,_1jP,_1jW],[1,_4O,_1jX]);});}else{var _1jZ=E(_1jY[2]);if(!_1jZ[0]){return new F(function(){return _1jA(_1jR,_1jS,[1,_1jP,_1jW],[1,_4O,_1jX]);});}else{if(!E(_1jZ[2])[0]){return new F(function(){return _1jB(_1jR,_1jS,_1jT,E(_1jY[1])[1],E(_1jZ[1])[1],_1jU,_1jW,_1jX);});}else{return new F(function(){return _1jA(_1jR,_1jS,[1,_1jP,_1jW],[1,_4O,_1jX]);});}}}},_1k0=function(_1k1,_1k2,_1k3){return [0,[1,_9,_1k2],[1,_4O,new T(function(){var _1k4=B(_16f(_1k2,0))-E(_1k1)[1]|0,_1k5=new T(function(){return _1k4>=0?B(_1aT(_1k4,_1k3)):E(_1k3);});if(_1k4>0){var _1k6=function(_1k7,_1k8){var _1k9=E(_1k7);return _1k9[0]==0?E(_1k5):_1k8>1?[1,_4O,new T(function(){return B(_1k6(_1k9[2],_1k8-1|0));})]:E([1,_4O,_1k5]);},_1ka=B(_1k6(_1k3,_1k4));}else{var _1ka=E(_1k5);}var _1kb=_1ka,_1kc=_1kb,_1kd=_1kc,_1ke=_1kd;return _1ke;})]];},_1kf=function(_1kg,_1kh,_1ki,_1kj,_1kk,_1kl,_1km){var _1kn=new T(function(){return E(B(_1jA(_1kg,_1kh,[1,_9,_1kl],[1,_4O,_1km]))[2]);});if(_1kj<=B(_16f(_1kn,0))){var _1ko=_1kj-1|0;if(_1ko>=0){var _1kp=B(_gE(B(_1is(_1kn)),_1ko));return _1kp[0]==0?B(_1jA(_1kg,_1kh,[1,new T(function(){return B(unAppCStr("depends on unjustified line ",new T(function(){return B(_F(0,_1kj,_9));})));}),_1kl],[1,_4O,_1km])):B(_1jA(_1kg,_1kh,[1,_9,_1kl],[1,[1,[0,_1ki,[1,_1kk,[1,_1kp[1],_9]]]],_1km]));}else{return E(_gB);}}else{return new F(function(){return _1jA(_1kg,_1kh,[1,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_1kj,_9)),_1ju));})));}),_1kl],[1,_4O,_1km]);});}},_1kq=function(_1kr,_1ks,_1kt,_1ku,_1kv,_1kw,_1kx){var _1ky=E(_1kv);if(!_1ky[0]){return new F(function(){return _1jA(_1kr,_1ks,[1,_1jP,_1kw],[1,_4O,_1kx]);});}else{if(!E(_1ky[2])[0]){return new F(function(){return _1kf(_1kr,_1ks,_1kt,E(_1ky[1])[1],_1ku,_1kw,_1kx);});}else{return new F(function(){return _1jA(_1kr,_1ks,[1,_1jP,_1kw],[1,_4O,_1kx]);});}}},_1kz=new T(function(){return B(unCStr("Open Subproof"));}),_1kA=new T(function(){return B(unCStr("Impossible Error 2"));}),_1kB=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1kC=new T(function(){return B(unCStr("SHOW"));}),_1kD=function(_1kE,_1kF,_1kG,_1kH,_1kI,_1kJ,_1kK){if(!B(_3x(_1kF,_1kC))){var _1kL=B(A(_1kH,[_1kF]));if(!_1kL[0]){return [0,[1,_1jf,_1kJ],[1,_4O,_1kK]];}else{var _1kM=E(_1kL[1]);if(!_1kM[0]){return [0,[1,_1kB,_1kJ],[1,_4O,_1kK]];}else{switch(E(E(_1kM[1])[1])){case 1:var _1kN=B(_1kq(_1kI,_1kH,_1kE,_1kF,_1kG,_1kJ,_1kK));return new F(function(){return _1k0(new T(function(){return [0,B(_16f(_1kJ,0))+1|0];},1),_1kN[1],_1kN[2]);});break;case 2:var _1kO=B(_1jQ(_1kI,_1kH,_1kE,_1kF,_1kG,_1kJ,_1kK));return new F(function(){return _1k0(new T(function(){return [0,B(_16f(_1kJ,0))+1|0];},1),_1kO[1],_1kO[2]);});break;default:return [0,[1,_1kA,_1kJ],[1,_4O,_1kK]];}}}}else{var _1kP=B(_1jA(_1kI,_1kH,[1,_1kz,_1kJ],[1,_4O,_1kK]));return new F(function(){return _1k0(new T(function(){return [0,B(_16f(_1kJ,0))+1|0];},1),_1kP[1],_1kP[2]);});}},_1kQ=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1kR=new T(function(){return B(unCStr("incomplete line"));}),_1kS=function(_1kT,_1kU,_1kV,_1kW,_1kX){var _1kY=E(_1kT);if(!_1kY[0]){return E(_1kU)[0]==0?[0,[1,_1kR,_1kW],[1,_4O,_1kX]]:[0,[1,_1kQ,_1kW],[1,_4O,_1kX]];}else{var _1kZ=_1kY[1],_1l0=E(_1kU);if(!_1l0[0]){var _1l1=E(_1kZ);return new F(function(){return _1jg(_1l1[1],_1l1[2],_1l1[3],_1kV,_1kW,_1kX);});}else{var _1l2=E(_1kZ);return new F(function(){return _1kD(_1l2[1],_1l2[2],_1l2[3],_1kV,_1l0,_1kW,_1kX);});}}},_1jA=function(_1l3,_1l4,_1l5,_1l6){return new F(function(){return (function(_1l7,_1l8,_1l9){while(1){var _1la=E(_1l9);if(!_1la[0]){return [0,_1l7,_1l8];}else{var _1lb=E(_1la[1]),_1lc=B(_1kS(_1lb[1],_1lb[2],_1l4,_1l7,_1l8));_1l7=_1lc[1];_1l8=_1lc[2];_1l9=_1la[2];continue;}}})(_1l5,_1l6,_1l3);});},_1ld=function(_1le,_1lf){while(1){var _1lg=E(_1lf);if(!_1lg[0]){return true;}else{if(!B(A(_1le,[_1lg[1]]))){return false;}else{_1lf=_1lg[2];continue;}}}},_1lh=[0,666],_1li=[0,_,_1lh],_1lj=[1,_1li],_1lk=[0,_1lj,_1ja],_1ll=function(_1lm){return new F(function(){return _3x(_1lm,_9);});},_1ln=function(_1lo,_1lp){var _1lq=B(_1jA(_1lo,_1lp,_9,_9)),_1lr=_1lq[1];return !B(_1ld(_1ll,_1lr))?[0,_1lr]:[1,new T(function(){var _1ls=B(_16f(_1lo,0))-1|0;if(_1ls>=0){var _1lt=B(_gE(B(_dq(_1lq[2],_9)),_1ls)),_1lu=_1lt[0]==0?E(_1lk):E(_1lt[1]);}else{var _1lu=E(_gB);}var _1lv=_1lu,_1lw=_1lv,_1lx=_1lw;return _1lx;})];},_1ly=function(_1lz,_){return _1lz;},_1lA=function(_1lB){var _1lC=E(_1lB);return _1lC[0]==0?E(_1ly):function(_1lD,_){var _1lE=B(A(new T(function(){var _1lF=E(_1lC[1]);return B(_1lG(_1lF[1],_1lF[2]));}),[_1lD,_])),_1lH=_1lE,_1lI=B(A(new T(function(){return B(_1lA(_1lC[2]));}),[_1lD,_])),_1lJ=_1lI;return _1lD;};},_1lK=function(_1lL,_1lM){return function(_1lN,_){var _1lO=B(A(new T(function(){var _1lP=E(_1lL);return B(_1lG(_1lP[1],_1lP[2]));}),[_1lN,_])),_1lQ=_1lO,_1lR=B(A(new T(function(){return B(_1lA(_1lM));}),[_1lN,_])),_1lS=_1lR;return _1lN;};},_1lT=function(_1lU,_1lV){return new F(function(){return _F(0,E(_1lU)[1],_1lV);});},_1lW=function(_1lX){return function(_ma,_19i){return new F(function(){return _6v(new T(function(){return B(_23(_1lT,_1lX,_9));}),_ma,_19i);});};},_1lY=function(_1lZ){return function(_ma,_19i){return new F(function(){return _6v(new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1lZ,_V4));}),_ma,_19i);});};},_1m0=new T(function(){return B(unCStr("open"));}),_1m1=new T(function(){return B(unCStr("termination"));}),_1m2=new T(function(){return B(unCStr("closed"));}),_1m3=function(_1m4){var _1m5=E(_1m4);return _1m5[0]==0?E(_1ly):function(_1m6,_){var _1m7=B(A(new T(function(){var _1m8=E(_1m5[1]);return B(_1lG(_1m8[1],_1m8[2]));}),[_1m6,_])),_1m9=_1m7,_1ma=B(A(new T(function(){return B(_1m3(_1m5[2]));}),[_1m6,_])),_1mb=_1ma;return _1m6;};},_1mc=function(_1md,_1me){return function(_1mf,_){var _1mg=B(A(new T(function(){var _1mh=E(_1md);return B(_1lG(_1mh[1],_1mh[2]));}),[_1mf,_])),_1mi=_1mg,_1mj=B(A(new T(function(){return B(_1m3(_1me));}),[_1mf,_])),_1mk=_1mj;return _1mf;};},_1ml=new T(function(){return B(unCStr("SHOW"));}),_1lG=function(_1mm,_1mn){var _1mo=E(_1mm);if(!_1mo[0]){return function(_ma,_19i){return new F(function(){return _1ii(_6v,_1mo[1],_ma,_19i);});};}else{var _1mp=E(_1mo[1]),_1mq=_1mp[1],_1mr=_1mp[2],_1ms=_1mp[3];if(!B(_3x(_1mr,_1ml))){var _1mt=E(_1mn);return _1mt[0]==0?function(_ma,_19i){return new F(function(){return _1ii(_7s,function(_1mu,_){var _1mv=B(_7i(_1lY,_1mq,_1mu,_)),_1mw=_1mv,_1mx=B(_7i(_7s,function(_1my,_){var _1mz=B(_7i(_6v,_1mr,_1my,_)),_1mA=_1mz,_1mB=B(_7i(_1lW,_1ms,_1my,_)),_1mC=_1mB;return _1my;},_1mu,_)),_1mD=_1mx;return _1mu;},_ma,_19i);});}:function(_ma,_19i){return new F(function(){return _1ii(_7s,function(_1mE,_){var _1mF=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1mq,_V4));})));}),_1mE,_)),_1mG=_1mF,_1mH=B(_1ii(_7s,function(_1mI,_){var _1mJ=B(_7i(_7s,new T(function(){return B(_1lK(_1mt[1],_1mt[2]));}),_1mI,_)),_1mK=_1mJ,_1mL=B(_1ii(_7s,function(_1mM,_){var _1mN=B(_7i(_6v,_9,_1mM,_)),_1mO=_1mN,_1mP=B(A(_6C,[_6P,_1mO,_cn,_1m1,_])),_1mQ=_1mP,_1mR=B(_7i(_7s,function(_1mS,_){var _1mT=B(_7i(_6v,_1mr,_1mS,_)),_1mU=_1mT,_1mV=B(_7i(_1lW,_1ms,_1mS,_)),_1mW=_1mV;return _1mS;},_1mM,_)),_1mX=_1mR;return _1mM;},_1mI,_)),_1mY=_1mL;return _1mI;},_1mE,_)),_1mZ=_1mH,_1n0=B(A(_6C,[_6P,_1mZ,_cn,_1m2,_])),_1n1=_1n0;return _1mE;},_ma,_19i);});};}else{var _1n2=E(_1mn);return _1n2[0]==0?function(_ma,_19i){return new F(function(){return _1ii(_7s,function(_ca,_){return new F(function(){return _7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1mq,_V4));})));}),_ca,_);});},_ma,_19i);});}:function(_ma,_19i){return new F(function(){return _1ii(_7s,function(_1n3,_){var _1n4=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1mq,_V4));})));}),_1n3,_)),_1n5=_1n4,_1n6=B(_1ii(_7s,function(_ca,_){return new F(function(){return _7i(_7s,new T(function(){return B(_1mc(_1n2[1],_1n2[2]));}),_ca,_);});},_1n3,_)),_1n7=_1n6,_1n8=B(A(_6C,[_6P,_1n7,_cn,_1m0,_])),_1n9=_1n8;return _1n3;},_ma,_19i);});};}}},_1na=function(_1nb){var _1nc=E(_1nb);return _1nc[0]==0?E(_1ly):function(_1nd,_){var _1ne=B(A(new T(function(){var _1nf=E(_1nc[1]);return B(_1lG(_1nf[1],_1nf[2]));}),[_1nd,_])),_1ng=_1ne,_1nh=B(A(new T(function(){return B(_1na(_1nc[2]));}),[_1nd,_])),_1ni=_1nh;return _1nd;};},_1nj=new T(function(){return B(unCStr("errormsg"));}),_1nk=function(_ca,_){return new F(function(){return _1ii(_6v,_9,_ca,_);});},_1nl=[0,10006],_1nm=[1,_1nl,_9],_1nn=function(_1no){return !B(_3x(_1no,_9))?function(_ma,_19i){return new F(function(){return _1ii(_7s,function(_1np,_){var _1nq=B(_7i(_6v,_1nm,_1np,_)),_1nr=_1nq,_1ns=B(_7i(_6v,_1no,_1np,_)),_1nt=_1ns,_1nu=B(A(_6C,[_6P,_1nt,_cn,_1nj,_])),_1nv=_1nu;return _1np;},_ma,_19i);});}:E(_1nk);},_1nw=function(_1nx){var _1ny=E(_1nx);return _1ny[0]==0?E(_1ly):function(_1nz,_){var _1nA=B(A(new T(function(){return B(_1nn(_1ny[1]));}),[_1nz,_])),_1nB=_1nA,_1nC=B(A(new T(function(){return B(_1nw(_1ny[2]));}),[_1nz,_])),_1nD=_1nC;return _1nz;};},_1nE=[0,10],_1nF=[1,_1nE,_9],_1nG=function(_1nH,_1nI,_){var _1nJ=jsCreateElem(toJSStr(E(_1nH))),_1nK=_1nJ,_1nL=jsAppendChild(_1nK,E(_1nI)[1]);return [0,_1nK];},_1nM=function(_1nN,_1nO,_1nP,_){var _1nQ=B(_1nG(_1nN,_1nP,_)),_1nR=_1nQ,_1nS=B(A(_1nO,[_1nR,_])),_1nT=_1nS;return _1nR;},_1nU=new T(function(){return B(unCStr("()"));}),_1nV=new T(function(){return B(unCStr("GHC.Tuple"));}),_1nW=new T(function(){return B(unCStr("ghc-prim"));}),_1nX=new T(function(){var _1nY=hs_wordToWord64(2170319554),_1nZ=_1nY,_1o0=hs_wordToWord64(26914641),_1o1=_1o0;return [0,_1nZ,_1o1,[0,_1nZ,_1o1,_1nW,_1nV,_1nU],_9];}),_1o2=function(_1o3){return E(_1nX);},_1o4=new T(function(){return B(unCStr("PerchM"));}),_1o5=new T(function(){return B(unCStr("Haste.Perch"));}),_1o6=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1o7=new T(function(){var _1o8=hs_wordToWord64(3005229400),_1o9=_1o8,_1oa=hs_wordToWord64(2682402736),_1ob=_1oa;return [0,_1o9,_1ob,[0,_1o9,_1ob,_1o6,_1o5,_1o4],_9];}),_1oc=function(_1od){return E(_1o7);},_1oe=function(_1of){var _1og=E(_1of);if(!_1og[0]){return [0];}else{var _1oh=E(_1og[1]);return [1,[0,_1oh[1],_1oh[2]],new T(function(){return B(_1oe(_1og[2]));})];}},_1oi=function(_1oj,_1ok){var _1ol=E(_1oj);if(!_1ol){return [0,_9,_1ok];}else{var _1om=E(_1ok);if(!_1om[0]){return [0,_9,_9];}else{var _1on=new T(function(){var _1oo=B(_1oi(_1ol-1|0,_1om[2]));return [0,_1oo[1],_1oo[2]];});return [0,[1,_1om[1],new T(function(){return E(E(_1on)[1]);})],new T(function(){return E(E(_1on)[2]);})];}}},_1op=[0,120],_1oq=[0,48],_1or=function(_1os){var _1ot=new T(function(){var _1ou=B(_1oi(8,new T(function(){var _1ov=md5(toJSStr(E(_1os))),_1ow=_1ov;return fromJSStr(_1ow);})));return [0,_1ou[1],_1ou[2]];}),_1ox=parseInt([0,toJSStr([1,_1oq,[1,_1op,new T(function(){return E(E(_1ot)[1]);})]])]),_1oy=_1ox,_1oz=new T(function(){var _1oA=B(_1oi(8,new T(function(){return E(E(_1ot)[2]);})));return [0,_1oA[1],_1oA[2]];}),_1oB=parseInt([0,toJSStr([1,_1oq,[1,_1op,new T(function(){return E(E(_1oz)[1]);})]])]),_1oC=_1oB,_1oD=hs_mkWord64(_1oy,_1oC),_1oE=_1oD,_1oF=parseInt([0,toJSStr([1,_1oq,[1,_1op,new T(function(){return E(B(_1oi(8,new T(function(){return E(E(_1oz)[2]);})))[1]);})]])]),_1oG=_1oF,_1oH=hs_mkWord64(_1oG,_1oG),_1oI=_1oH;return [0,_1oE,_1oI];},_1oJ=function(_1oK,_1oL){var _1oM=jsShowI(_1oK),_1oN=_1oM,_1oO=md5(_1oN),_1oP=_1oO;return new F(function(){return _e(fromJSStr(_1oP),new T(function(){var _1oQ=jsShowI(_1oL),_1oR=_1oQ,_1oS=md5(_1oR),_1oT=_1oS;return fromJSStr(_1oT);},1));});},_1oU=function(_1oV){var _1oW=E(_1oV);return new F(function(){return _1oJ(_1oW[1],_1oW[2]);});},_1oX=function(_1oY,_1oZ){return function(_1p0){return E(new T(function(){var _1p1=B(A(_1oY,[_])),_1p2=E(_1p1[3]),_1p3=_1p2[1],_1p4=_1p2[2],_1p5=B(_e(_1p1[4],[1,new T(function(){return B(A(_1oZ,[_]));}),_9]));if(!_1p5[0]){var _1p6=[0,_1p3,_1p4,_1p2,_9];}else{var _1p7=B(_1or(new T(function(){return B(_8Q(B(_3d(_1oU,[1,[0,_1p3,_1p4],new T(function(){return B(_1oe(_1p5));})]))));},1))),_1p6=[0,_1p7[1],_1p7[2],_1p2,_1p5];}var _1p8=_1p6,_1p9=_1p8;return _1p9;}));};},_1pa=new T(function(){return B(_1oX(_1oc,_1o2));}),_1pb=function(_1pc,_1pd,_1pe,_){var _1pf=E(_1pd),_1pg=B(A(_1pc,[_1pe,_])),_1ph=_1pg,_1pi=B(A(_6C,[_6P,_1ph,_1pf[1],_1pf[2],_])),_1pj=_1pi;return _1ph;},_1pk=function(_1pl,_1pm){while(1){var _1pn=(function(_1po,_1pp){var _1pq=E(_1pp);if(!_1pq[0]){return E(_1po);}else{_1pl=function(_1pr,_){return new F(function(){return _1pb(_1po,_1pq[1],_1pr,_);});};_1pm=_1pq[2];return null;}})(_1pl,_1pm);if(_1pn!=null){return _1pn;}}},_1ps=new T(function(){return B(unCStr("value"));}),_1pt=new T(function(){return B(unCStr("id"));}),_1pu=new T(function(){return B(unCStr("onclick"));}),_1pv=new T(function(){return B(unCStr("checked"));}),_1pw=[0,_1pv,_9],_1px=new T(function(){return B(unCStr("type"));}),_1py=new T(function(){return B(unCStr("input"));}),_1pz=function(_1pA,_){return new F(function(){return _1nG(_1py,_1pA,_);});},_1pB=function(_1pC,_1pD,_1pE){return new F(function(){return _1pk(function(_1pr,_){return new F(function(){return _1pb(_1pC,_1pD,_1pr,_);});},_1pE);});},_1pF=function(_1pG,_1pH,_1pI,_1pJ,_1pK){var _1pL=new T(function(){var _1pM=new T(function(){return B(_1pB(_1pz,[0,_1px,_1pH],[1,[0,_1pt,_1pG],[1,[0,_1ps,_1pI],_9]]));});return !E(_1pJ)?E(_1pM):B(_1pB(_1pM,_1pw,_9));}),_1pN=E(_1pK);return _1pN[0]==0?E(_1pL):B(_1pB(_1pL,[0,_1pu,_1pN[1]],_9));},_1pO=new T(function(){return B(unCStr("href"));}),_1pP=[0,97],_1pQ=[1,_1pP,_9],_1pR=function(_1pS,_){return new F(function(){return _1nG(_1pQ,_1pS,_);});},_1pT=function(_1pU,_1pV){return function(_1pW,_){var _1pX=B(A(new T(function(){return B(_1pB(_1pR,[0,_1pO,_1pU],_9));}),[_1pW,_])),_1pY=_1pX,_1pZ=B(A(_1pV,[_1pY,_])),_1q0=_1pZ;return _1pY;};},_1q1=function(_1q2){return new F(function(){return _1pT(_1q2,function(_1pr,_){return new F(function(){return _6v(_1q2,_1pr,_);});});});},_1q3=new T(function(){return B(unCStr("option"));}),_1q4=function(_1q5,_){return new F(function(){return _1nG(_1q3,_1q5,_);});},_1q6=new T(function(){return B(unCStr("selected"));}),_1q7=[0,_1q6,_9],_1q8=function(_1q9,_1qa,_1qb){var _1qc=new T(function(){return B(_1pB(_1q4,[0,_1ps,_1q9],_9));});if(!E(_1qb)){return function(_1qd,_){var _1qe=B(A(_1qc,[_1qd,_])),_1qf=_1qe,_1qg=B(A(_1qa,[_1qf,_])),_1qh=_1qg;return _1qf;};}else{return new F(function(){return _1pB(function(_1qi,_){var _1qj=B(A(_1qc,[_1qi,_])),_1qk=_1qj,_1ql=B(A(_1qa,[_1qk,_])),_1qm=_1ql;return _1qk;},_1q7,_9);});}},_1qn=function(_1qo,_1qp){return new F(function(){return _1q8(_1qo,function(_1pr,_){return new F(function(){return _6v(_1qo,_1pr,_);});},_1qp);});},_1qq=new T(function(){return B(unCStr("method"));}),_1qr=new T(function(){return B(unCStr("action"));}),_1qs=new T(function(){return B(unCStr("UTF-8"));}),_1qt=new T(function(){return B(unCStr("acceptCharset"));}),_1qu=[0,_1qt,_1qs],_1qv=new T(function(){return B(unCStr("form"));}),_1qw=function(_1qx,_){return new F(function(){return _1nG(_1qv,_1qx,_);});},_1qy=function(_1qz,_1qA,_1qB){return function(_1qC,_){var _1qD=B(A(new T(function(){return B(_1pB(_1qw,_1qu,[1,[0,_1qr,_1qz],[1,[0,_1qq,_1qA],_9]]));}),[_1qC,_])),_1qE=_1qD,_1qF=B(A(_1qB,[_1qE,_])),_1qG=_1qF;return _1qE;};},_1qH=new T(function(){return B(unCStr("select"));}),_1qI=function(_1qJ,_){return new F(function(){return _1nG(_1qH,_1qJ,_);});},_1qK=function(_1qL,_1qM){return function(_1qN,_){var _1qO=B(A(new T(function(){return B(_1pB(_1qI,[0,_1pt,_1qL],_9));}),[_1qN,_])),_1qP=_1qO,_1qQ=B(A(_1qM,[_1qP,_])),_1qR=_1qQ;return _1qP;};},_1qS=new T(function(){return B(unCStr("textarea"));}),_1qT=function(_1qU,_){return new F(function(){return _1nG(_1qS,_1qU,_);});},_1qV=function(_1qW,_1qX){return function(_1qY,_){var _1qZ=B(A(new T(function(){return B(_1pB(_1qT,[0,_1pt,_1qW],_9));}),[_1qY,_])),_1r0=_1qZ,_1r1=B(_6v(_1qX,_1r0,_)),_1r2=_1r1;return _1r0;};},_1r3=new T(function(){return B(unCStr("color:red"));}),_1r4=new T(function(){return B(unCStr("style"));}),_1r5=[0,_1r4,_1r3],_1r6=[0,98],_1r7=[1,_1r6,_9],_1r8=function(_1r9){return new F(function(){return _1pB(function(_1ra,_){var _1rb=B(_1nG(_1r7,_1ra,_)),_1rc=_1rb,_1rd=B(A(_1r9,[_1rc,_])),_1re=_1rd;return _1rc;},_1r5,_9);});},_1rf=function(_1rg,_1rh,_){var _1ri=E(_1rg);if(!_1ri[0]){return _1rh;}else{var _1rj=B(A(_1ri[1],[_1rh,_])),_1rk=_1rj,_1rl=B(_1rf(_1ri[2],_1rh,_)),_1rm=_1rl;return _1rh;}},_1rn=function(_1ro,_1rp,_){return new F(function(){return _1rf(_1ro,_1rp,_);});},_1rq=function(_1rr,_1rs,_1rt,_){var _1ru=B(A(_1rr,[_1rt,_])),_1rv=_1ru,_1rw=B(A(_1rs,[_1rt,_])),_1rx=_1rw;return _1rt;},_1ry=[0,_6S,_1rq,_1rn],_1rz=[0,_1ry,_1pa,_6v,_6v,_1nM,_1r8,_1pT,_1q1,_1pF,_1qV,_1qK,_1q8,_1qn,_1qy,_1pk],_1rA=function(_1rB,_1rC,_){var _1rD=B(A(_1rC,[_])),_1rE=_1rD;return _1rB;},_1rF=function(_1rG,_1rH,_){var _1rI=B(A(_1rH,[_])),_1rJ=_1rI;return new T(function(){return B(A(_1rG,[_1rJ]));});},_1rK=[0,_1rF,_1rA],_1rL=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1rM=new T(function(){return B(unCStr("base"));}),_1rN=new T(function(){return B(unCStr("IOException"));}),_1rO=new T(function(){var _1rP=hs_wordToWord64(4053623282),_1rQ=_1rP,_1rR=hs_wordToWord64(3693590983),_1rS=_1rR;return [0,_1rQ,_1rS,[0,_1rQ,_1rS,_1rM,_1rL,_1rN],_9];}),_1rT=function(_1rU){return E(_1rO);},_1rV=function(_1rW){var _1rX=E(_1rW);return new F(function(){return _1I(B(_1G(_1rX[1])),_1rT,_1rX[2]);});},_1rY=new T(function(){return B(unCStr(": "));}),_1rZ=[0,41],_1s0=new T(function(){return B(unCStr(" ("));}),_1s1=new T(function(){return B(unCStr("already exists"));}),_1s2=new T(function(){return B(unCStr("does not exist"));}),_1s3=new T(function(){return B(unCStr("protocol error"));}),_1s4=new T(function(){return B(unCStr("failed"));}),_1s5=new T(function(){return B(unCStr("invalid argument"));}),_1s6=new T(function(){return B(unCStr("inappropriate type"));}),_1s7=new T(function(){return B(unCStr("hardware fault"));}),_1s8=new T(function(){return B(unCStr("unsupported operation"));}),_1s9=new T(function(){return B(unCStr("timeout"));}),_1sa=new T(function(){return B(unCStr("resource vanished"));}),_1sb=new T(function(){return B(unCStr("interrupted"));}),_1sc=new T(function(){return B(unCStr("resource busy"));}),_1sd=new T(function(){return B(unCStr("resource exhausted"));}),_1se=new T(function(){return B(unCStr("end of file"));}),_1sf=new T(function(){return B(unCStr("illegal operation"));}),_1sg=new T(function(){return B(unCStr("permission denied"));}),_1sh=new T(function(){return B(unCStr("user error"));}),_1si=new T(function(){return B(unCStr("unsatisified constraints"));}),_1sj=new T(function(){return B(unCStr("system error"));}),_1sk=function(_1sl,_1sm){switch(E(_1sl)){case 0:return new F(function(){return _e(_1s1,_1sm);});break;case 1:return new F(function(){return _e(_1s2,_1sm);});break;case 2:return new F(function(){return _e(_1sc,_1sm);});break;case 3:return new F(function(){return _e(_1sd,_1sm);});break;case 4:return new F(function(){return _e(_1se,_1sm);});break;case 5:return new F(function(){return _e(_1sf,_1sm);});break;case 6:return new F(function(){return _e(_1sg,_1sm);});break;case 7:return new F(function(){return _e(_1sh,_1sm);});break;case 8:return new F(function(){return _e(_1si,_1sm);});break;case 9:return new F(function(){return _e(_1sj,_1sm);});break;case 10:return new F(function(){return _e(_1s3,_1sm);});break;case 11:return new F(function(){return _e(_1s4,_1sm);});break;case 12:return new F(function(){return _e(_1s5,_1sm);});break;case 13:return new F(function(){return _e(_1s6,_1sm);});break;case 14:return new F(function(){return _e(_1s7,_1sm);});break;case 15:return new F(function(){return _e(_1s8,_1sm);});break;case 16:return new F(function(){return _e(_1s9,_1sm);});break;case 17:return new F(function(){return _e(_1sa,_1sm);});break;default:return new F(function(){return _e(_1sb,_1sm);});}},_1sn=[0,125],_1so=new T(function(){return B(unCStr("{handle: "));}),_1sp=function(_1sq,_1sr,_1ss,_1st,_1su,_1sv){var _1sw=new T(function(){var _1sx=new T(function(){return B(_1sk(_1sr,new T(function(){var _1sy=E(_1st);return _1sy[0]==0?E(_1sv):B(_e(_1s0,new T(function(){return B(_e(_1sy,[1,_1rZ,_1sv]));},1)));},1)));},1),_1sz=E(_1ss);return _1sz[0]==0?E(_1sx):B(_e(_1sz,new T(function(){return B(_e(_1rY,_1sx));},1)));},1),_1sA=E(_1su);if(!_1sA[0]){var _1sB=E(_1sq);if(!_1sB[0]){return E(_1sw);}else{var _1sC=E(_1sB[1]);return _1sC[0]==0?B(_e(_1so,new T(function(){return B(_e(_1sC[1],[1,_1sn,new T(function(){return B(_e(_1rY,_1sw));})]));},1))):B(_e(_1so,new T(function(){return B(_e(_1sC[1],[1,_1sn,new T(function(){return B(_e(_1rY,_1sw));})]));},1)));}}else{return new F(function(){return _e(_1sA[1],new T(function(){return B(_e(_1rY,_1sw));},1));});}},_1sD=function(_1sE){var _1sF=E(_1sE);return new F(function(){return _1sp(_1sF[1],_1sF[2],_1sF[3],_1sF[4],_1sF[6],_9);});},_1sG=function(_1sH,_1sI){var _1sJ=E(_1sH);return new F(function(){return _1sp(_1sJ[1],_1sJ[2],_1sJ[3],_1sJ[4],_1sJ[6],_1sI);});},_1sK=function(_1sL,_1sM){return new F(function(){return _23(_1sG,_1sL,_1sM);});},_1sN=function(_1sO,_1sP,_1sQ){var _1sR=E(_1sP);return new F(function(){return _1sp(_1sR[1],_1sR[2],_1sR[3],_1sR[4],_1sR[6],_1sQ);});},_1sS=[0,_1sN,_1sD,_1sK],_1sT=new T(function(){return [0,_1rT,_1sS,_1sU,_1rV];}),_1sU=function(_1sV){return [0,_1sT,_1sV];},_1sW=7,_1sX=function(_1sY){return [0,_4O,_1sW,_9,_1sY,_4O,_4O];},_1sZ=function(_1t0,_){return new F(function(){return die(new T(function(){return B(_1sU(new T(function(){return B(_1sX(_1t0));})));}));});},_1t1=function(_1t2,_){return new F(function(){return _1sZ(_1t2,_);});},_1t3=function(_1t4,_){return new F(function(){return _1t1(_1t4,_);});},_1t5=function(_1t6,_){return new F(function(){return _1t3(_1t6,_);});},_1t7=function(_1t8,_1t9,_){var _1ta=B(A(_1t8,[_])),_1tb=_1ta;return new F(function(){return A(_1t9,[_1tb,_]);});},_1tc=function(_1td,_1te,_){var _1tf=B(A(_1td,[_])),_1tg=_1tf;return new F(function(){return A(_1te,[_]);});},_1th=[0,_1t7,_1tc,_6S,_1t5],_1ti=[0,_1th,_6P],_1tj=function(_1tk){return E(E(_1tk)[1]);},_1tl=function(_1tm){return E(E(_1tm)[2]);},_1tn=function(_1to,_1tp){var _1tq=new T(function(){return B(_1tj(_1to));});return function(_1tr){return new F(function(){return A(new T(function(){return B(_NO(_1tq));}),[new T(function(){return B(A(_1tl,[_1to,_1tp]));}),function(_1ts){return new F(function(){return A(new T(function(){return B(_iZ(_1tq));}),[[0,_1ts,_1tr]]);});}]);});};},_1tt=function(_1tu,_1tv){return [0,_1tu,function(_1tw){return new F(function(){return _1tn(_1tv,_1tw);});}];},_1tx=function(_1ty,_1tz,_1tA,_1tB){return new F(function(){return A(_NO,[_1ty,new T(function(){return B(A(_1tz,[_1tB]));}),function(_1tC){return new F(function(){return A(_1tA,[new T(function(){return E(E(_1tC)[1]);}),new T(function(){return E(E(_1tC)[2]);})]);});}]);});},_1tD=function(_1tE,_1tF,_1tG,_1tH){return new F(function(){return A(_NO,[_1tE,new T(function(){return B(A(_1tF,[_1tH]));}),function(_1tI){return new F(function(){return A(_1tG,[new T(function(){return E(E(_1tI)[2]);})]);});}]);});},_1tJ=function(_1tK,_1tL,_1tM,_1tN){return new F(function(){return _1tD(_1tK,_1tL,_1tM,_1tN);});},_1tO=function(_1tP){return E(E(_1tP)[4]);},_1tQ=function(_1tR,_1tS){return function(_1tT){return E(new T(function(){return B(A(_1tO,[_1tR,_1tS]));}));};},_1tU=function(_1tV){return [0,function(_1tL,_1tM,_1tN){return new F(function(){return _1tx(_1tV,_1tL,_1tM,_1tN);});},function(_1tL,_1tM,_1tN){return new F(function(){return _1tJ(_1tV,_1tL,_1tM,_1tN);});},function(_1tW,_1tX){return new F(function(){return A(new T(function(){return B(_iZ(_1tV));}),[[0,_1tW,_1tX]]);});},function(_1tN){return new F(function(){return _1tQ(_1tV,_1tN);});}];},_1tY=function(_1tZ,_1u0,_1u1){return new F(function(){return A(_iZ,[_1tZ,[0,_1u0,_1u1]]);});},_1u2=[0,10],_1u3=function(_1u4,_1u5){var _1u6=E(_1u5);if(!_1u6[0]){return E(_6P);}else{var _1u7=_1u6[1],_1u8=E(_1u6[2]);if(!_1u8[0]){var _1u9=E(_1u7);return new F(function(){return _1ua(_1u2,_1u9[3],_1u9[4]);});}else{return function(_1ub){return new F(function(){return A(new T(function(){var _1uc=E(_1u7);return B(_1ua(_1u2,_1uc[3],_1uc[4]));}),[new T(function(){return B(A(_1u4,[new T(function(){return B(A(new T(function(){return B(_1u3(_1u4,_1u8));}),[_1ub]));})]));})]);});};}}},_1ud=new T(function(){return B(unCStr("(->)"));}),_1ue=new T(function(){return B(unCStr("GHC.Prim"));}),_1uf=new T(function(){var _1ug=hs_wordToWord64(4173248105),_1uh=_1ug,_1ui=hs_wordToWord64(4270398258),_1uj=_1ui;return [0,_1uh,_1uj,[0,_1uh,_1uj,_1nW,_1ue,_1ud],_9];}),_1uk=new T(function(){return E(E(_1uf)[3]);}),_1ul=new T(function(){return B(unCStr("GHC.Types"));}),_1um=new T(function(){return B(unCStr("[]"));}),_1un=new T(function(){var _1uo=hs_wordToWord64(4033920485),_1up=_1uo,_1uq=hs_wordToWord64(786266835),_1ur=_1uq;return [0,_1up,_1ur,[0,_1up,_1ur,_1nW,_1ul,_1um],_9];}),_1us=[1,_1nX,_9],_1ut=function(_1uu){var _1uv=E(_1uu);if(!_1uv[0]){return [0];}else{var _1uw=E(_1uv[1]);return [1,[0,_1uw[1],_1uw[2]],new T(function(){return B(_1ut(_1uv[2]));})];}},_1ux=new T(function(){var _1uy=E(_1un),_1uz=E(_1uy[3]),_1uA=B(_e(_1uy[4],_1us));if(!_1uA[0]){var _1uB=E(_1uz);}else{var _1uC=B(_1or(new T(function(){return B(_8Q(B(_3d(_1oU,[1,[0,_1uz[1],_1uz[2]],new T(function(){return B(_1ut(_1uA));})]))));},1))),_1uB=E(_1uz);}var _1uD=_1uB,_1uE=_1uD;return _1uE;}),_1uF=[0,8],_1uG=[0,32],_1uH=function(_1uI){return [1,_1uG,_1uI];},_1uJ=new T(function(){return B(unCStr(" -> "));}),_1uK=[0,9],_1uL=[0,93],_1uM=[0,91],_1uN=[0,41],_1uO=[0,44],_1uP=function(_1uI){return [1,_1uO,_1uI];},_1uQ=[0,40],_1uR=[0,0],_1ua=function(_1uS,_1uT,_1uU){var _1uV=E(_1uU);if(!_1uV[0]){return function(_1uW){return new F(function(){return _e(E(_1uT)[5],_1uW);});};}else{var _1uX=_1uV[1],_1uY=function(_1uZ){var _1v0=E(_1uT)[5],_1v1=function(_1v2){var _1v3=new T(function(){return B(_1u3(_1uH,_1uV));});return E(_1uS)[1]<=9?function(_1v4){return new F(function(){return _e(_1v0,[1,_1uG,new T(function(){return B(A(_1v3,[_1v4]));})]);});}:function(_1v5){return [1,_E,new T(function(){return B(_e(_1v0,[1,_1uG,new T(function(){return B(A(_1v3,[[1,_D,_1v5]]));})]));})];};},_1v6=E(_1v0);if(!_1v6[0]){return new F(function(){return _1v1(_);});}else{if(E(E(_1v6[1])[1])==40){var _1v7=E(_1v6[2]);if(!_1v7[0]){return new F(function(){return _1v1(_);});}else{if(E(E(_1v7[1])[1])==44){return function(_1v8){return [1,_1uQ,new T(function(){return B(A(new T(function(){return B(_1u3(_1uP,_1uV));}),[[1,_1uN,_1v8]]));})];};}else{return new F(function(){return _1v1(_);});}}}else{return new F(function(){return _1v1(_);});}}},_1v9=E(_1uV[2]);if(!_1v9[0]){var _1va=E(_1uT),_1vb=E(_1ux),_1vc=hs_eqWord64(_1va[1],_1vb[1]),_1vd=_1vc;if(!E(_1vd)){return new F(function(){return _1uY(_);});}else{var _1ve=hs_eqWord64(_1va[2],_1vb[2]),_1vf=_1ve;if(!E(_1vf)){return new F(function(){return _1uY(_);});}else{return function(_1vg){return [1,_1uM,new T(function(){return B(A(new T(function(){var _1vh=E(_1uX);return B(_1ua(_1uR,_1vh[3],_1vh[4]));}),[[1,_1uL,_1vg]]));})];};}}}else{if(!E(_1v9[2])[0]){var _1vi=E(_1uT),_1vj=E(_1uk),_1vk=hs_eqWord64(_1vi[1],_1vj[1]),_1vl=_1vk;if(!E(_1vl)){return new F(function(){return _1uY(_);});}else{var _1vm=hs_eqWord64(_1vi[2],_1vj[2]),_1vn=_1vm;if(!E(_1vn)){return new F(function(){return _1uY(_);});}else{var _1vo=new T(function(){var _1vp=E(_1v9[1]);return B(_1ua(_1uF,_1vp[3],_1vp[4]));}),_1vq=new T(function(){var _1vr=E(_1uX);return B(_1ua(_1uK,_1vr[3],_1vr[4]));});return E(_1uS)[1]<=8?function(_1vs){return new F(function(){return A(_1vq,[new T(function(){return B(_e(_1uJ,new T(function(){return B(A(_1vo,[_1vs]));},1)));})]);});}:function(_1vt){return [1,_E,new T(function(){return B(A(_1vq,[new T(function(){return B(_e(_1uJ,new T(function(){return B(A(_1vo,[[1,_D,_1vt]]));},1)));})]));})];};}}}else{return new F(function(){return _1uY(_);});}}}},_1vu=function(_1vv,_1vw){return new F(function(){return A(_1vv,[function(_){return new F(function(){return jsFind(toJSStr(E(_1vw)));});}]);});},_1vx=[0],_1vy=function(_1vz){return E(E(_1vz)[3]);},_1vA=new T(function(){return [0,"value"];}),_1vB=function(_1vC){return E(E(_1vC)[6]);},_1vD=function(_1vE){return E(E(_1vE)[1]);},_1vF=new T(function(){return B(unCStr("Char"));}),_1vG=new T(function(){var _1vH=hs_wordToWord64(3763641161),_1vI=_1vH,_1vJ=hs_wordToWord64(1343745632),_1vK=_1vJ;return [0,_1vI,_1vK,[0,_1vI,_1vK,_1nW,_1ul,_1vF],_9];}),_1vL=function(_1vM){return E(_1vG);},_1vN=function(_1vO){return E(_1un);},_1vP=new T(function(){return B(_1oX(_1vN,_1vL));}),_1vQ=new T(function(){return B(A(_1vP,[_]));}),_1vR=function(_1vS,_1vT,_1vU,_1vV,_1vW,_1vX,_1vY,_1vZ,_1w0){var _1w1=new T(function(){return B(A(_1vV,[_1vx]));});return new F(function(){return A(_1vT,[new T(function(){return B(_1vu(E(_1vS)[2],_1w0));}),function(_1w2){var _1w3=E(_1w2);return _1w3[0]==0?E(_1w1):B(A(_1vT,[new T(function(){return B(A(E(_1vS)[2],[function(_){var _1w4=jsGet(E(_1w3[1])[1],E(_1vA)[1]),_1w5=_1w4;return [1,new T(function(){return fromJSStr(_1w5);})];}]));}),function(_1w6){var _1w7=E(_1w6);if(!_1w7[0]){return E(_1w1);}else{var _1w8=_1w7[1];if(!E(new T(function(){var _1w9=B(A(_1vX,[_])),_1wa=E(_1vQ),_1wb=hs_eqWord64(_1w9[1],_1wa[1]),_1wc=_1wb;if(!E(_1wc)){var _1wd=false;}else{var _1we=hs_eqWord64(_1w9[2],_1wa[2]),_1wf=_1we,_1wd=E(_1wf)==0?false:true;}var _1wg=_1wd,_1wh=_1wg;return _1wh;}))){var _1wi=function(_1wj){return new F(function(){return A(_1vV,[[1,_1w8,new T(function(){return B(A(new T(function(){return B(_1vB(_1vZ));}),[new T(function(){return B(A(new T(function(){return B(_1vy(_1vZ));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1w8,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1wk=B(A(_1vX,[_]));return B(A(_1ua,[_1uR,_1wk[3],_1wk[4],_9]));})));})));})));})]));})]));})]]);});},_1wl=B(A(new T(function(){return B(A(_1vD,[_1vY,_4x]));}),[_1w8]));if(!_1wl[0]){return new F(function(){return _1wi(_);});}else{var _1wm=E(_1wl[1]);return E(_1wm[2])[0]==0?E(_1wl[2])[0]==0?B(A(_1vV,[[2,_1wm[1]]])):B(_1wi(_)):B(_1wi(_));}}else{return new F(function(){return A(_1vV,[[2,_1w8]]);});}}}]));}]);});},_1wn=function(_1wo){return E(E(_1wo)[10]);},_1wp=function(_1wq){return new F(function(){return _l1([1,function(_1wr){return new F(function(){return A(_sC,[_1wr,function(_1ws){return E(new T(function(){return B(_tS(function(_1wt){var _1wu=E(_1wt);return _1wu[0]==0?B(A(_1wq,[_1wu[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_ue(_1wv,_1wq))];}));});},_1wv=function(_1ww,_1wx){return new F(function(){return _1wp(_1wx);});},_1wy=[0,91],_1wz=[1,_1wy,_9],_1wA=function(_1wB,_1wC){var _1wD=function(_1wE,_1wF){return [1,function(_1wG){return new F(function(){return A(_sC,[_1wG,function(_1wH){return E(new T(function(){return B(_tS(function(_1wI){var _1wJ=E(_1wI);if(_1wJ[0]==2){var _1wK=E(_1wJ[1]);if(!_1wK[0]){return [2];}else{var _1wL=_1wK[2];switch(E(E(_1wK[1])[1])){case 44:return E(_1wL)[0]==0?!E(_1wE)?[2]:E(new T(function(){return B(A(_1wB,[_ud,function(_1wM){return new F(function(){return _1wD(_o9,function(_1wN){return new F(function(){return A(_1wF,[[1,_1wM,_1wN]]);});});});}]));})):[2];case 93:return E(_1wL)[0]==0?E(new T(function(){return B(A(_1wF,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1wO=function(_1wP){return new F(function(){return _l1([1,function(_1wQ){return new F(function(){return A(_sC,[_1wQ,function(_1wR){return E(new T(function(){return B(_tS(function(_1wS){var _1wT=E(_1wS);return _1wT[0]==2?!B(_3x(_1wT[1],_1wz))?[2]:E(new T(function(){return B(_l1(B(_1wD(_4y,_1wP)),new T(function(){return B(A(_1wB,[_ud,function(_1wU){return new F(function(){return _1wD(_o9,function(_1wV){return new F(function(){return A(_1wP,[[1,_1wU,_1wV]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_ue(function(_1wW,_1wX){return new F(function(){return _1wO(_1wX);});},_1wP))];}));});};return new F(function(){return _1wO(_1wC);});},_1wY=function(_1wZ){return new F(function(){return _l1(B(_l1([1,function(_1x0){return new F(function(){return A(_sC,[_1x0,function(_1x1){return E(new T(function(){return B(_tS(function(_1x2){var _1x3=E(_1x2);return _1x3[0]==1?B(A(_1wZ,[_1x3[1]])):[2];}));}));}]);});}],new T(function(){return B(_1wA(_1wv,_1wZ));}))),new T(function(){return [1,B(_ue(_1x4,_1wZ))];}));});},_1x4=function(_1x5,_1x6){return new F(function(){return _1wY(_1x6);});},_1x7=new T(function(){return B(_1wY(_lK));}),_1x8=function(_1x9){return new F(function(){return _kR(_1x7,_1x9);});},_1xa=new T(function(){return B(_1wp(_lK));}),_1xb=function(_1x9){return new F(function(){return _kR(_1xa,_1x9);});},_1xc=function(_1xd){return E(_1xb);},_1xe=[0,_1xc,_1x8,_1wv,_1x4],_1xf=function(_1xg){return E(E(_1xg)[4]);},_1xh=function(_1xi,_1xj,_1xk){return new F(function(){return _1wA(new T(function(){return B(_1xf(_1xi));}),_1xk);});},_1xl=function(_1xm){return function(_ma){return new F(function(){return _kR(new T(function(){return B(_1wA(new T(function(){return B(_1xf(_1xm));}),_lK));}),_ma);});};},_1xn=function(_1xo,_1xp){return function(_ma){return new F(function(){return _kR(new T(function(){return B(A(_1xf,[_1xo,_1xp,_lK]));}),_ma);});};},_1xq=function(_1xr){return [0,function(_1x9){return new F(function(){return _1xn(_1xr,_1x9);});},new T(function(){return B(_1xl(_1xr));}),new T(function(){return B(_1xf(_1xr));}),function(_1xs,_1x9){return new F(function(){return _1xh(_1xr,_1xs,_1x9);});}];},_1xt=new T(function(){return B(_1xq(_1xe));}),_1xu=function(_1xv,_1xw,_1xx){var _1xy=new T(function(){return B(_1wn(_1xv));}),_1xz=new T(function(){return B(_1tj(_1xx));}),_1xA=new T(function(){return B(_iZ(_1xz));});return function(_1xB,_1xC){return new F(function(){return A(new T(function(){return B(_NO(_1xz));}),[new T(function(){return B(A(new T(function(){return B(_NO(_1xz));}),[new T(function(){return B(A(new T(function(){return B(_iZ(_1xz));}),[[0,_1xC,_1xC]]));}),function(_1xD){var _1xE=new T(function(){return E(E(_1xD)[1]);}),_1xF=new T(function(){return E(E(_1xE)[2]);});return new F(function(){return A(new T(function(){return B(_NO(_1xz));}),[new T(function(){return B(A(new T(function(){return B(_iZ(_1xz));}),[[0,_6B,new T(function(){var _1xG=E(_1xE);return [0,_1xG[1],new T(function(){return [0,E(_1xF)[1]+1|0];}),_1xG[3],_1xG[4],_1xG[5],_1xG[6],_1xG[7]];})]]));}),function(_1xH){return new F(function(){return A(new T(function(){return B(_iZ(_1xz));}),[[0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_1xF)[1],_9)),new T(function(){return E(E(_1xE)[1]);},1)));})],new T(function(){return E(E(_1xH)[2]);})]]);});}]);});}]));}),function(_1xI){var _1xJ=new T(function(){return E(E(_1xI)[1]);});return new F(function(){return A(new T(function(){return B(_NO(_1xz));}),[new T(function(){return B(A(_1vR,[new T(function(){return B(_1tt(new T(function(){return B(_1tU(_1xz));}),_1xx));}),function(_1xK,_1pr,_1xL){return new F(function(){return _1tx(_1xz,_1xK,_1pr,_1xL);});},function(_1xK,_1pr,_1xL){return new F(function(){return _1tJ(_1xz,_1xK,_1pr,_1xL);});},function(_1pr,_1xL){return new F(function(){return _1tY(_1xz,_1pr,_1xL);});},function(_1xL){return new F(function(){return _1tQ(_1xz,_1xL);});},_1vP,_1xt,_1xv,_1xJ,new T(function(){return E(E(_1xI)[2]);})]));}),function(_1xM){var _1xN=E(_1xM),_1xO=_1xN[2],_1xP=E(_1xN[1]);switch(_1xP[0]){case 0:return new F(function(){return A(_1xA,[[0,[0,new T(function(){return B(A(_1xy,[_1xJ,_1xB]));}),_4O],_1xO]]);});break;case 1:return new F(function(){return A(_1xA,[[0,[0,new T(function(){return B(A(_1xy,[_1xJ,_1xP[1]]));}),_4O],_1xO]]);});break;default:var _1xQ=_1xP[1];return new F(function(){return A(_1xA,[[0,[0,new T(function(){return B(A(_1xy,[_1xJ,_1xQ]));}),[1,_1xQ]],_1xO]]);});}}]);});}]);});};},_1xR=new T(function(){return B(_1xu(_1rz,_1rK,_1ti));}),_1xS=new T(function(){return B(_Ci("w_s8Az{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv a7Kn} [tv]"));}),_1xT=new T(function(){return B(_Ci("w_s8AA{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv a7Km} [tv]"));}),_1xU=function(_1xV){return E(E(_1xV)[2]);},_1xW=function(_1xX){return E(E(_1xX)[1]);},_1xY=function(_1xZ,_1y0,_1y1){return function(_1y2,_){var _1y3=B(A(_1y0,[_1y2,_])),_1y4=_1y3,_1y5=E(_1y4),_1y6=E(_1y5[1]),_1y7=new T(function(){return B(A(new T(function(){return B(_1xU(_1xZ));}),[_1y1,function(_){var _1y8=E(E(_1y2)[4]),_1y9=B(A(_1y8[1],[_])),_1ya=_1y9,_1yb=E(_1ya);if(!_1yb[0]){return _6B;}else{var _1yc=B(A(_1y8[2],[_1yb[1],_])),_1yd=_1yc;return _6B;}}]));});return [0,[0,function(_1ye,_){var _1yf=B(A(_1y6[1],[_1ye,_])),_1yg=_1yf,_1yh=E(_1yg),_1yi=E(_1y7),_1yj=jsSetCB(_1yh[1],toJSStr(E(new T(function(){return B(A(_1xW,[_1xZ,_1y1]));}))),_1y7),_1yk=_1yj;return _1yh;},_1y6[2]],_1y5[2]];};},_1yl=function(_1ym,_1yn,_1yo,_1yp,_1yq,_1yr,_1ys,_1yt,_1yu,_1yv,_1yw){return function(_1yx,_1yy){return function(_ma,_19i){return new F(function(){return _7u(function(_1yz,_){var _1yA=B(A(new T(function(){return B(_1xY(_6u,new T(function(){return B(_1xY(_6u,new T(function(){return B(A(_1xR,[_1yy]));}),_1p));}),_1o));}),[_1yz,_])),_1yB=_1yA,_1yC=E(_1yB),_1yD=E(_1yC[1]);return [0,[0,function(_1yE,_){var _1yF=B(A(_1yD[1],[_1yE,_])),_1yG=_1yF,_1yH=B(A(_6C,[_6P,_1yG,_cn,_c2,_])),_1yI=_1yH;return _1yG;},_1yD[2]],_1yC[2]];},function(_1yJ){var _1yK=new T(function(){var _1yL=B(_Dq(_Cm,_DM,[0,new T(function(){return B(_e(_1yJ,_1nF));}),E(_Cf),E(_6B)]));if(!_1yL[0]){var _1yM=E(_1yL[1]);if(!_1yM[0]){var _1yN=E(E(_1yM[1])[1]);}else{var _1yN=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1yM[1]));})));})],_9],_9];}var _1yO=_1yN;}else{var _1yP=E(_1yL[1]);if(!_1yP[0]){var _1yQ=E(E(_1yP[1])[1]);}else{var _1yQ=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1yP[1]));})));})],_9],_9];}var _1yO=_1yQ;}return _1yO;});return function(_ma,_19i){return new F(function(){return _7u(_c9,function(_1yR,_1yS,_){return new F(function(){return _7u(_cf,function(_1yT,_1yU,_){return new F(function(){return _7u(_ck,function(_1yV,_1yW,_){return new F(function(){return _7u(function(_1yX,_){return [0,[0,function(_1yY,_){var _1yZ=B(_1ii(_6v,_9,_1yY,_)),_1z0=_1yZ,_1z1=B(A(_6C,[_6P,_1z0,_6O,_1yR,_])),_1z2=_1z1,_1z3=B(A(_6C,[_6P,_1z0,_cn,_cl,_])),_1z4=_1z3;return _1z0;},_cr],_1yX];},function(_1z5,_1z6,_){return new F(function(){return _7u(function(_1z7,_){return [0,[0,function(_1z8,_){var _1z9=B(_7i(_7s,new T(function(){return B(_1na(_1yK));}),_1z8,_)),_1za=_1z9,_1zb=B(A(_6C,[_6P,_1za,_6O,_1yT,_])),_1zc=_1zb,_1zd=B(A(_6C,[_6P,_1za,_cn,_cm,_])),_1ze=_1zd;return _1za;},_cr],_1z7];},function(_1zf){return E(new T(function(){var _1zg=E(new T(function(){var _1zh=B(_1ln(_1yK,new T(function(){return E(E(_1yx)[1]);})));return _1zh[0]==0?[0,_1zh[1]]:[1,new T(function(){return B(_1i0(_1ym,_1yn,_1yo,_1yp,_1yq,_1yr,_1ys,_1yt,_1yu,_1xS,_1xT,_1yv,_1yw,new T(function(){return E(E(_1yx)[2]);}),_1zh[1]));})];}));if(!_1zg[0]){var _1zi=function(_1zj,_){return [0,[0,function(_1zk,_){var _1zl=B(_1ii(_7s,new T(function(){return B(_1nw(B(_dq(_1zg[1],_9))));}),_1zk,_)),_1zm=_1zl,_1zn=B(A(_6C,[_6P,_1zm,_6O,_1yV,_])),_1zo=_1zn,_1zp=B(A(_6C,[_6P,_1zm,_cn,_co,_])),_1zq=_1zp;return _1zm;},_cr],_1zj];};}else{var _1zr=E(_1zg[1]);if(!_1zr[0]){var _1zs=function(_ca,_){return new F(function(){return _cw(_1yR,_c1,_ct,_ca,_);});};}else{var _1zs=function(_ma,_19i){return new F(function(){return _cw(_1yR,_c1,function(_1zt,_){return [0,[0,function(_ca,_){return new F(function(){return _7i(_6v,new T(function(){var _1zu=E(_1zr[1]);return B(_bV(new T(function(){return B(_bI(_1ys,_1yr,_1yq,_1yp,_1yo,_1ym,_1yn));}),new T(function(){return B(_3W(_1ys,_1yr,_1yq,_1yp,_1yo,_1ym,_1yn));}),_1zu[1],_1zu[2]));}),_ca,_);});},_cr],_1zt];},_ma,_19i);});};}var _1zi=_1zs;}return _1zi;}));},_1z6,_);});},_1yW,_);});},_1yU,_);});},_1yS,_);});},_ma,_19i);});};},_ma,_19i);});};};},_1zv=function(_1zw,_1zx,_1zy,_1zz){return new F(function(){return A(_1zw,[function(_){var _1zA=jsSet(E(_1zx)[1],toJSStr(E(_1zy)),toJSStr(E(_1zz)));return _6B;}]);});},_1zB=new T(function(){return B(unCStr("innerHTML"));}),_1zC=new T(function(){return B(unCStr("textContent"));}),_1zD=function(_1zE,_1zF,_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM,_1zN,_1zO,_1zP,_1zQ,_){var _1zR=B(_1j(_1zQ,_1zC,_)),_1zS=_1zR,_1zT=[0,_1zQ],_1zU=B(A(_1zv,[_6P,_1zT,_1zB,_9,_])),_1zV=_1zU,_1zW=E(_51)[1],_1zX=takeMVar(_1zW),_1zY=_1zX,_1zZ=B(A(_1yl,[_1zE,_1zF,_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM,_1zN,_1zO,_1zP,_1zS,_1zY,_])),_1A0=_1zZ,_1A1=E(_1A0),_1A2=E(_1A1[1]),_=putMVar(_1zW,_1A1[2]),_1A3=B(A(_1A2[1],[_1zT,_])),_1A4=_1A3;return _1A2[2];},_1A5=function(_){var _1A6=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1A7=_1A6;return _6B;},_1A8=new T(function(){return B(unCStr("embedding complete"));}),_1A9=new T(function(){return B(unCStr("proofbox"));}),_1Aa=function(_1Ab,_1Ac,_1Ad,_1Ae,_1Af,_1Ag,_1Ah,_1Ai,_1Aj,_1Ak,_1Al,_1Am,_){var _1An=jsElemsByClassName(toJSStr(E(_1A9))),_1Ao=_1An,_1Ap=B((function(_1Aq,_){while(1){var _1Ar=E(_1Aq);if(!_1Ar[0]){return _6B;}else{var _1As=B(_1zD(_1Ab,_1Ac,_1Ad,_1Ae,_1Af,_1Ag,_1Ah,_1Ai,_1Aj,_1Ak,_1Al,_1Am,E(_1Ar[1])[1],_)),_1At=_1As;_1Aq=_1Ar[2];continue;}}})(_1Ao,_)),_1Au=_1Ap,_1Av=jsLog(toJSStr(E(_1A8))),_1Aw=jsSetTimeout(60,_1A5);return _6B;},_1Ax=new T(function(){return B(unCStr("ADD"));}),_1Ay=new T(function(){return B(unCStr("ADJ"));}),_1Az=[0,1],_1AA=[1,_1Az],_1AB=[1,_1AA],_1AC=[0,_1Az],_1AD=[1,_1AC],_1AE=new T(function(){return B(unCStr("DN"));}),_1AF=new T(function(){return B(_3x(_9,_1AE));}),_1AG=new T(function(){return B(unCStr("MTP"));}),_1AH=new T(function(){return B(unCStr("MP"));}),_1AI=new T(function(){return B(unCStr("ID"));}),_1AJ=new T(function(){return B(unCStr("CD"));}),_1AK=[0,2],_1AL=[1,_1AK],_1AM=[1,_1AL],_1AN=[0,_1AK],_1AO=[1,_1AN],_1AP=function(_1AQ){if(!B(_3x(_1AQ,_1Ax))){if(!B(_3x(_1AQ,_1Ay))){if(!B(_3x(_1AQ,_1AJ))){if(!B(_3x(_1AQ,_1AI))){if(!B(_3x(_1AQ,_1AH))){if(!B(_3x(_1AQ,_1AG))){var _1AR=E(_1AQ);return _1AR[0]==0?!E(_1AF)?[0]:E(_1AD):E(E(_1AR[1])[1])==83?E(_1AR[2])[0]==0?E(_1AD):!B(_3x(_1AR,_1AE))?[0]:E(_1AD):!B(_3x(_1AR,_1AE))?[0]:E(_1AD);}else{return E(_1AO);}}else{return E(_1AO);}}else{return E(_1AM);}}else{return E(_1AB);}}else{return E(_1AO);}}else{return E(_1AD);}},_1AS=function(_1AT){return E(E(_1AT)[2]);},_1AU=function(_1AV,_1AW,_1AX){while(1){var _1AY=E(_1AW);if(!_1AY[0]){return E(_1AX)[0]==0?1:0;}else{var _1AZ=E(_1AX);if(!_1AZ[0]){return 2;}else{var _1B0=B(A(_1AS,[_1AV,_1AY[1],_1AZ[1]]));if(_1B0==1){_1AW=_1AY[2];_1AX=_1AZ[2];continue;}else{return E(_1B0);}}}}},_1B1=function(_1B2){return E(E(_1B2)[3]);},_1B3=function(_1B4,_1B5,_1B6,_1B7,_1B8){switch(B(_1AU(_1B4,_1B5,_1B7))){case 0:return true;case 1:return new F(function(){return A(_1B1,[_1B4,_1B6,_1B8]);});break;default:return false;}},_1B9=function(_1Ba,_1Bb,_1Bc,_1Bd){var _1Be=E(_1Bc),_1Bf=E(_1Bd);return new F(function(){return _1B3(_1Bb,_1Be[1],_1Be[2],_1Bf[1],_1Bf[2]);});},_1Bg=function(_1Bh){return E(E(_1Bh)[6]);},_1Bi=function(_1Bj,_1Bk,_1Bl,_1Bm,_1Bn){switch(B(_1AU(_1Bj,_1Bk,_1Bm))){case 0:return true;case 1:return new F(function(){return A(_1Bg,[_1Bj,_1Bl,_1Bn]);});break;default:return false;}},_1Bo=function(_1Bp,_1Bq,_1Br,_1Bs){var _1Bt=E(_1Br),_1Bu=E(_1Bs);return new F(function(){return _1Bi(_1Bq,_1Bt[1],_1Bt[2],_1Bu[1],_1Bu[2]);});},_1Bv=function(_1Bw){return E(E(_1Bw)[5]);},_1Bx=function(_1By,_1Bz,_1BA,_1BB,_1BC){switch(B(_1AU(_1By,_1Bz,_1BB))){case 0:return false;case 1:return new F(function(){return A(_1Bv,[_1By,_1BA,_1BC]);});break;default:return true;}},_1BD=function(_1BE,_1BF,_1BG,_1BH){var _1BI=E(_1BG),_1BJ=E(_1BH);return new F(function(){return _1Bx(_1BF,_1BI[1],_1BI[2],_1BJ[1],_1BJ[2]);});},_1BK=function(_1BL){return E(E(_1BL)[4]);},_1BM=function(_1BN,_1BO,_1BP,_1BQ,_1BR){switch(B(_1AU(_1BN,_1BO,_1BQ))){case 0:return false;case 1:return new F(function(){return A(_1BK,[_1BN,_1BP,_1BR]);});break;default:return true;}},_1BS=function(_1BT,_1BU,_1BV,_1BW){var _1BX=E(_1BV),_1BY=E(_1BW);return new F(function(){return _1BM(_1BU,_1BX[1],_1BX[2],_1BY[1],_1BY[2]);});},_1BZ=function(_1C0,_1C1,_1C2,_1C3,_1C4){switch(B(_1AU(_1C0,_1C1,_1C3))){case 0:return 0;case 1:return new F(function(){return A(_1AS,[_1C0,_1C2,_1C4]);});break;default:return 2;}},_1C5=function(_1C6,_1C7,_1C8,_1C9){var _1Ca=E(_1C8),_1Cb=E(_1C9);return new F(function(){return _1BZ(_1C7,_1Ca[1],_1Ca[2],_1Cb[1],_1Cb[2]);});},_1Cc=function(_1Cd,_1Ce,_1Cf,_1Cg){var _1Ch=E(_1Cf),_1Ci=_1Ch[1],_1Cj=_1Ch[2],_1Ck=E(_1Cg),_1Cl=_1Ck[1],_1Cm=_1Ck[2];switch(B(_1AU(_1Ce,_1Ci,_1Cl))){case 0:return [0,_1Cl,_1Cm];case 1:return !B(A(_1Bg,[_1Ce,_1Cj,_1Cm]))?[0,_1Ci,_1Cj]:[0,_1Cl,_1Cm];default:return [0,_1Ci,_1Cj];}},_1Cn=function(_1Co,_1Cp,_1Cq,_1Cr){var _1Cs=E(_1Cq),_1Ct=_1Cs[1],_1Cu=_1Cs[2],_1Cv=E(_1Cr),_1Cw=_1Cv[1],_1Cx=_1Cv[2];switch(B(_1AU(_1Cp,_1Ct,_1Cw))){case 0:return [0,_1Ct,_1Cu];case 1:return !B(A(_1Bg,[_1Cp,_1Cu,_1Cx]))?[0,_1Cw,_1Cx]:[0,_1Ct,_1Cu];default:return [0,_1Cw,_1Cx];}},_1Cy=function(_1Cz,_1CA){return [0,_1Cz,function(_ZT,_ZU){return new F(function(){return _1C5(_1Cz,_1CA,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1B9(_1Cz,_1CA,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1BS(_1Cz,_1CA,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1BD(_1Cz,_1CA,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Bo(_1Cz,_1CA,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Cc(_1Cz,_1CA,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Cn(_1Cz,_1CA,_ZT,_ZU);});}];},_1CB=function(_1CC,_1CD,_1CE,_1CF){return !B(A(_1CC,[_1CE,_1CF]))?B(_d3(B(A(_1CD,[_1CE,_16m])),B(A(_1CD,[_1CF,_16m]))))==2?false:true:false;},_1CG=function(_1CH,_1CI,_1CJ,_1CK){return new F(function(){return _1CB(E(_1CH)[1],_1CI,_1CJ,_1CK);});},_1CL=function(_1CM,_1CN,_1CO,_1CP){return B(_d3(B(A(_1CN,[_1CO,_16m])),B(A(_1CN,[_1CP,_16m]))))==2?false:true;},_1CQ=function(_1CR,_1CS,_1CT,_1CU){return !B(A(_1CR,[_1CT,_1CU]))?B(_d3(B(A(_1CS,[_1CT,_16m])),B(A(_1CS,[_1CU,_16m]))))==2?true:false:false;},_1CV=function(_1CW,_1CX,_1CY,_1CZ){return new F(function(){return _1CQ(E(_1CW)[1],_1CX,_1CY,_1CZ);});},_1D0=function(_1D1,_1D2,_1D3,_1D4){return !B(A(_1D1,[_1D3,_1D4]))?B(_d3(B(A(_1D2,[_1D3,_16m])),B(A(_1D2,[_1D4,_16m]))))==2?true:false:true;},_1D5=function(_1D6,_1D7,_1D8,_1D9){return new F(function(){return _1D0(E(_1D6)[1],_1D7,_1D8,_1D9);});},_1Da=function(_1Db,_1Dc,_1Dd,_1De){return !B(A(_1Db,[_1Dd,_1De]))?B(_d3(B(A(_1Dc,[_1Dd,_16m])),B(A(_1Dc,[_1De,_16m]))))==2?2:0:1;},_1Df=function(_1Dg,_1Dh,_1Di,_1Dj){return new F(function(){return _1Da(E(_1Dg)[1],_1Dh,_1Di,_1Dj);});},_1Dk=function(_1Dl,_1Dm,_1Dn,_1Do){return B(_d3(B(A(_1Dm,[_1Dn,_16m])),B(A(_1Dm,[_1Do,_16m]))))==2?E(_1Dn):E(_1Do);},_1Dp=function(_1Dq,_1Dr,_1Ds,_1Dt){return B(_d3(B(A(_1Dr,[_1Ds,_16m])),B(A(_1Dr,[_1Dt,_16m]))))==2?E(_1Dt):E(_1Ds);},_1Du=function(_1Dv,_1Dw){return [0,_1Dv,function(_44,_45){return new F(function(){return _1Df(_1Dv,_1Dw,_44,_45);});},function(_44,_45){return new F(function(){return _1CG(_1Dv,_1Dw,_44,_45);});},function(_44,_45){return new F(function(){return _1D5(_1Dv,_1Dw,_44,_45);});},function(_44,_45){return new F(function(){return _1CV(_1Dv,_1Dw,_44,_45);});},function(_44,_45){return new F(function(){return _1CL(_1Dv,_1Dw,_44,_45);});},function(_44,_45){return new F(function(){return _1Dk(_1Dv,_1Dw,_44,_45);});},function(_44,_45){return new F(function(){return _1Dp(_1Dv,_1Dw,_44,_45);});}];},_1Dx=function(_1Dy,_1Dz,_1DA,_1DB,_1DC,_1DD,_1DE){var _1DF=function(_1DG,_1DH){return new F(function(){return _2W(_1Dy,_1Dz,_1DA,_1DC,_1DB,_1DE,_1DD,_1DG);});};return function(_1DI,_1DJ){var _1DK=E(_1DI);if(!_1DK[0]){var _1DL=E(_1DJ);return _1DL[0]==0?B(_d3(B(_1r(_1DK[1])),B(_1r(_1DL[1]))))==2?false:true:true;}else{var _1DM=E(_1DJ);return _1DM[0]==0?false:B(_1AU(new T(function(){return B(_1Du(new T(function(){return B(_16r(_1DF));}),_1DF));}),_1DK[1],_1DM[1]))==2?false:true;}};},_1DN=function(_1DO,_1DP,_1DQ,_1DR,_1DS,_1DT,_1DU,_1DV,_1DW,_1DX){return !B(A(_1Dx,[_1DP,_1DQ,_1DR,_1DS,_1DT,_1DU,_1DV,_1DW,_1DX]))?E(_1DW):E(_1DX);},_1DY=function(_1DZ,_1E0,_1E1,_1E2,_1E3,_1E4,_1E5,_1E6,_1E7,_1E8){return !B(A(_1Dx,[_1E0,_1E1,_1E2,_1E3,_1E4,_1E5,_1E6,_1E7,_1E8]))?E(_1E8):E(_1E7);},_1E9=function(_1Ea,_1Eb,_1Ec,_1Ed,_1Ee,_1Ef,_1Eg){var _1Eh=function(_1Ei,_1Ej){return new F(function(){return _2W(_1Ea,_1Eb,_1Ec,_1Ee,_1Ed,_1Eg,_1Ef,_1Ei);});};return function(_1Ek,_1El){var _1Em=E(_1Ek);if(!_1Em[0]){var _1En=_1Em[1],_1Eo=E(_1El);if(!_1Eo[0]){var _1Ep=_1Eo[1];return B(_109(_1En,_1Ep,_1))[0]==0?B(_d3(B(_1r(_1En)),B(_1r(_1Ep))))==2?false:true:false;}else{return true;}}else{var _1Eq=E(_1El);return _1Eq[0]==0?false:B(_1AU(new T(function(){return B(_1Du(new T(function(){return B(_16r(_1Eh));}),_1Eh));}),_1Em[1],_1Eq[1]))==0?true:false;}};},_1Er=function(_1Es,_1Et,_1Eu,_1Ev,_1Ew,_1Ex,_1Ey){var _1Ez=function(_1EA,_1EB){return new F(function(){return _2W(_1Es,_1Et,_1Eu,_1Ew,_1Ev,_1Ey,_1Ex,_1EA);});};return function(_1EC,_1ED){var _1EE=E(_1EC);if(!_1EE[0]){var _1EF=_1EE[1],_1EG=E(_1ED);if(!_1EG[0]){var _1EH=_1EG[1];return B(_109(_1EF,_1EH,_1))[0]==0?B(_d3(B(_1r(_1EF)),B(_1r(_1EH))))==2?true:false:false;}else{return false;}}else{var _1EI=E(_1ED);return _1EI[0]==0?true:B(_1AU(new T(function(){return B(_1Du(new T(function(){return B(_16r(_1Ez));}),_1Ez));}),_1EE[1],_1EI[1]))==2?true:false;}};},_1EJ=function(_1EK,_1EL,_1EM,_1EN,_1EO,_1EP,_1EQ){var _1ER=function(_1ES,_1ET){return new F(function(){return _2W(_1EK,_1EL,_1EM,_1EO,_1EN,_1EQ,_1EP,_1ES);});};return function(_1EU,_1EV){var _1EW=E(_1EU);if(!_1EW[0]){var _1EX=_1EW[1],_1EY=E(_1EV);if(!_1EY[0]){var _1EZ=_1EY[1];return B(_109(_1EX,_1EZ,_1))[0]==0?B(_d3(B(_1r(_1EX)),B(_1r(_1EZ))))==2?true:false:true;}else{return false;}}else{var _1F0=E(_1EV);return _1F0[0]==0?true:B(_1AU(new T(function(){return B(_1Du(new T(function(){return B(_16r(_1ER));}),_1ER));}),_1EW[1],_1F0[1]))==0?false:true;}};},_1F1=function(_1F2,_1F3,_1F4,_1F5,_1F6,_1F7,_1F8){var _1F9=function(_1Fa,_1Fb){return new F(function(){return _2W(_1F2,_1F3,_1F4,_1F6,_1F5,_1F8,_1F7,_1Fa);});};return function(_1Fc,_1Fd){var _1Fe=E(_1Fc);if(!_1Fe[0]){var _1Ff=_1Fe[1],_1Fg=E(_1Fd);if(!_1Fg[0]){var _1Fh=_1Fg[1];return B(_109(_1Ff,_1Fh,_1))[0]==0?B(_d3(B(_1r(_1Ff)),B(_1r(_1Fh))))==2?2:0:1;}else{return 0;}}else{var _1Fi=E(_1Fd);return _1Fi[0]==0?2:B(_1AU(new T(function(){return B(_1Du(new T(function(){return B(_16r(_1F9));}),_1F9));}),_1Fe[1],_1Fi[1]));}};},_1Fj=function(_1Fk,_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr){return [0,_1Fk,new T(function(){return B(_1F1(_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr));}),new T(function(){return B(_1E9(_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr));}),new T(function(){return B(_1EJ(_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr));}),new T(function(){return B(_1Er(_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr));}),new T(function(){return B(_1Dx(_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr));}),function(_44,_45){return new F(function(){return _1DN(_1Fk,_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr,_44,_45);});},function(_44,_45){return new F(function(){return _1DY(_1Fk,_1Fl,_1Fm,_1Fn,_1Fo,_1Fp,_1Fq,_1Fr,_44,_45);});}];},_1Fs=new T(function(){return B(_3W(_Q,_u,_Q,_Q,_N,_2,_15));}),_1Ft=new T(function(){return B(_1Fj(_1Fs,_Q,_u,_Q,_Q,_N,_15,_2));}),_1Fu=new T(function(){return B(_107(_1Fs));}),_1Fv=new T(function(){return B(_1Cy(_1Fu,_1Ft));}),_1Fw=function(_1Fx,_1Fy,_1Fz,_1FA){var _1FB=E(_1Fz),_1FC=E(_1FA);return new F(function(){return _1B3(_1Fy,_1FB[1],_1FB[2],_1FC[1],_1FC[2]);});},_1FD=function(_1FE,_1FF,_1FG,_1FH){var _1FI=E(_1FG),_1FJ=E(_1FH);return new F(function(){return _1Bi(_1FF,_1FI[1],_1FI[2],_1FJ[1],_1FJ[2]);});},_1FK=function(_1FL,_1FM,_1FN,_1FO){var _1FP=E(_1FN),_1FQ=E(_1FO);return new F(function(){return _1Bx(_1FM,_1FP[1],_1FP[2],_1FQ[1],_1FQ[2]);});},_1FR=function(_1FS,_1FT,_1FU,_1FV){var _1FW=E(_1FU),_1FX=E(_1FV);return new F(function(){return _1BM(_1FT,_1FW[1],_1FW[2],_1FX[1],_1FX[2]);});},_1FY=function(_1FZ,_1G0,_1G1,_1G2){var _1G3=E(_1G1),_1G4=E(_1G2);return new F(function(){return _1BZ(_1G0,_1G3[1],_1G3[2],_1G4[1],_1G4[2]);});},_1G5=function(_1G6,_1G7,_1G8,_1G9){var _1Ga=E(_1G8),_1Gb=_1Ga[1],_1Gc=_1Ga[2],_1Gd=E(_1G9),_1Ge=_1Gd[1],_1Gf=_1Gd[2];switch(B(_1AU(_1G7,_1Gb,_1Ge))){case 0:return [0,_1Ge,_1Gf];case 1:return !B(A(_1Bg,[_1G7,_1Gc,_1Gf]))?[0,_1Gb,_1Gc]:[0,_1Ge,_1Gf];default:return [0,_1Gb,_1Gc];}},_1Gg=function(_1Gh,_1Gi,_1Gj,_1Gk){var _1Gl=E(_1Gj),_1Gm=_1Gl[1],_1Gn=_1Gl[2],_1Go=E(_1Gk),_1Gp=_1Go[1],_1Gq=_1Go[2];switch(B(_1AU(_1Gi,_1Gm,_1Gp))){case 0:return [0,_1Gm,_1Gn];case 1:return !B(A(_1Bg,[_1Gi,_1Gn,_1Gq]))?[0,_1Gp,_1Gq]:[0,_1Gm,_1Gn];default:return [0,_1Gp,_1Gq];}},_1Gr=function(_1Gs,_1Gt){return [0,_1Gs,function(_ZT,_ZU){return new F(function(){return _1FY(_1Gs,_1Gt,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Fw(_1Gs,_1Gt,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1FR(_1Gs,_1Gt,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1FK(_1Gs,_1Gt,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1FD(_1Gs,_1Gt,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1G5(_1Gs,_1Gt,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Gg(_1Gs,_1Gt,_ZT,_ZU);});}];},_1Gu=function(_1Gv,_1Gw){return B(_d3(_1Gv,_1Gw))==0?false:true;},_1Gx=function(_1Gy){return E(E(_1Gy)[1]);},_1Gz=function(_1GA){return function(_1GB,_1GC){var _1GD=E(_1GB),_1GE=E(_1GC);switch(B(_1AU(new T(function(){return B(_1Gr(new T(function(){return B(_ZR(new T(function(){return B(_1Gx(_1GA));})));}),_1GA));}),_1GD[1],_1GE[1]))){case 0:return false;case 1:return new F(function(){return _1Gu(_1GD[2],_1GE[2]);});break;default:return true;}};},_1GF=new T(function(){return B(_1Gz(_1Fv));}),_1GG=function(_1GH,_1GI,_1GJ){var _1GK=E(_1GH);if(_1GK==1){var _1GL=E(_1GJ);return _1GL[0]==0?[0,new T(function(){return [0,1,E(E(_1GI)),E(_1e4),E(_1e4)];}),_9,_9]:!B(A(_1GF,[_1GI,_1GL[1]]))?[0,new T(function(){return [0,1,E(E(_1GI)),E(_1e4),E(_1e4)];}),_1GL,_9]:[0,new T(function(){return [0,1,E(E(_1GI)),E(_1e4),E(_1e4)];}),_9,_1GL];}else{var _1GM=B(_1GG(_1GK>>1,_1GI,_1GJ)),_1GN=_1GM[1],_1GO=_1GM[3],_1GP=E(_1GM[2]);if(!_1GP[0]){return [0,_1GN,_9,_1GO];}else{var _1GQ=_1GP[1],_1GR=E(_1GP[2]);if(!_1GR[0]){return [0,new T(function(){return B(_1fr(_1GQ,_1GN));}),_9,_1GO];}else{var _1GS=_1GR[1];if(!B(A(_1GF,[_1GQ,_1GS]))){var _1GT=B(_1GG(_1GK>>1,_1GS,_1GR[2]));return [0,new T(function(){return B(_1g5(_1GQ,_1GN,_1GT[1]));}),_1GT[2],_1GT[3]];}else{return [0,_1GN,_9,_1GP];}}}}},_1GU=function(_1GV,_1GW){return B(_d3(_1GV,_1GW))==2?false:true;},_1GX=function(_1GY){return function(_1GZ,_1H0){var _1H1=E(_1GZ),_1H2=E(_1H0);switch(B(_1AU(new T(function(){return B(_1Gr(new T(function(){return B(_ZR(new T(function(){return B(_1Gx(_1GY));})));}),_1GY));}),_1H1[1],_1H2[1]))){case 0:return true;case 1:return new F(function(){return _1GU(_1H1[2],_1H2[2]);});break;default:return false;}};},_1H3=function(_1H4,_1H5,_1H6,_1H7){return !B(A(_1GX,[_1H5,_1H6,_1H7]))?E(_1H6):E(_1H7);},_1H8=function(_1H9,_1Ha,_1Hb,_1Hc){return !B(A(_1GX,[_1Ha,_1Hb,_1Hc]))?E(_1Hc):E(_1Hb);},_1Hd=function(_1He,_1Hf){return B(_d3(_1He,_1Hf))==0?true:false;},_1Hg=function(_1Hh){return function(_1Hi,_1Hj){var _1Hk=E(_1Hi),_1Hl=E(_1Hj);switch(B(_1AU(new T(function(){return B(_1Gr(new T(function(){return B(_ZR(new T(function(){return B(_1Gx(_1Hh));})));}),_1Hh));}),_1Hk[1],_1Hl[1]))){case 0:return true;case 1:return new F(function(){return _1Hd(_1Hk[2],_1Hl[2]);});break;default:return false;}};},_1Hm=function(_1Hn,_1Ho){return B(_d3(_1Hn,_1Ho))==2?true:false;},_1Hp=function(_1Hq){return function(_1Hr,_1Hs){var _1Ht=E(_1Hr),_1Hu=E(_1Hs);switch(B(_1AU(new T(function(){return B(_1Gr(new T(function(){return B(_ZR(new T(function(){return B(_1Gx(_1Hq));})));}),_1Hq));}),_1Ht[1],_1Hu[1]))){case 0:return false;case 1:return new F(function(){return _1Hm(_1Ht[2],_1Hu[2]);});break;default:return true;}};},_1Hv=function(_1Hw){return function(_1Hx,_1Hy){var _1Hz=E(_1Hx),_1HA=E(_1Hy);switch(B(_1AU(new T(function(){return B(_1Gr(new T(function(){return B(_ZR(new T(function(){return B(_1Gx(_1Hw));})));}),_1Hw));}),_1Hz[1],_1HA[1]))){case 0:return 0;case 1:return new F(function(){return _d3(_1Hz[2],_1HA[2]);});break;default:return 2;}};},_1HB=function(_1HC,_1HD){return [0,_1HC,new T(function(){return B(_1Hv(_1HD));}),new T(function(){return B(_1Hg(_1HD));}),new T(function(){return B(_1Gz(_1HD));}),new T(function(){return B(_1Hp(_1HD));}),new T(function(){return B(_1GX(_1HD));}),function(_ZT,_ZU){return new F(function(){return _1H3(_1HC,_1HD,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1H8(_1HC,_1HD,_ZT,_ZU);});}];},_1HE=function(_1HF,_1HG,_1HH,_1HI,_1HJ){return !B(_Zt(new T(function(){return B(_ZR(_1HF));}),_1HG,_1HI))?true:!B(_3x(_1HH,_1HJ))?true:false;},_1HK=function(_1HL,_1HM,_1HN){var _1HO=E(_1HM),_1HP=E(_1HN);return new F(function(){return _1HE(_1HL,_1HO[1],_1HO[2],_1HP[1],_1HP[2]);});},_1HQ=function(_1HR){return function(_1HS,_1HT){var _1HU=E(_1HS),_1HV=E(_1HT);return !B(_Zt(new T(function(){return B(_ZR(_1HR));}),_1HU[1],_1HV[1]))?false:B(_3x(_1HU[2],_1HV[2]));};},_1HW=function(_1HX){return [0,new T(function(){return B(_1HQ(_1HX));}),function(_ZT,_ZU){return new F(function(){return _1HK(_1HX,_ZT,_ZU);});}];},_1HY=new T(function(){return B(_1HW(_1Fu));}),_1HZ=new T(function(){return B(_1HB(_1HY,_1Fv));}),_1I0=function(_1I1,_1I2,_1I3){var _1I4=E(_1I2),_1I5=E(_1I3);if(!_1I5[0]){var _1I6=_1I5[2],_1I7=_1I5[3],_1I8=_1I5[4];switch(B(A(_1AS,[_1I1,_1I4,_1I6]))){case 0:return new F(function(){return _1e9(_1I6,B(_1I0(_1I1,_1I4,_1I7)),_1I8);});break;case 1:return [0,_1I5[1],E(_1I4),E(_1I7),E(_1I8)];default:return new F(function(){return _1eL(_1I6,_1I7,B(_1I0(_1I1,_1I4,_1I8)));});}}else{return [0,1,E(_1I4),E(_1e4),E(_1e4)];}},_1I9=function(_1Ia,_1Ib){while(1){var _1Ic=E(_1Ib);if(!_1Ic[0]){return E(_1Ia);}else{var _1Id=B(_1I0(_1HZ,_1Ic[1],_1Ia));_1Ib=_1Ic[2];_1Ia=_1Id;continue;}}},_1Ie=function(_1If,_1Ig,_1Ih){return new F(function(){return _1I9(B(_1I0(_1HZ,_1Ig,_1If)),_1Ih);});},_1Ii=function(_1Ij,_1Ik,_1Il){while(1){var _1Im=E(_1Il);if(!_1Im[0]){return E(_1Ik);}else{var _1In=_1Im[1],_1Io=E(_1Im[2]);if(!_1Io[0]){return new F(function(){return _1fr(_1In,_1Ik);});}else{var _1Ip=_1Io[1];if(!B(A(_1GF,[_1In,_1Ip]))){var _1Iq=B(_1GG(_1Ij,_1Ip,_1Io[2])),_1Ir=_1Iq[1],_1Is=E(_1Iq[3]);if(!_1Is[0]){var _1It=_1Ij<<1,_1Iu=B(_1g5(_1In,_1Ik,_1Ir));_1Il=_1Iq[2];_1Ij=_1It;_1Ik=_1Iu;continue;}else{return new F(function(){return _1Ie(B(_1g5(_1In,_1Ik,_1Ir)),_1Is[1],_1Is[2]);});}}else{return new F(function(){return _1Ie(_1Ik,_1In,_1Io);});}}}}},_1Iv=function(_1Iw,_1Ix,_1Iy,_1Iz){var _1IA=E(_1Iz);if(!_1IA[0]){return new F(function(){return _1fr(_1Iy,_1Ix);});}else{var _1IB=_1IA[1];if(!B(A(_1GF,[_1Iy,_1IB]))){var _1IC=B(_1GG(_1Iw,_1IB,_1IA[2])),_1ID=_1IC[1],_1IE=E(_1IC[3]);if(!_1IE[0]){return new F(function(){return _1Ii(_1Iw<<1,B(_1g5(_1Iy,_1Ix,_1ID)),_1IC[2]);});}else{return new F(function(){return _1Ie(B(_1g5(_1Iy,_1Ix,_1ID)),_1IE[1],_1IE[2]);});}}else{return new F(function(){return _1Ie(_1Ix,_1Iy,_1IA);});}}},_1IF=function(_1IG){var _1IH=E(_1IG);if(!_1IH[0]){return [1];}else{var _1II=_1IH[1],_1IJ=E(_1IH[2]);if(!_1IJ[0]){return [0,1,E(E(_1II)),E(_1e4),E(_1e4)];}else{var _1IK=_1IJ[1],_1IL=_1IJ[2];if(!B(A(_1GF,[_1II,_1IK]))){return new F(function(){return _1Iv(1,[0,1,E(E(_1II)),E(_1e4),E(_1e4)],_1IK,_1IL);});}else{return new F(function(){return _1Ie([0,1,E(E(_1II)),E(_1e4),E(_1e4)],_1IK,_1IL);});}}}},_1IM=new T(function(){return B(_F(0,1,_9));}),_1IN=new T(function(){return B(unAppCStr("delta_",_1IM));}),_1IO=[9,_,_,_1IN],_1IP=[0,_1IO],_1IQ=[1,_1IP,_9],_1IR=new T(function(){return B(unAppCStr("phi_",_1IM));}),_1IS=[3,_,_,_1IR],_1IT=[2,_,_1IS],_1IU=[1,_1IT,_9],_1IV=[1,_1IU],_1IW=[0,_1IQ,_1IV],_1IX=new T(function(){return B(_F(0,2,_9));}),_1IY=new T(function(){return B(unAppCStr("phi_",_1IX));}),_1IZ=[3,_,_,_1IY],_1J0=[2,_,_1IZ],_1J1=[1,_1J0,_9],_1J2=[1,_1J1],_1J3=new T(function(){return B(unAppCStr("delta_",_1IX));}),_1J4=[9,_,_,_1J3],_1J5=[0,_1J4],_1J6=[1,_1J5,_9],_1J7=[0,_1J6,_1J2],_1J8=[1,_1J7,_9],_1J9=[1,_1IW,_1J8],_1Ja=function(_1Jb,_1Jc){var _1Jd=E(_1Jb);if(!_1Jd[0]){return [0];}else{var _1Je=_1Jd[1],_1Jf=_1Jd[2],_1Jg=function(_1Jh,_1Ji,_1Jj){var _1Jk=E(_1Ji);if(!_1Jk[0]){return [0,_1Jf,_1Jj];}else{var _1Jl=_1Jk[1],_1Jm=new T(function(){var _1Jn=B(_1Jg(function(_1Jo){return new F(function(){return A(_1Jh,[[1,_1Jl,_1Jo]]);});},_1Jk[2],_1Jj));return [0,_1Jn[1],_1Jn[2]];}),_1Jp=new T(function(){return E(E(_1Jm)[1]);});return [0,[1,_1Jl,_1Jp],[1,new T(function(){return B(A(_1Jh,[[1,_1Je,[1,_1Jl,_1Jp]]]));}),new T(function(){return E(E(_1Jm)[2]);})]];}},_1Jq=function(_1Jr){var _1Js=E(_1Jr);return _1Js[0]==0?E(new T(function(){return B(_1Ja(_1Jf,[1,_1Je,_1Jc]));})):E(B(_1Jg(_6P,_1Js[1],new T(function(){return B(_1Jq(_1Js[2]));})))[2]);};return new F(function(){return _1Jq([1,_1Jc,new T(function(){return B(_1Ja(_1Jc,_9));})]);});}},_1Jt=new T(function(){return B(_1Ja(_1J9,_9));}),_1Ju=[1,_1J9,_1Jt],_1Jv=[9,_,_P8,_1IT,_1J0],_1Jw=[1,_1Jv,_9],_1Jx=[1,_1Jw],_1Jy=[1,_1IP,_1J6],_1Jz=[0,_1Jy,_1Jx],_1JA=function(_1JB){return [0,_1JB,_1Jz];},_1JC=new T(function(){return B(_3d(_1JA,_1Ju));}),_1JD=[0,_1JC,_1Ay],_1JE=[1,_1IW,_9],_1JF=[9,_,_OK,_1IT,_1J0],_1JG=[1,_1JF,_9],_1JH=[1,_1JG],_1JI=[0,_1IQ,_1JH],_1JJ=[0,_1JE,_1JI],_1JK=[9,_,_OK,_1J0,_1IT],_1JL=[1,_1JK,_9],_1JM=[1,_1JL],_1JN=[0,_1IQ,_1JM],_1JO=[0,_1JE,_1JN],_1JP=[1,_1JO,_9],_1JQ=[1,_1JJ,_1JP],_1JR=[0,_1JQ,_1Ax],_1JS=[1,_1IV,_1IQ],_1JT=[0,_1JS,_1J2],_1JU=[7,_,_Pz,_1J0],_1JV=[1,_1JU,_9],_1JW=[1,_1JV],_1JX=[1,_1IV,_1J6],_1JY=[0,_1JX,_1JW],_1JZ=[1,_1JY,_9],_1K0=[1,_1JT,_1JZ],_1K1=new T(function(){return B(_1Ja(_1K0,_9));}),_1K2=[7,_,_Pz,_1IT],_1K3=[1,_1K2,_9],_1K4=[1,_1K3],_1K5=[0,_1Jy,_1K4],_1K6=[0,_1Jy,_1IV],_1K7=function(_1K8){return [0,_1K8,_1K6];},_1K9=[0,_1IQ,_1J2],_1Ka=[1,_1K9,_9],_1Kb=[0,_1J6,_1JW],_1Kc=[1,_1Kb,_1Ka],_1Kd=new T(function(){return B(_1Ja(_1Kc,_9));}),_1Ke=[1,_1Kc,_1Kd],_1Kf=new T(function(){return B(_3d(_1K7,_1Ke));}),_1Kg=function(_1Kh){var _1Ki=E(_1Kh);return _1Ki[0]==0?E(_1Kf):[1,[0,_1Ki[1],_1K6],new T(function(){return B(_1Kg(_1Ki[2]));})];},_1Kj=function(_1Kk,_1Kl){return [1,[0,_1Kk,_1K6],new T(function(){return B(_1Kg(_1Kl));})];},_1Km=[1,_1K4,_1J6],_1Kn=[0,_1Km,_1JW],_1Ko=[1,_1Kn,_1Ka],_1Kp=new T(function(){return B(_1Ja(_1Ko,_9));}),_1Kq=new T(function(){return B(_1Kj(_1Ko,_1Kp));}),_1Kr=function(_1Ks){var _1Kt=E(_1Ks);return _1Kt[0]==0?E(_1Kq):[1,[0,_1Kt[1],_1K6],new T(function(){return B(_1Kr(_1Kt[2]));})];},_1Ku=function(_1Kv,_1Kw){return [1,[0,_1Kv,_1K6],new T(function(){return B(_1Kr(_1Kw));})];},_1Kx=[1,_1K4,_1IQ],_1Ky=[0,_1Kx,_1J2],_1Kz=[1,_1Ky,_9],_1KA=[1,_1Kb,_1Kz],_1KB=new T(function(){return B(_1Ja(_1KA,_9));}),_1KC=new T(function(){return B(_1Ku(_1KA,_1KB));}),_1KD=function(_1KE){var _1KF=E(_1KE);return _1KF[0]==0?E(_1KC):[1,[0,_1KF[1],_1K6],new T(function(){return B(_1KD(_1KF[2]));})];},_1KG=function(_1KH,_1KI){return [1,[0,_1KH,_1K6],new T(function(){return B(_1KD(_1KI));})];},_1KJ=[1,_1Kn,_1Kz],_1KK=new T(function(){return B(_1Ja(_1KJ,_9));}),_1KL=new T(function(){return B(_1KG(_1KJ,_1KK));}),_1KM=function(_1KN){var _1KO=E(_1KN);return _1KO[0]==0?E(_1KL):[1,[0,_1KO[1],_1K5],new T(function(){return B(_1KM(_1KO[2]));})];},_1KP=function(_1KQ,_1KR){return [1,[0,_1KQ,_1K5],new T(function(){return B(_1KM(_1KR));})];},_1KS=[1,_1Kb,_9],_1KT=[1,_1K9,_1KS],_1KU=new T(function(){return B(_1Ja(_1KT,_9));}),_1KV=new T(function(){return B(_1KP(_1KT,_1KU));}),_1KW=function(_1KX){var _1KY=E(_1KX);return _1KY[0]==0?E(_1KV):[1,[0,_1KY[1],_1K5],new T(function(){return B(_1KW(_1KY[2]));})];},_1KZ=function(_1L0,_1L1){return [1,[0,_1L0,_1K5],new T(function(){return B(_1KW(_1L1));})];},_1L2=[1,_1JT,_1KS],_1L3=new T(function(){return B(_1Ja(_1L2,_9));}),_1L4=new T(function(){return B(_1KZ(_1L2,_1L3));}),_1L5=function(_1L6){var _1L7=E(_1L6);return _1L7[0]==0?E(_1L4):[1,[0,_1L7[1],_1K5],new T(function(){return B(_1L5(_1L7[2]));})];},_1L8=function(_1L9,_1La){return [1,[0,_1L9,_1K5],new T(function(){return B(_1L5(_1La));})];},_1Lb=[1,_1K9,_1JZ],_1Lc=new T(function(){return B(_1Ja(_1Lb,_9));}),_1Ld=new T(function(){return B(_1L8(_1Lb,_1Lc));}),_1Le=function(_1Lf){var _1Lg=E(_1Lf);return _1Lg[0]==0?E(_1Ld):[1,[0,_1Lg[1],_1K5],new T(function(){return B(_1Le(_1Lg[2]));})];},_1Lh=function(_1Li,_1Lj){return [1,[0,_1Li,_1K5],new T(function(){return B(_1Le(_1Lj));})];},_1Lk=new T(function(){return B(_1Lh(_1K0,_1K1));}),_1Ll=[0,_1Lk,_1AI],_1Lm=[1,_1Ll,_9],_1Ln=[1,_1JR,_1Lm],_1Lo=[0,83],_1Lp=[1,_1Lo,_9],_1Lq=[0,_1IQ,_1Jx],_1Lr=[1,_1Lq,_9],_1Ls=[0,_1Lr,_1IW],_1Lt=[0,_1Lr,_1K9],_1Lu=[1,_1Lt,_9],_1Lv=[1,_1Ls,_1Lu],_1Lw=[0,_1Lv,_1Lp],_1Lx=[1,_1Lw,_1Ln],_1Ly=[1,_1JN,_1KS],_1Lz=new T(function(){return B(_1Ja(_1Ly,_9));}),_1LA=[0,_1J6,_1K4],_1LB=[1,_1LA,_9],_1LC=[1,_1JN,_1LB],_1LD=new T(function(){return B(_1Ja(_1LC,_9));}),_1LE=[1,_1LC,_1LD],_1LF=[0,_1Jy,_1J2],_1LG=function(_1LH){return [0,_1LH,_1LF];},_1LI=new T(function(){return B(_3d(_1LG,_1LE));}),_1LJ=function(_1LK){var _1LL=E(_1LK);return _1LL[0]==0?E(_1LI):[1,[0,_1LL[1],_1K6],new T(function(){return B(_1LJ(_1LL[2]));})];},_1LM=function(_1LN,_1LO){return [1,[0,_1LN,_1K6],new T(function(){return B(_1LJ(_1LO));})];},_1LP=new T(function(){return B(_1LM(_1Ly,_1Lz));}),_1LQ=[0,_1LP,_1AG],_1LR=[1,_1LQ,_1Lx],_1LS=[9,_,_Ny,_1IT,_1J0],_1LT=[1,_1LS,_9],_1LU=[1,_1LT],_1LV=[0,_1J6,_1LU],_1LW=[1,_1LV,_9],_1LX=[1,_1IW,_1LW],_1LY=new T(function(){return B(_1Ja(_1LX,_9));}),_1LZ=[1,_1LX,_1LY],_1M0=new T(function(){return B(_3d(_1LG,_1LZ));}),_1M1=[0,_1M0,_1AH],_1M2=[1,_1M1,_1LR],_1M3=[0,_1IQ,_1LU],_1M4=[1,_1JT,_9],_1M5=[0,_1M4,_1M3],_1M6=[0,_1Ka,_1M3],_1M7=[1,_1M6,_9],_1M8=[1,_1M5,_1M7],_1M9=[0,_1M8,_1AJ],_1Ma=[1,_1M9,_1M2],_1Mb=[1,_1JD,_1Ma],_1Mc=new T(function(){return B(_1IF(_1Mb));}),_1Md=[0,_1AP,_1Mc],_1Me=function(_){return new F(function(){return _1Aa(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1Md,_);});},_1Mf=function(_){return new F(function(){return _1Me(_);});};
var hasteMain = function() {B(A(_1Mf, [0]));};window.onload = hasteMain;