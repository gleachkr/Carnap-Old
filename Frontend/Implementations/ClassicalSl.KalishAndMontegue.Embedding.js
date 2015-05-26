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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr(" . "));}),_1r=function(_1s){var _1t=E(_1s);switch(_1t[0]){case 0:return E(_1t[3]);case 1:return E(_1t[3]);case 2:return E(_1t[3]);case 3:return E(_1t[3]);case 4:return E(_1t[3]);case 5:return E(_1t[3]);case 6:return E(_1t[3]);case 7:return E(_1t[3]);case 8:return E(_1t[3]);default:return E(_1t[3]);}},_1u=[0,41],_1v=[1,_1u,_9],_1w=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1x=new T(function(){return B(unCStr("base"));}),_1y=new T(function(){return B(unCStr("PatternMatchFail"));}),_1z=new T(function(){var _1A=hs_wordToWord64(18445595),_1B=_1A,_1C=hs_wordToWord64(52003073),_1D=_1C;return [0,_1B,_1D,[0,_1B,_1D,_1x,_1w,_1y],_9];}),_1E=function(_1F){return E(_1z);},_1G=function(_1H){return E(E(_1H)[1]);},_1I=function(_1J,_1K,_1L){var _1M=B(A(_1J,[_])),_1N=B(A(_1K,[_])),_1O=hs_eqWord64(_1M[1],_1N[1]),_1P=_1O;if(!E(_1P)){return [0];}else{var _1Q=hs_eqWord64(_1M[2],_1N[2]),_1R=_1Q;return E(_1R)==0?[0]:[1,_1L];}},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return _1I(B(_1G(_1U[1])),_1E,_1U[2]);});},_1V=function(_1W){return E(E(_1W)[1]);},_1X=function(_1Y,_1Z){return new F(function(){return _e(E(_1Y)[1],_1Z);});},_20=[0,44],_21=[0,93],_22=[0,91],_23=function(_24,_25,_26){var _27=E(_25);return _27[0]==0?B(unAppCStr("[]",_26)):[1,_22,new T(function(){return B(A(_24,[_27[1],new T(function(){var _28=function(_29){var _2a=E(_29);return _2a[0]==0?E([1,_21,_26]):[1,_20,new T(function(){return B(A(_24,[_2a[1],new T(function(){return B(_28(_2a[2]));})]));})];};return B(_28(_27[2]));})]));})];},_2b=function(_2c,_2d){return new F(function(){return _23(_1X,_2c,_2d);});},_2e=function(_2f,_2g,_2h){return new F(function(){return _e(E(_2g)[1],_2h);});},_2i=[0,_2e,_1V,_2b],_2j=new T(function(){return [0,_1E,_2i,_2k,_1S];}),_2k=function(_2l){return [0,_2j,_2l];},_2m=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_2n=function(_2o,_2p){return new F(function(){return die(new T(function(){return B(A(_2p,[_2o]));}));});},_2q=function(_2r,_2s){var _2t=E(_2s);if(!_2t[0]){return [0,_9,_9];}else{var _2u=_2t[1];if(!B(A(_2r,[_2u]))){return [0,_9,_2t];}else{var _2v=new T(function(){var _2w=B(_2q(_2r,_2t[2]));return [0,_2w[1],_2w[2]];});return [0,[1,_2u,new T(function(){return E(E(_2v)[1]);})],new T(function(){return E(E(_2v)[2]);})];}}},_2x=[0,32],_2y=[0,10],_2z=[1,_2y,_9],_2A=function(_2B){return E(E(_2B)[1])==124?false:true;},_2C=function(_2D,_2E){var _2F=B(_2q(_2A,B(unCStr(_2D)))),_2G=_2F[1],_2H=function(_2I,_2J){return new F(function(){return _e(_2I,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_2E,new T(function(){return B(_e(_2J,_2z));},1)));})));},1));});},_2K=E(_2F[2]);if(!_2K[0]){return new F(function(){return _2H(_2G,_9);});}else{return E(E(_2K[1])[1])==124?B(_2H(_2G,[1,_2x,_2K[2]])):B(_2H(_2G,_9));}},_2L=function(_2M){return new F(function(){return _2n([0,new T(function(){return B(_2C(_2M,_2m));})],_2k);});},_2N=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_2O=[0,44],_2P=[0,40],_2Q=function(_2R,_2S,_2T){var _2U=E(_2T);switch(_2U[0]){case 0:return E(_2N);case 1:return new F(function(){return A(_2R,[_2U[2],_9]);});break;case 2:return new F(function(){return _1r(_2U[2]);});break;case 3:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),[1,new T(function(){return B(_2Q(_2R,_2S,_2U[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[4])),_1v));})]));})]);});}},_2V=[0],_2W=function(_2X,_2Y,_2Z,_30,_31,_32,_33,_34){var _35=E(_34);switch(_35[0]){case 0:return [0];case 1:return new F(function(){return A(_30,[_35[2],_9]);});break;case 2:return new F(function(){return _1r(_35[2]);});break;case 3:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),[1,new T(function(){return B(_2Q(_30,_31,_35[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_30,_31,_35[4])),_1v));})]));})]);});break;case 7:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_1r(_35[2])),new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));},1));});break;case 9:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4]));}),_9]]]);});break;case 10:return [1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3])),new T(function(){return B(_e(B(_1r(_35[2])),new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4])),_1v));},1)));},1)));})];case 11:var _36=_35[2],_37=_35[3];return new F(function(){return A(_2Z,[_36,[1,new T(function(){return B(A(_32,[new T(function(){return B(A(_37,[_2V]));}),_36]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_37,[_2V]))));}),_9]]]);});break;default:var _38=_35[2],_39=_35[3];return new F(function(){return _e(B(_1r(_38)),new T(function(){return B(_e(B(A(_33,[new T(function(){return B(A(_39,[_2V]));}),_38])),[1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_39,[_2V])))),_1v));})]));},1));});}},_3a=function(_3b){var _3c=E(_3b);if(!_3c[0]){return [0];}else{return new F(function(){return _e(_3c[1],new T(function(){return B(_3a(_3c[2]));},1));});}},_3d=function(_3e,_3f){var _3g=E(_3f);return _3g[0]==0?[0]:[1,new T(function(){return B(A(_3e,[_3g[1]]));}),new T(function(){return B(_3d(_3e,_3g[2]));})];},_3h=function(_3i,_3j){var _3k=E(_3j);return _3k[0]==0?[0]:[1,_3i,[1,_3k[1],new T(function(){return B(_3h(_3i,_3k[2]));})]];},_3l=function(_3m,_3n,_3o,_3p,_3q,_3r,_3s,_3t){var _3u=E(_3t);if(!_3u[0]){return new F(function(){return _1r(_3u[1]);});}else{var _3v=B(_3d(function(_3w){return new F(function(){return _2W(_3m,_3n,_3o,_3q,_3p,_3r,_3s,_3w);});},_3u[1]));return _3v[0]==0?[0]:B(_3a([1,_3v[1],new T(function(){return B(_3h(_1q,_3v[2]));})]));}},_3x=function(_3y,_3z){while(1){var _3A=E(_3y);if(!_3A[0]){return E(_3z)[0]==0?true:false;}else{var _3B=E(_3z);if(!_3B[0]){return false;}else{if(E(_3A[1])[1]!=E(_3B[1])[1]){return false;}else{_3y=_3A[2];_3z=_3B[2];continue;}}}}},_3C=function(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K,_3L){return new F(function(){return _3x(B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K)),B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3L)));});},_3M=function(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V){return !B(_3C(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V))?true:false;},_3W=function(_3X,_3Y,_3Z,_40,_41,_42,_43){return [0,function(_44,_45){return new F(function(){return _3C(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});},function(_44,_45){return new F(function(){return _3M(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});}];},_46=new T(function(){return B(unCStr("wheel"));}),_47=new T(function(){return B(unCStr("mouseout"));}),_48=new T(function(){return B(unCStr("mouseover"));}),_49=new T(function(){return B(unCStr("mousemove"));}),_4a=new T(function(){return B(unCStr("blur"));}),_4b=new T(function(){return B(unCStr("focus"));}),_4c=new T(function(){return B(unCStr("change"));}),_4d=new T(function(){return B(unCStr("unload"));}),_4e=new T(function(){return B(unCStr("load"));}),_4f=new T(function(){return B(unCStr("submit"));}),_4g=new T(function(){return B(unCStr("keydown"));}),_4h=new T(function(){return B(unCStr("keyup"));}),_4i=new T(function(){return B(unCStr("keypress"));}),_4j=new T(function(){return B(unCStr("mouseup"));}),_4k=new T(function(){return B(unCStr("mousedown"));}),_4l=new T(function(){return B(unCStr("dblclick"));}),_4m=new T(function(){return B(unCStr("click"));}),_4n=function(_4o){switch(E(_4o)[0]){case 0:return E(_4e);case 1:return E(_4d);case 2:return E(_4c);case 3:return E(_4b);case 4:return E(_4a);case 5:return E(_49);case 6:return E(_48);case 7:return E(_47);case 8:return E(_4m);case 9:return E(_4l);case 10:return E(_4k);case 11:return E(_4j);case 12:return E(_4i);case 13:return E(_4h);case 14:return E(_4g);case 15:return E(_4f);default:return E(_46);}},_4p=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_4q=new T(function(){return B(unCStr("main"));}),_4r=new T(function(){return B(unCStr("EventData"));}),_4s=new T(function(){var _4t=hs_wordToWord64(3703396926),_4u=_4t,_4v=hs_wordToWord64(1660403598),_4w=_4v;return [0,_4u,_4w,[0,_4u,_4w,_4q,_4p,_4r],_9];}),_4x=[0,0],_4y=false,_4z=2,_4A=[1],_4B=new T(function(){return B(unCStr("Dynamic"));}),_4C=new T(function(){return B(unCStr("Data.Dynamic"));}),_4D=new T(function(){return B(unCStr("base"));}),_4E=new T(function(){var _4F=hs_wordToWord64(628307645),_4G=_4F,_4H=hs_wordToWord64(949574464),_4I=_4H;return [0,_4G,_4I,[0,_4G,_4I,_4D,_4C,_4B],_9];}),_4J=[0],_4K=new T(function(){return B(unCStr("OnLoad"));}),_4L=[0,_4K,_4J],_4M=[0,_4s,_4L],_4N=[0,_4E,_4M],_4O=[0],_4P=function(_){return _4O;},_4Q=function(_4R,_){return _4O;},_4S=[0,_4P,_4Q],_4T=[0,_9,_4x,_4z,_4S,_4y,_4N,_4A],_4U=function(_){var _=0,_4V=newMVar(),_4W=_4V,_=putMVar(_4W,_4T);return [0,_4W];},_4X=function(_4Y){var _4Z=B(A(_4Y,[_])),_50=_4Z;return E(_50);},_51=new T(function(){return B(_4X(_4U));}),_52=new T(function(){return B(_2L("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_53=[0,_4e,_4J],_54=[0,_4s,_53],_55=[0,_4d,_4J],_56=[0,_4s,_55],_57=[0,_4c,_4J],_58=[0,_4s,_57],_59=[0,_4b,_4J],_5a=[0,_4s,_59],_5b=[0,_4a,_4J],_5c=[0,_4s,_5b],_5d=[3],_5e=[0,_47,_5d],_5f=[0,_4s,_5e],_5g=function(_5h,_5i){switch(E(_5h)[0]){case 0:return function(_){var _5j=E(_51)[1],_5k=takeMVar(_5j),_5l=_5k,_=putMVar(_5j,new T(function(){var _5m=E(_5l);return [0,_5m[1],_5m[2],_5m[3],_5m[4],_5m[5],_54,_5m[7]];}));return new F(function(){return A(_5i,[_]);});};case 1:return function(_){var _5n=E(_51)[1],_5o=takeMVar(_5n),_5p=_5o,_=putMVar(_5n,new T(function(){var _5q=E(_5p);return [0,_5q[1],_5q[2],_5q[3],_5q[4],_5q[5],_56,_5q[7]];}));return new F(function(){return A(_5i,[_]);});};case 2:return function(_){var _5r=E(_51)[1],_5s=takeMVar(_5r),_5t=_5s,_=putMVar(_5r,new T(function(){var _5u=E(_5t);return [0,_5u[1],_5u[2],_5u[3],_5u[4],_5u[5],_58,_5u[7]];}));return new F(function(){return A(_5i,[_]);});};case 3:return function(_){var _5v=E(_51)[1],_5w=takeMVar(_5v),_5x=_5w,_=putMVar(_5v,new T(function(){var _5y=E(_5x);return [0,_5y[1],_5y[2],_5y[3],_5y[4],_5y[5],_5a,_5y[7]];}));return new F(function(){return A(_5i,[_]);});};case 4:return function(_){var _5z=E(_51)[1],_5A=takeMVar(_5z),_5B=_5A,_=putMVar(_5z,new T(function(){var _5C=E(_5B);return [0,_5C[1],_5C[2],_5C[3],_5C[4],_5C[5],_5c,_5C[7]];}));return new F(function(){return A(_5i,[_]);});};case 5:return function(_5D){return function(_){var _5E=E(_51)[1],_5F=takeMVar(_5E),_5G=_5F,_=putMVar(_5E,new T(function(){var _5H=E(_5G);return [0,_5H[1],_5H[2],_5H[3],_5H[4],_5H[5],[0,_4s,[0,_49,[2,E(_5D)]]],_5H[7]];}));return new F(function(){return A(_5i,[_]);});};};case 6:return function(_5I){return function(_){var _5J=E(_51)[1],_5K=takeMVar(_5J),_5L=_5K,_=putMVar(_5J,new T(function(){var _5M=E(_5L);return [0,_5M[1],_5M[2],_5M[3],_5M[4],_5M[5],[0,_4s,[0,_48,[2,E(_5I)]]],_5M[7]];}));return new F(function(){return A(_5i,[_]);});};};case 7:return function(_){var _5N=E(_51)[1],_5O=takeMVar(_5N),_5P=_5O,_=putMVar(_5N,new T(function(){var _5Q=E(_5P);return [0,_5Q[1],_5Q[2],_5Q[3],_5Q[4],_5Q[5],_5f,_5Q[7]];}));return new F(function(){return A(_5i,[_]);});};case 8:return function(_5R,_5S){return function(_){var _5T=E(_51)[1],_5U=takeMVar(_5T),_5V=_5U,_=putMVar(_5T,new T(function(){var _5W=E(_5V);return [0,_5W[1],_5W[2],_5W[3],_5W[4],_5W[5],[0,_4s,[0,_4m,[1,_5R,E(_5S)]]],_5W[7]];}));return new F(function(){return A(_5i,[_]);});};};case 9:return function(_5X,_5Y){return function(_){var _5Z=E(_51)[1],_60=takeMVar(_5Z),_61=_60,_=putMVar(_5Z,new T(function(){var _62=E(_61);return [0,_62[1],_62[2],_62[3],_62[4],_62[5],[0,_4s,[0,_4l,[1,_5X,E(_5Y)]]],_62[7]];}));return new F(function(){return A(_5i,[_]);});};};case 10:return function(_63,_64){return function(_){var _65=E(_51)[1],_66=takeMVar(_65),_67=_66,_=putMVar(_65,new T(function(){var _68=E(_67);return [0,_68[1],_68[2],_68[3],_68[4],_68[5],[0,_4s,[0,_4k,[1,_63,E(_64)]]],_68[7]];}));return new F(function(){return A(_5i,[_]);});};};case 11:return function(_69,_6a){return function(_){var _6b=E(_51)[1],_6c=takeMVar(_6b),_6d=_6c,_=putMVar(_6b,new T(function(){var _6e=E(_6d);return [0,_6e[1],_6e[2],_6e[3],_6e[4],_6e[5],[0,_4s,[0,_4j,[1,_69,E(_6a)]]],_6e[7]];}));return new F(function(){return A(_5i,[_]);});};};case 12:return function(_6f,_){var _6g=E(_51)[1],_6h=takeMVar(_6g),_6i=_6h,_=putMVar(_6g,new T(function(){var _6j=E(_6i);return [0,_6j[1],_6j[2],_6j[3],_6j[4],_6j[5],[0,_4s,[0,_4i,[4,_6f]]],_6j[7]];}));return new F(function(){return A(_5i,[_]);});};case 13:return function(_6k,_){var _6l=E(_51)[1],_6m=takeMVar(_6l),_6n=_6m,_=putMVar(_6l,new T(function(){var _6o=E(_6n);return [0,_6o[1],_6o[2],_6o[3],_6o[4],_6o[5],[0,_4s,[0,_4h,[4,_6k]]],_6o[7]];}));return new F(function(){return A(_5i,[_]);});};case 14:return function(_6p,_){var _6q=E(_51)[1],_6r=takeMVar(_6q),_6s=_6r,_=putMVar(_6q,new T(function(){var _6t=E(_6s);return [0,_6t[1],_6t[2],_6t[3],_6t[4],_6t[5],[0,_4s,[0,_4g,[4,_6p]]],_6t[7]];}));return new F(function(){return A(_5i,[_]);});};default:return E(_52);}},_6u=[0,_4n,_5g],_6v=function(_6w,_6x,_){var _6y=jsCreateTextNode(toJSStr(E(_6w))),_6z=_6y,_6A=jsAppendChild(_6z,E(_6x)[1]);return [0,_6z];},_6B=0,_6C=function(_6D,_6E,_6F,_6G){return new F(function(){return A(_6D,[function(_){var _6H=jsSetAttr(E(_6E)[1],toJSStr(E(_6F)),toJSStr(E(_6G)));return _6B;}]);});},_6I=[0,112],_6J=function(_6K){var _6L=new T(function(){return E(E(_6K)[2]);});return function(_6M,_){return [0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_6L)[1],_9)),new T(function(){return E(E(_6K)[1]);},1)));})],new T(function(){var _6N=E(_6K);return [0,_6N[1],new T(function(){return [0,E(_6L)[1]+1|0];}),_6N[3],_6N[4],_6N[5],_6N[6],_6N[7]];})];};},_6O=new T(function(){return B(unCStr("id"));}),_6P=function(_6Q){return E(_6Q);},_6R=new T(function(){return B(unCStr("noid"));}),_6S=function(_6T,_){return _6T;},_6U=function(_6V,_6W,_){var _6X=jsFind(toJSStr(E(_6W))),_6Y=_6X,_6Z=E(_6Y);if(!_6Z[0]){var _70=E(_51)[1],_71=takeMVar(_70),_72=_71,_73=B(A(_6V,[_72,_])),_74=_73,_75=E(_74),_=putMVar(_70,_75[2]);return E(_75[1])[2];}else{var _76=E(_6Z[1]),_77=jsClearChildren(_76[1]),_78=E(_51)[1],_79=takeMVar(_78),_7a=_79,_7b=B(A(_6V,[_7a,_])),_7c=_7b,_7d=E(_7c),_7e=E(_7d[1]),_=putMVar(_78,_7d[2]),_7f=B(A(_7e[1],[_76,_])),_7g=_7f;return _7e[2];}},_7h=new T(function(){return B(unCStr("span"));}),_7i=function(_7j,_7k,_7l,_){var _7m=jsCreateElem(toJSStr(E(_7h))),_7n=_7m,_7o=jsAppendChild(_7n,E(_7l)[1]),_7p=[0,_7n],_7q=B(A(_7j,[_7k,_7p,_])),_7r=_7q;return _7p;},_7s=function(_7t){return E(_7t);},_7u=function(_7v,_7w,_7x,_){var _7y=B(A(_6J,[_7x,_7x,_])),_7z=_7y,_7A=E(_7z),_7B=_7A[1],_7C=E(_7A[2]),_7D=_7C[2],_7E=E(_7C[4]),_7F=B(A(_7v,[[0,_7C[1],_7D,_7C[3],[0,function(_){return new F(function(){return _6U(function(_7G,_){var _7H=B(A(_7v,[new T(function(){var _7I=E(_7G);return [0,_7I[1],_7D,_7I[3],_7I[4],_7I[5],_7I[6],_7I[7]];}),_])),_7J=_7H;return [0,[0,_6S,E(E(_7J)[1])[2]],_7G];},_6R,_);});},function(_7K,_){var _7L=B(_6U(new T(function(){return B(A(_7w,[_7K]));},1),_7B,_)),_7M=_7L,_7N=E(_7M);return _7N[0]==0?_4O:B(A(_7E[2],[_7N[1],_]));}],_7C[5],_7C[6],_7C[7]],_])),_7O=_7F,_7P=E(_7O),_7Q=_7P[2],_7R=E(_7P[1]),_7S=_7R[1],_7T=E(_7R[2]);if(!_7T[0]){return [0,[0,function(_7U,_){var _7V=B(A(_7S,[_7U,_])),_7W=_7V;if(!E(E(_7x)[5])){var _7X=B(_7i(_7s,_6S,_7U,_)),_7Y=_7X,_7Z=B(A(_6C,[_6P,_7Y,_6O,_7B,_])),_80=_7Z;return _7U;}else{return _7U;}},_4O],new T(function(){var _81=E(_7Q);return [0,_81[1],_81[2],_81[3],_7E,_81[5],_81[6],_81[7]];})];}else{var _82=B(A(_7w,[_7T[1],new T(function(){var _83=E(_7Q);return [0,_83[1],_83[2],_83[3],_7E,_83[5],_83[6],_83[7]];}),_])),_84=_82,_85=E(_84),_86=E(_85[1]),_87=_86[1];return [0,[0,function(_88,_){var _89=B(A(_7S,[_88,_])),_8a=_89;if(!E(E(_7x)[5])){var _8b=B(_7i(_7s,_87,_88,_)),_8c=_8b,_8d=B(A(_6C,[_6P,_8c,_6O,_7B,_])),_8e=_8d;return _88;}else{var _8f=B(A(_87,[_88,_])),_8g=_8f;return _88;}},_86[2]],_85[2]];}},_8h=function(_8i,_8j){switch(E(_8i)[0]){case 0:switch(E(_8j)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_8j)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_8j)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_8j)[0]==3?1:2;}},_8k=new T(function(){return B(unCStr("end of input"));}),_8l=new T(function(){return B(unCStr("unexpected"));}),_8m=new T(function(){return B(unCStr("expecting"));}),_8n=new T(function(){return B(unCStr("unknown parse error"));}),_8o=new T(function(){return B(unCStr("or"));}),_8p=[0,58],_8q=[0,34],_8r=[0,41],_8s=[1,_8r,_9],_8t=function(_8u,_8v,_8w){var _8x=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_8v,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_8w,_9)),_8s));})));},1)));})));}),_8y=E(_8u);return _8y[0]==0?E(_8x):[1,_8q,new T(function(){return B(_e(_8y,new T(function(){return B(unAppCStr("\" ",_8x));},1)));})];},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C[0]){return E(_8B)[0]==0?true:false;}else{var _8D=E(_8B);if(!_8D[0]){return false;}else{if(E(_8C[1])[1]!=E(_8D[1])[1]){return false;}else{_8A=_8C[2];_8B=_8D[2];continue;}}}}},_8E=function(_8F,_8G){return !B(_8z(_8F,_8G))?true:false;},_8H=[0,_8z,_8E],_8I=function(_8J,_8K,_8L){var _8M=E(_8L);if(!_8M[0]){return E(_8K);}else{return new F(function(){return _e(_8K,new T(function(){return B(_e(_8J,new T(function(){return B(_8I(_8J,_8M[1],_8M[2]));},1)));},1));});}},_8N=function(_8O){return E(_8O)[0]==0?false:true;},_8P=new T(function(){return B(unCStr(", "));}),_8Q=function(_8R){var _8S=E(_8R);if(!_8S[0]){return [0];}else{return new F(function(){return _e(_8S[1],new T(function(){return B(_8Q(_8S[2]));},1));});}},_8T=function(_8U,_8V){while(1){var _8W=(function(_8X,_8Y){var _8Z=E(_8Y);if(!_8Z[0]){return [0];}else{var _90=_8Z[1],_91=_8Z[2];if(!B(A(_8X,[_90]))){var _92=_8X;_8V=_91;_8U=_92;return null;}else{return [1,_90,new T(function(){return B(_8T(_8X,_91));})];}}})(_8U,_8V);if(_8W!=null){return _8W;}}},_93=function(_94,_95){var _96=E(_95);return _96[0]==0?[0]:[1,_94,new T(function(){return B(_93(_96[1],_96[2]));})];},_97=function(_98,_99){while(1){var _9a=E(_99);if(!_9a[0]){return E(_98);}else{_98=_9a[1];_99=_9a[2];continue;}}},_9b=function(_9c){switch(E(_9c)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_9d=function(_9e){return E(_9e)[0]==1?true:false;},_9f=function(_9g){return E(_9g)[0]==2?true:false;},_9h=[0,10],_9i=[1,_9h,_9],_9j=function(_9k){return new F(function(){return _e(_9i,_9k);});},_9l=[0,32],_9m=function(_9n){var _9o=E(_9n);switch(_9o[0]){case 0:return E(_9o[1]);case 1:return E(_9o[1]);case 2:return E(_9o[1]);default:return E(_9o[1]);}},_9p=function(_9q){return E(E(_9q)[1]);},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v[0]){return false;}else{if(!B(A(_9p,[_9s,_9t,_9v[1]]))){_9u=_9v[2];continue;}else{return true;}}}},_9w=function(_9x,_9y){var _9z=function(_9A,_9B){while(1){var _9C=(function(_9D,_9E){var _9F=E(_9D);if(!_9F[0]){return [0];}else{var _9G=_9F[1],_9H=_9F[2];if(!B(_9r(_9x,_9G,_9E))){return [1,_9G,new T(function(){return B(_9z(_9H,[1,_9G,_9E]));})];}else{_9A=_9H;var _9I=_9E;_9B=_9I;return null;}}})(_9A,_9B);if(_9C!=null){return _9C;}}};return new F(function(){return _9z(_9y,_9);});},_9J=function(_9K,_9L,_9M,_9N,_9O,_9P){var _9Q=E(_9P);if(!_9Q[0]){return E(_9L);}else{var _9R=new T(function(){var _9S=B(_2q(_9b,_9Q));return [0,_9S[1],_9S[2]];}),_9T=new T(function(){var _9U=B(_2q(_9d,E(_9R)[2]));return [0,_9U[1],_9U[2]];}),_9V=new T(function(){return E(E(_9T)[1]);}),_9W=function(_9X,_9Y){var _9Z=E(_9Y);if(!_9Z[0]){return E(_9X);}else{var _a0=new T(function(){return B(_e(_9K,[1,_9l,new T(function(){return B(_97(_9X,_9Z));})]));}),_a1=B(_9w(_8H,B(_8T(_8N,B(_93(_9X,_9Z))))));if(!_a1[0]){return new F(function(){return _e(_9,[1,_9l,_a0]);});}else{var _a2=_a1[1],_a3=E(_a1[2]);if(!_a3[0]){return new F(function(){return _e(_a2,[1,_9l,_a0]);});}else{return new F(function(){return _e(B(_e(_a2,new T(function(){return B(_e(_8P,new T(function(){return B(_8I(_8P,_a3[1],_a3[2]));},1)));},1))),[1,_9l,_a0]);});}}}},_a4=function(_a5,_a6){var _a7=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_a6))))));if(!_a7[0]){return [0];}else{var _a8=_a7[1],_a9=_a7[2],_aa=E(_a5);return _aa[0]==0?B(_9W(_a8,_a9)):B(_e(_aa,[1,_9l,new T(function(){return B(_9W(_a8,_a9));})]));}},_ab=new T(function(){var _ac=B(_2q(_9f,E(_9T)[2]));return [0,_ac[1],_ac[2]];});return new F(function(){return _8Q(B(_3d(_9j,B(_9w(_8H,B(_8T(_8N,[1,new T(function(){if(!E(_9V)[0]){var _ad=E(E(_9R)[1]);if(!_ad[0]){var _ae=[0];}else{var _af=E(_ad[1]);switch(_af[0]){case 0:var _ag=E(_af[1]),_ah=_ag[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ag]));break;case 1:var _ai=E(_af[1]),_ah=_ai[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ai]));break;case 2:var _aj=E(_af[1]),_ah=_aj[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_aj]));break;default:var _ak=E(_af[1]),_ah=_ak[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ak]));}var _ae=_ah;}var _al=_ae,_am=_al;}else{var _am=[0];}return _am;}),[1,new T(function(){return B(_a4(_9N,_9V));}),[1,new T(function(){return B(_a4(_9M,E(_ab)[1]));}),[1,new T(function(){return B((function(_an){var _ao=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_an))))));return _ao[0]==0?[0]:B(_9W(_ao[1],_ao[2]));})(E(_ab)[2]));}),_9]]]])))))));});}},_ap=[1,_9,_9],_aq=function(_ar,_as){var _at=function(_au,_av){var _aw=E(_au);if(!_aw[0]){return E(_av);}else{var _ax=_aw[1],_ay=E(_av);if(!_ay[0]){return E(_aw);}else{var _az=_ay[1];return B(A(_ar,[_ax,_az]))==2?[1,_az,new T(function(){return B(_at(_aw,_ay[2]));})]:[1,_ax,new T(function(){return B(_at(_aw[2],_ay));})];}}},_aA=function(_aB){var _aC=E(_aB);if(!_aC[0]){return [0];}else{var _aD=E(_aC[2]);return _aD[0]==0?E(_aC):[1,new T(function(){return B(_at(_aC[1],_aD[1]));}),new T(function(){return B(_aA(_aD[2]));})];}},_aE=function(_aF){while(1){var _aG=E(_aF);if(!_aG[0]){return E(new T(function(){return B(_aE(B(_aA(_9))));}));}else{if(!E(_aG[2])[0]){return E(_aG[1]);}else{_aF=B(_aA(_aG));continue;}}}},_aH=new T(function(){return B(_aI(_9));}),_aI=function(_aJ){var _aK=E(_aJ);if(!_aK[0]){return E(_ap);}else{var _aL=_aK[1],_aM=E(_aK[2]);if(!_aM[0]){return [1,_aK,_9];}else{var _aN=_aM[1],_aO=_aM[2];if(B(A(_ar,[_aL,_aN]))==2){return new F(function(){return (function(_aP,_aQ,_aR){while(1){var _aS=(function(_aT,_aU,_aV){var _aW=E(_aV);if(!_aW[0]){return [1,[1,_aT,_aU],_aH];}else{var _aX=_aW[1];if(B(A(_ar,[_aT,_aX]))==2){_aP=_aX;var _aY=[1,_aT,_aU];_aR=_aW[2];_aQ=_aY;return null;}else{return [1,[1,_aT,_aU],new T(function(){return B(_aI(_aW));})];}}})(_aP,_aQ,_aR);if(_aS!=null){return _aS;}}})(_aN,[1,_aL,_9],_aO);});}else{return new F(function(){return (function(_aZ,_b0,_b1){while(1){var _b2=(function(_b3,_b4,_b5){var _b6=E(_b5);if(!_b6[0]){return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),_aH];}else{var _b7=_b6[1],_b8=_b6[2];switch(B(A(_ar,[_b3,_b7]))){case 0:_aZ=_b7;_b0=function(_b9){return new F(function(){return A(_b4,[[1,_b3,_b9]]);});};_b1=_b8;return null;case 1:_aZ=_b7;_b0=function(_ba){return new F(function(){return A(_b4,[[1,_b3,_ba]]);});};_b1=_b8;return null;default:return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),new T(function(){return B(_aI(_b6));})];}}})(_aZ,_b0,_b1);if(_b2!=null){return _b2;}}})(_aN,function(_bb){return [1,_aL,_bb];},_aO);});}}}};return new F(function(){return _aE(B(_aI(_as)));});},_bc=function(_bd,_be,_bf,_bg){return new F(function(){return _e(B(_8t(_bd,_be,_bf)),[1,_8p,new T(function(){return B(_9J(_8o,_8n,_8m,_8l,_8k,B(_aq(_8h,_bg))));})]);});},_bh=function(_bi){var _bj=E(_bi),_bk=E(_bj[1]);return new F(function(){return _bc(_bk[1],_bk[2],_bk[3],_bj[2]);});},_bl=function(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bt,_bu){return new F(function(){return _23(function(_bv,_bw){return new F(function(){return _e(B(_3l(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bv)),_bw);});},_bt,_bu);});},_bx=function(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bF,_bG,_bH){return new F(function(){return _e(B(_3l(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bG)),_bH);});},_bI=function(_bJ,_bK,_bL,_bM,_bN,_bO,_bP){return [0,function(_bQ,_44,_45){return new F(function(){return _bx(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_bQ,_44,_45);});},function(_45){return new F(function(){return _3l(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_45);});},function(_44,_45){return new F(function(){return _bl(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_44,_45);});}];},_bR=new T(function(){return B(unCStr(" \u2234 "));}),_bS=new T(function(){return B(unCStr(" . "));}),_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW,_bX,_bY,_bZ){var _c0=B(_3d(new T(function(){return B(_bT(_bW));}),B(_9w(_bX,_bY))));if(!_c0[0]){return new F(function(){return _e(_bR,new T(function(){return B(A(_bT,[_bW,_bZ]));},1));});}else{return new F(function(){return _e(B(_3a([1,_c0[1],new T(function(){return B(_3h(_bS,_c0[2]));})])),new T(function(){return B(_e(_bR,new T(function(){return B(A(_bT,[_bW,_bZ]));},1)));},1));});}},_c1=function(_c2,_c3,_c4){while(1){var _c5=E(_c3);if(!_c5[0]){return E(_c4)[0]==0?true:false;}else{var _c6=E(_c4);if(!_c6[0]){return false;}else{if(!B(A(_9p,[_c2,_c5[1],_c6[1]]))){return false;}else{_c3=_c5[2];_c4=_c6[2];continue;}}}}},_c7=function(_c8,_c9,_ca){var _cb=E(_c9),_cc=E(_ca);return !B(_c1(_c8,_cb[1],_cc[1]))?true:!B(A(_9p,[_c8,_cb[2],_cc[2]]))?true:false;},_cd=function(_ce,_cf,_cg,_ch,_ci){return !B(_c1(_ce,_cf,_ch))?false:B(A(_9p,[_ce,_cg,_ci]));},_cj=function(_ck,_cl,_cm){var _cn=E(_cl),_co=E(_cm);return new F(function(){return _cd(_ck,_cn[1],_cn[2],_co[1],_co[2]);});},_cp=function(_cq){return [0,function(_cr,_cs){return new F(function(){return _cj(_cq,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _c7(_cq,_cr,_cs);});}];},_ct=function(_cu,_cv,_cw){var _cx=E(_cv),_cy=E(_cw);return !B(_c1(_cu,_cx[1],_cy[1]))?true:!B(A(_9p,[_cu,_cx[2],_cy[2]]))?true:false;},_cz=function(_cA,_cB,_cC){var _cD=E(_cB),_cE=E(_cC);return new F(function(){return _cd(_cA,_cD[1],_cD[2],_cE[1],_cE[2]);});},_cF=function(_cG){return [0,function(_cr,_cs){return new F(function(){return _cz(_cG,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _ct(_cG,_cr,_cs);});}];},_cH=function(_cI,_cJ,_cK){var _cL=E(_cI);switch(_cL[0]){case 0:var _cM=E(_cJ);return _cM[0]==0?!B(_3x(_cL[3],_cM[3]))?[0]:[1,_cK]:[0];case 1:var _cN=E(_cJ);return _cN[0]==1?!B(_3x(_cL[3],_cN[3]))?[0]:[1,_cK]:[0];case 2:var _cO=E(_cJ);return _cO[0]==2?!B(_3x(_cL[3],_cO[3]))?[0]:[1,_cK]:[0];case 3:var _cP=E(_cJ);return _cP[0]==3?!B(_3x(_cL[3],_cP[3]))?[0]:[1,_cK]:[0];case 4:var _cQ=E(_cJ);return _cQ[0]==4?!B(_3x(_cL[3],_cQ[3]))?[0]:[1,_cK]:[0];case 5:var _cR=E(_cJ);return _cR[0]==5?!B(_3x(_cL[3],_cR[3]))?[0]:[1,_cK]:[0];case 6:var _cS=E(_cJ);return _cS[0]==6?!B(_3x(_cL[3],_cS[3]))?[0]:[1,_cK]:[0];case 7:var _cT=E(_cJ);return _cT[0]==7?!B(_3x(_cL[3],_cT[3]))?[0]:[1,_cK]:[0];case 8:var _cU=E(_cJ);return _cU[0]==8?!B(_3x(_cL[3],_cU[3]))?[0]:[1,_cK]:[0];default:var _cV=E(_cJ);return _cV[0]==9?!B(_3x(_cL[3],_cV[3]))?[0]:[1,_cK]:[0];}},_cW=new T(function(){return B(_2L("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_cX=function(_cY,_cZ,_d0){return [5,_,_cY,_cZ,_d0];},_d1=function(_d2,_d3,_d4){return [10,_,_d2,_d3,_d4];},_d5=function(_d6,_d7,_d8){return [6,_,_d6,_d7,_d8];},_d9=function(_da,_db){return [12,_,_da,_db];},_dc=function(_dd,_de){return [3,_,_dd,_de];},_df=function(_dg,_dh){return [8,_,_dg,_dh];},_di=function(_dj,_dk){return [4,_,_dj,_dk];},_dl=function(_dm,_dn,_do){while(1){var _dp=E(_do);if(!_dp[0]){return [0];}else{var _dq=E(_dp[1]),_dr=B(A(_dm,[_dn,_dq[2],_dq[3]]));if(!_dr[0]){_do=_dp[2];continue;}else{return E(_dr);}}}},_ds=function(_dt,_du){while(1){var _dv=(function(_dw,_dx){var _dy=E(_dx);switch(_dy[0]){case 2:var _dz=B(_dl(_cH,_dy[2],_dw));if(!_dz[0]){return E(_dy);}else{var _dA=_dw;_du=_dz[1];_dt=_dA;return null;}break;case 4:var _dB=_dy[3],_dC=B(_dl(_cH,_dy[2],_dw));if(!_dC[0]){return E(_dy);}else{var _dD=E(_dC[1]);switch(_dD[0]){case 3:return E(_dD[3])[0]==0?B(_dc(_dD[2],_dB)):E(_dy);case 4:if(!E(_dD[3])[0]){var _dA=_dw;_du=B(_di(_dD[2],_dB));_dt=_dA;return null;}else{return E(_dy);}break;default:return E(_dy);}}break;case 6:var _dE=_dy[3],_dF=_dy[4],_dG=B(_dl(_cH,_dy[2],_dw));if(!_dG[0]){return E(_dy);}else{var _dH=E(_dG[1]);switch(_dH[0]){case 5:if(!E(_dH[3])[0]){if(!E(_dH[4])[0]){var _dA=_dw;_du=B(_cX(_dH[2],_dE,_dF));_dt=_dA;return null;}else{return E(_dy);}}else{return E(_dy);}break;case 6:if(!E(_dH[3])[0]){if(!E(_dH[4])[0]){var _dA=_dw;_du=B(_d5(_dH[2],_dE,_dF));_dt=_dA;return null;}else{return E(_dy);}}else{return E(_dy);}break;default:return E(_dy);}}break;case 7:return [7,_,_dy[2],new T(function(){return B(_ds(_dw,_dy[3]));})];case 8:var _dI=_dy[2],_dJ=_dy[3],_dK=B(_dl(_cH,_dI,_dw));if(!_dK[0]){return [8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];}else{var _dL=E(_dK[1]);switch(_dL[0]){case 7:return E(_dL[3])[0]==0?[7,_,_dL[2],new T(function(){return B(_ds(_dw,_dJ));})]:[8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];case 8:if(!E(_dL[3])[0]){var _dA=_dw;_du=B(_df(_dL[2],_dJ));_dt=_dA;return null;}else{return [8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];}break;default:return [8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];}}break;case 9:return [9,_,_dy[2],new T(function(){return B(_ds(_dw,_dy[3]));}),new T(function(){return B(_ds(_dw,_dy[4]));})];case 10:var _dM=_dy[2],_dN=_dy[3],_dO=_dy[4],_dP=B(_dl(_cH,_dM,_dw));if(!_dP[0]){return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}else{var _dQ=E(_dP[1]);switch(_dQ[0]){case 9:if(!E(_dQ[3])[0]){if(!E(_dQ[4])[0]){var _dA=_dw;_du=[9,_,_dQ[2],new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];_dt=_dA;return null;}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}break;case 10:if(!E(_dQ[3])[0]){if(!E(_dQ[4])[0]){var _dA=_dw;_du=B(_d1(_dQ[2],_dN,_dO));_dt=_dA;return null;}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}break;default:return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}}break;case 11:return [11,_,_dy[2],function(_dR){return new F(function(){return _ds(_dw,B(A(_dy[3],[_dR])));});}];case 12:var _dS=_dy[2],_dT=_dy[3],_dU=B(_dl(_cH,_dS,_dw));if(!_dU[0]){return [12,_,_dS,function(_dV){return new F(function(){return _ds(_dw,B(A(_dT,[_dV])));});}];}else{var _dW=E(_dU[1]);switch(_dW[0]){case 11:return [11,_,_dW[2],function(_dX){return new F(function(){return _ds(_dw,B(A(_dT,[_dX])));});}];case 12:var _dA=_dw;_du=B(_d9(_dW[2],_dT));_dt=_dA;return null;default:return [12,_,_dS,function(_dY){return new F(function(){return _ds(_dw,B(A(_dT,[_dY])));});}];}}break;default:return E(_dy);}})(_dt,_du);if(_dv!=null){return _dv;}}},_dZ=function(_e0,_e1){var _e2=E(_e1);if(!_e2[0]){var _e3=B(_dl(_cH,_e2[1],_e0));if(!_e3[0]){return E(_e2);}else{var _e4=E(_e3[1]);return _e4[0]==0?E(_cW):[1,new T(function(){return B(_3d(function(_e5){return new F(function(){return _ds(_e0,_e5);});},_e4[1]));})];}}else{return [1,new T(function(){return B(_3d(function(_e6){return new F(function(){return _ds(_e0,_e6);});},_e2[1]));})];}},_e7=function(_e8,_e9,_ea,_eb,_ec,_ed,_ee,_ef,_eg){var _eh=E(_eg);return [0,new T(function(){return B(_3d(function(_ei){return new F(function(){return _dZ(_ef,_ei);});},_eh[1]));}),new T(function(){return B(_dZ(_ef,_eh[2]));})];},_ej=function(_ek,_el,_em,_en,_eo,_ep,_eq,_er,_es){var _et=E(_es);return [0,new T(function(){return B(_3d(function(_eu){return new F(function(){return _e7(_ek,_el,_em,_en,_eo,_ep,_eq,_er,_eu);});},_et[1]));}),new T(function(){return B(_e7(_ek,_el,_em,_en,_eo,_ep,_eq,_er,_et[2]));})];},_ev=function(_ew){return E(E(_ew)[1]);},_ex=function(_ey,_ez){var _eA=E(_ez);return new F(function(){return A(_ev,[_eA[1],E(_ey)[2],_eA[2]]);});},_eB=function(_eC,_eD,_eE){var _eF=E(_eE);if(!_eF[0]){return [0];}else{var _eG=_eF[1],_eH=_eF[2];return !B(A(_eC,[_eD,_eG]))?[1,_eG,new T(function(){return B(_eB(_eC,_eD,_eH));})]:E(_eH);}},_eI=function(_eJ,_eK,_eL){while(1){var _eM=E(_eL);if(!_eM[0]){return false;}else{if(!B(A(_eJ,[_eK,_eM[1]]))){_eL=_eM[2];continue;}else{return true;}}}},_eN=function(_eO,_eP){var _eQ=function(_eR,_eS){while(1){var _eT=(function(_eU,_eV){var _eW=E(_eU);if(!_eW[0]){return [0];}else{var _eX=_eW[1],_eY=_eW[2];if(!B(_eI(_eO,_eX,_eV))){return [1,_eX,new T(function(){return B(_eQ(_eY,[1,_eX,_eV]));})];}else{_eR=_eY;var _eZ=_eV;_eS=_eZ;return null;}}})(_eR,_eS);if(_eT!=null){return _eT;}}};return new F(function(){return _eQ(_eP,_9);});},_f0=function(_f1,_f2,_f3){return new F(function(){return _e(_f2,new T(function(){return B((function(_f4,_f5){while(1){var _f6=E(_f5);if(!_f6[0]){return E(_f4);}else{var _f7=B(_eB(_f1,_f6[1],_f4));_f5=_f6[2];_f4=_f7;continue;}}})(B(_eN(_f1,_f3)),_f2));},1));});},_f8=function(_f9,_fa){while(1){var _fb=(function(_fc,_fd){var _fe=E(_fd);switch(_fe[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_fc,_fe[2]],_9];case 3:var _ff=_fc;_fa=_fe[3];_f9=_ff;return null;case 4:return new F(function(){return _f0(_ex,[1,[0,_fc,_fe[2]],_9],new T(function(){return B(_f8(_fc,_fe[3]));},1));});break;case 5:return new F(function(){return _f0(_ex,B(_f8(_fc,_fe[3])),new T(function(){return B(_f8(_fc,_fe[4]));},1));});break;default:return new F(function(){return _f0(_ex,B(_f0(_ex,[1,[0,_fc,_fe[2]],_9],new T(function(){return B(_f8(_fc,_fe[3]));},1))),new T(function(){return B(_f8(_fc,_fe[4]));},1));});}})(_f9,_fa);if(_fb!=null){return _fb;}}},_fg=function(_fh,_fi,_fj,_fk){while(1){var _fl=(function(_fm,_fn,_fo,_fp){var _fq=E(_fp);switch(_fq[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_fm,_fq[2]],_9];case 3:return new F(function(){return _f8(_fm,_fq[3]);});break;case 4:return new F(function(){return _f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_f8(_fm,_fq[3]));},1));});break;case 5:return new F(function(){return _f0(_ex,B(_f8(_fm,_fq[3])),new T(function(){return B(_f8(_fm,_fq[4]));},1));});break;case 6:return new F(function(){return _f0(_ex,B(_f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_f8(_fm,_fq[3]));},1))),new T(function(){return B(_f8(_fm,_fq[4]));},1));});break;case 7:var _fr=_fm,_fs=_fn,_ft=_fo;_fk=_fq[3];_fh=_fr;_fi=_fs;_fj=_ft;return null;case 8:return new F(function(){return _f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_fg(_fm,_fn,_fo,_fq[3]));},1));});break;case 9:return new F(function(){return _f0(_ex,B(_fg(_fm,_fn,_fo,_fq[3])),new T(function(){return B(_fg(_fm,_fn,_fo,_fq[4]));},1));});break;case 10:return new F(function(){return _f0(_ex,B(_f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_fg(_fm,_fn,_fo,_fq[3]));},1))),new T(function(){return B(_fg(_fm,_fn,_fo,_fq[4]));},1));});break;case 11:var _fr=_fm,_fs=_fn,_ft=_fo;_fk=B(A(_fq[3],[_2V]));_fh=_fr;_fi=_fs;_fj=_ft;return null;default:return new F(function(){return _f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_fg(_fm,_fn,_fo,B(A(_fq[3],[_2V]))));},1));});}})(_fh,_fi,_fj,_fk);if(_fl!=null){return _fl;}}},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=function(_fB){return new F(function(){return _fg(_fv,_fw,_fx,_fB);});};return new F(function(){return _e(B(_8Q(B(_3d(function(_fC){var _fD=E(_fC);if(!_fD[0]){return [1,[0,_fv,_fD[1]],_9];}else{return new F(function(){return _8Q(B(_3d(_fA,_fD[1])));});}},_fy)))),new T(function(){var _fE=E(_fz);if(!_fE[0]){var _fF=[1,[0,_fv,_fE[1]],_9];}else{var _fF=B(_8Q(B(_3d(_fA,_fE[1]))));}return _fF;},1));});},_fG=function(_fH,_fI,_fJ,_fK,_fL,_fM,_fN,_fO,_fP){var _fQ=E(_fP);return new F(function(){return _e(B(_8Q(B(_3d(function(_fR){var _fS=E(_fR);return new F(function(){return _fu(_fH,_fL,_fM,_fS[1],_fS[2]);});},_fQ[1])))),new T(function(){var _fT=E(_fQ[2]);return B(_fu(_fH,_fL,_fM,_fT[1],_fT[2]));},1));});},_fU=function(_fV,_fW,_fX,_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5){return [0,_fV,_fW,_fX,_fY,function(_eu){return new F(function(){return _fG(_fV,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_eu);});},function(_g6,_eu){return new F(function(){return _ej(_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_eu);});}];},_g7=function(_g8){return E(E(_g8)[2]);},_g9=function(_ga){return E(E(_ga)[1]);},_gb=[0,_g9,_g7],_gc=new T(function(){return B(unCStr(" \u2234 "));}),_gd=function(_ge,_gf,_gg,_gh){return new F(function(){return _e(B(A(_gf,[_gg,_9])),new T(function(){return B(_e(_gc,new T(function(){return B(A(_ge,[_gh]));},1)));},1));});},_gi=function(_gj,_gk){var _gl=E(_gj),_gm=E(_gk);return new F(function(){return _gd(_gl[2],_gl[3],_gm[1],_gm[2]);});},_gn=function(_go,_gp,_gq,_gr,_gs){return new F(function(){return _e(B(A(_gp,[_gq,_9])),new T(function(){return B(_e(_gc,new T(function(){return B(_e(B(A(_go,[_gr])),_gs));},1)));},1));});},_gt=function(_gu,_gv,_gw){return new F(function(){return _23(function(_gx,_gy){var _gz=E(_gu),_gA=E(_gx);return new F(function(){return _gn(_gz[2],_gz[3],_gA[1],_gA[2],_gy);});},_gv,_gw);});},_gB=function(_gC,_gD,_gE,_gF){var _gG=E(_gC),_gH=E(_gE);return new F(function(){return _gn(_gG[2],_gG[3],_gH[1],_gH[2],_gF);});},_gI=function(_gJ){return [0,function(_gK,_cr,_cs){return new F(function(){return _gB(_gJ,_gK,_cr,_cs);});},function(_cs){return new F(function(){return _gi(_gJ,_cs);});},function(_cr,_cs){return new F(function(){return _gt(_gJ,_cr,_cs);});}];},_gL=new T(function(){return B(unCStr(", "));}),_gM=new T(function(){return B(unCStr(" \u22a2 "));}),_gN=new T(function(){return B(_8Q(_9));}),_gO=function(_gP,_gQ,_gR){var _gS=B(_3d(new T(function(){return B(_bT(_gP));}),_gQ));if(!_gS[0]){return new F(function(){return _e(_gN,new T(function(){return B(_e(_gM,new T(function(){return B(A(_bT,[_gP,_gR]));},1)));},1));});}else{return new F(function(){return _e(B(_8Q([1,_gS[1],new T(function(){return B(_3h(_gL,_gS[2]));})])),new T(function(){return B(_e(_gM,new T(function(){return B(A(_bT,[_gP,_gR]));},1)));},1));});}},_gT=function(_gU,_gV){var _gW=E(_gV);return new F(function(){return _gO(_gU,_gW[1],_gW[2]);});},_gX=function(_gY,_gZ,_h0){return new F(function(){return _23(function(_h1,_h2){var _h3=E(_h1);return new F(function(){return _e(B(_gO(_gY,_h3[1],_h3[2])),_h2);});},_gZ,_h0);});},_h4=function(_h5,_h6,_h7,_h8){var _h9=E(_h7);return new F(function(){return _e(B(_gO(_h5,_h9[1],_h9[2])),_h8);});},_ha=function(_hb){return [0,function(_gK,_cr,_cs){return new F(function(){return _h4(_hb,_gK,_cr,_cs);});},function(_cs){return new F(function(){return _gT(_hb,_cs);});},function(_cr,_cs){return new F(function(){return _gX(_hb,_cr,_cs);});}];},_hc=function(_hd,_he){return new F(function(){return _e(B(_1r(_hd)),_he);});},_hf=function(_hg,_hh){return new F(function(){return _23(_hc,_hg,_hh);});},_hi=function(_hj,_hk,_hl){return new F(function(){return _e(B(_1r(_hk)),_hl);});},_hm=[0,_hi,_1r,_hf],_hn=function(_ho,_hp,_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz){var _hA=E(_hz);return new F(function(){return _fu(_ho,_hv,_hw,_hA[1],_hA[2]);});},_hB=function(_hC,_hD,_hE,_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM){return [0,_hC,_hD,_hE,_hF,function(_eu){return new F(function(){return _hn(_hC,_hD,_hE,_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_eu);});},function(_g6,_eu){return new F(function(){return _e7(_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_g6,_eu);});}];},_hN=function(_hO,_hP){return [0];},_hQ=function(_hR,_hS,_hT,_hU,_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4){return [0,_hR,_hS,_hN,_1];},_i5=function(_i6,_i7,_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig,_ih){var _ii=E(_ih);if(!_ii[0]){return [1,[0,_i6,_ii[1]],_9];}else{return new F(function(){return _8Q(B(_3d(function(_ij){return new F(function(){return _fg(_i6,_id,_ie,_ij);});},_ii[1])));});}},_ik=function(_il,_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv){return [0,_il,_im,_in,_io,function(_eu){return new F(function(){return _i5(_il,_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv,_eu);});},_dZ];},_iw=function(_ix){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_ix));}))));});},_iy=new T(function(){return B(_iw("w_szYG{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r150}\n                  sv{tv azCV} [tv] quant{tv azCT} [tv]"));}),_iz=new T(function(){return B(_iw("w_szYF{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv azCT} [tv]"));}),_iA=new T(function(){return B(_iw("w_szYE{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv azCS} [tv]"));}),_iB=new T(function(){return B(_iw("w_szYD{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv azCV} [tv]"));}),_iC=new T(function(){return B(_iw("w_szYC{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv azCR} [tv]"));}),_iD=new T(function(){return B(_iw("w_szYB{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv azCU} [tv]"));}),_iE=new T(function(){return B(_iw("w_szYH{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14a}\n                  sv{tv azCV} [tv]"));}),_iF=new T(function(){return B(_iw("w_szYA{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv azCT} [tv]"));}),_iG=new T(function(){return B(_iw("w_szYz{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv azCS} [tv]"));}),_iH=new T(function(){return B(_iw("w_szYy{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv azCV} [tv]"));}),_iI=new T(function(){return B(_iw("w_szYx{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv azCR} [tv]"));}),_iJ=new T(function(){return B(_iw("w_szYw{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv azCU} [tv]"));}),_iK=function(_iL,_iM){return function(_iN,_iO){var _iP=E(_iN);return _iP[0]==0?[1,[0,new T(function(){return B(_iQ(_iL,_iM,_iJ,_iI,_iH,_iG,_iF,_iD,_iC,_iB,_iA,_iz,_iy,_iE));}),_iP[1],_iO]]:[0];};},_iR=function(_iS){return [0,E(_iS)];},_iQ=function(_iT,_iU,_iV,_iW,_iX,_iY,_iZ,_j0,_j1,_j2,_j3,_j4,_j5,_j6){return [0,_iT,_iU,new T(function(){return B(_iK(_iT,_iU));}),_iR];},_j7=[1,_9],_j8=function(_j9,_ja){while(1){var _jb=E(_j9);if(!_jb[0]){return E(_ja);}else{_j9=_jb[2];var _jc=_ja+1|0;_ja=_jc;continue;}}},_jd=[0,95],_je=[1,_jd,_9],_jf=[1,_je,_9],_jg=function(_jh,_ji,_jj){return !B(_3x(B(A(_jh,[_ji,_jf])),B(A(_jh,[_jj,_jf]))))?true:false;},_jk=function(_jl){return [0,function(_jm,_jn){return new F(function(){return _3x(B(A(_jl,[_jm,_jf])),B(A(_jl,[_jn,_jf])));});},function(_44,_45){return new F(function(){return _jg(_jl,_44,_45);});}];},_jo=function(_jp,_jq){return new F(function(){return _ds(_jp,_jq);});},_jr=function(_js,_jt,_ju,_jv,_jw,_jx,_jy,_jz,_jA,_jB,_jC){return [0,_js,_jt,_ju,_jv,function(_jD){return new F(function(){return _fg(_js,_jz,_jA,_jD);});},_jo];},_jE=new T(function(){return B(_iw("w_spMq{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r150}\n                  sv{tv amK9} [tv] quant{tv amK7} [tv]"));}),_jF=new T(function(){return B(_iw("w_spMp{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv amK7} [tv]"));}),_jG=new T(function(){return B(_iw("w_spMo{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv amK6} [tv]"));}),_jH=new T(function(){return B(_iw("w_spMn{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv amK9} [tv]"));}),_jI=new T(function(){return B(_iw("w_spMm{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv amK5} [tv]"));}),_jJ=new T(function(){return B(_iw("w_spMl{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv amK8} [tv]"));}),_jK=new T(function(){return B(_iw("w_spMr{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14a}\n                  sv{tv amK9} [tv]"));}),_jL=new T(function(){return B(_iw("w_spMk{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv amK7} [tv]"));}),_jM=new T(function(){return B(_iw("w_spMj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv amK6} [tv]"));}),_jN=new T(function(){return B(_iw("w_spMi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv amK9} [tv]"));}),_jO=new T(function(){return B(_iw("w_spMh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv amK5} [tv]"));}),_jP=new T(function(){return B(_iw("w_spMg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv amK8} [tv]"));}),_jQ=function(_jR,_jS,_jT,_jU){var _jV=E(_jT);switch(_jV[0]){case 2:return [1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_jV[2],_jU]];case 4:var _jX=_jV[2];if(!E(_jV[3])[0]){var _jY=E(_jU);switch(_jY[0]){case 3:return E(_jY[3])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_jX,_jY]]:[0];case 4:return E(_jY[3])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_jX,_jY]]:[0];default:return [0];}}else{return [0];}break;case 6:var _jZ=_jV[2];if(!E(_jV[3])[0]){if(!E(_jV[4])[0]){var _k0=E(_jU);switch(_k0[0]){case 5:return E(_k0[3])[0]==0?E(_k0[4])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_jZ,_k0]]:[0]:[0];case 6:return E(_k0[3])[0]==0?E(_k0[4])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_jZ,_k0]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _k1=_jV[2];if(!E(_jV[3])[0]){var _k2=E(_jU);switch(_k2[0]){case 7:return E(_k2[3])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_k1,_k2]]:[0];case 8:return E(_k2[3])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_k1,_k2]]:[0];default:return [0];}}else{return [0];}break;case 10:var _k3=_jV[2];if(!E(_jV[3])[0]){if(!E(_jV[4])[0]){var _k4=E(_jU);switch(_k4[0]){case 9:return E(_k4[3])[0]==0?E(_k4[4])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_k3,_k4]]:[0]:[0];case 10:return E(_k4[3])[0]==0?E(_k4[4])[0]==0?[1,[0,new T(function(){return B(_jW(_jR,_jS,_jP,_jO,_jN,_jM,_jL,_jJ,_jI,_jH,_jG,_jF,_jE,_jK));}),_k3,_k4]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_k5=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_k6=function(_k7){var _k8=E(_k7);switch(_k8[0]){case 3:return [2,_,_k8];case 4:return [4,_,_k8,_V];case 5:return [6,_,_k8,_V,_V];case 6:return [8,_,_k8,_S];case 7:return [10,_,_k8,_S,_S];default:return E(_k5);}},_jW=function(_k9,_ka,_kb,_kc,_kd,_ke,_kf,_kg,_kh,_ki,_kj,_kk,_kl,_km){return [0,_k9,_ka,function(_kn,_ko){return new F(function(){return _jQ(_k9,_ka,_kn,_ko);});},_k6];},_kp=function(_kq,_kr,_ks){return new F(function(){return _23(function(_kt,_ku){return new F(function(){return _e(B(A(_kq,[_kt,_jf])),_ku);});},_kr,_ks);});},_kv=function(_kw){return [0,function(_kx,_ky,_kz){return new F(function(){return _e(B(A(_kw,[_ky,_jf])),_kz);});},function(_kA){return new F(function(){return A(_kw,[_kA,_jf]);});},function(_44,_45){return new F(function(){return _kp(_kw,_44,_45);});}];},_kB=[1,_9],_kC=function(_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO){var _kP=E(_kN);if(_kP[0]==2){return E(_kB);}else{var _kQ=E(_kO);if(_kQ[0]==2){return E(_kB);}else{var _kR=function(_kS){var _kT=function(_kU){var _kV=function(_kW){var _kX=function(_kY){var _kZ=function(_l0){var _l1=function(_l2){var _l3=function(_l4){var _l5=function(_l6){var _l7=function(_l8){var _l9=function(_la){var _lb=function(_lc){var _ld=function(_le){var _lf=E(_kP);switch(_lf[0]){case 1:var _lg=E(_kQ);return _lg[0]==1?!B(A(_kE,[_lf[2],_lg[2]]))?[0]:E(_kB):[0];case 3:var _lh=E(_kQ);return _lh[0]==3?!B(A(_kD,[_lf[2],_lh[2]]))?[0]:E(_kB):[0];case 4:var _li=_lf[2],_lj=E(_kQ);switch(_lj[0]){case 3:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[4,_,_li,_V],[3,_,_lj[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[4,_,_li,_V],[4,_,_lj[2],_V]]));}),_9]];default:return [0];}break;case 5:var _ll=E(_kQ);return _ll[0]==5?!B(A(_kD,[_lf[2],_ll[2]]))?[0]:E(_kB):[0];case 6:var _lm=_lf[2],_ln=E(_kQ);switch(_ln[0]){case 5:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[6,_,_lm,_V,_V],[5,_,_ln[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[6,_,_lm,_V,_V],[6,_,_ln[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _lo=E(_kQ);return _lo[0]==7?!B(A(_kF,[_lf[2],_lo[2]]))?[0]:[1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lf[3],_lo[3]]));}),_9]]:[0];case 8:var _lp=_lf[2],_lq=_lf[3],_lr=E(_kQ);switch(_lr[0]){case 7:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[8,_,_lp,_S],[7,_,_lr[2],_S]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lq,_lr[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[8,_,_lp,_S],[8,_,_lr[2],_S]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lq,_lr[3]]));}),_9]]];default:return [0];}break;case 9:var _ls=E(_kQ);return _ls[0]==9?!B(A(_kF,[_lf[2],_ls[2]]))?[0]:[1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lf[3],_ls[3]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lf[4],_ls[4]]));}),_9]]]:[0];case 10:var _lt=_lf[2],_lu=_lf[3],_lv=_lf[4],_lw=function(_lx){var _ly=E(_kQ);switch(_ly[0]){case 9:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[10,_,_lt,_S,_S],[9,_,_ly[2],_S,_S]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lu,_ly[3]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lv,_ly[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,[10,_,_lt,_S,_S],[10,_,_ly[2],_S,_S]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lu,_ly[3]]));}),[1,new T(function(){return B(A(_lk,[_kD,_kE,_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_lv,_ly[4]]));}),_9]]]];default:return [0];}};return E(_lu)[0]==0?E(_lv)[0]==0?E(_kB):B(_lw(_)):B(_lw(_));default:return [0];}},_lz=E(_kQ);return _lz[0]==10?E(_lz[3])[0]==0?E(_lz[4])[0]==0?E(_kB):B(_ld(_)):B(_ld(_)):B(_ld(_));},_lA=E(_kP);return _lA[0]==8?E(_lA[3])[0]==0?E(_kB):B(_lb(_)):B(_lb(_));},_lB=E(_kQ);switch(_lB[0]){case 6:return E(_lB[3])[0]==0?E(_lB[4])[0]==0?E(_kB):B(_l9(_)):B(_l9(_));case 8:return E(_lB[3])[0]==0?E(_kB):B(_l9(_));default:return new F(function(){return _l9(_);});}},_lC=E(_kP);return _lC[0]==6?E(_lC[3])[0]==0?E(_lC[4])[0]==0?E(_kB):B(_l7(_)):B(_l7(_)):B(_l7(_));},_lD=E(_kQ);return _lD[0]==4?E(_lD[3])[0]==0?E(_kB):B(_l5(_)):B(_l5(_));},_lE=E(_kP);switch(_lE[0]){case 4:return E(_lE[3])[0]==0?E(_kB):B(_l3(_));case 9:return E(_lE[3])[0]==0?E(_lE[4])[0]==0?E(_kB):B(_l3(_)):B(_l3(_));default:return new F(function(){return _l3(_);});}},_lF=E(_kQ);return _lF[0]==9?E(_lF[3])[0]==0?E(_lF[4])[0]==0?E(_kB):B(_l1(_)):B(_l1(_)):B(_l1(_));},_lG=E(_kP);return _lG[0]==7?E(_lG[3])[0]==0?E(_kB):B(_kZ(_)):B(_kZ(_));},_lH=E(_kQ);switch(_lH[0]){case 5:return E(_lH[3])[0]==0?E(_lH[4])[0]==0?E(_kB):B(_kX(_)):B(_kX(_));case 7:return E(_lH[3])[0]==0?E(_kB):B(_kX(_));default:return new F(function(){return _kX(_);});}},_lI=E(_kP);return _lI[0]==5?E(_lI[3])[0]==0?E(_lI[4])[0]==0?E(_kB):B(_kV(_)):B(_kV(_)):B(_kV(_));},_lJ=E(_kQ);return _lJ[0]==3?E(_lJ[3])[0]==0?E(_kB):B(_kT(_)):B(_kT(_));},_lK=E(_kP);return _lK[0]==3?E(_lK[3])[0]==0?E(_kB):B(_kR(_)):B(_kR(_));}}},_lL=function(_lM,_lN,_lO){return [0,_lM,_lN,_lO];},_lP=new T(function(){return B(_iw("w_spMz{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv amJu} [tv]"));}),_lQ=new T(function(){return B(_iw("w_spMv{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv amJv} [tv]"));}),_lR=function(_lS){return [0,function(_lT,_lU){return B(A(_lS,[_lT,_lU,_1]))[0]==0?false:true;},function(_lV,_lW){return B(A(_lS,[_lV,_lW,_1]))[0]==0?true:false;}];},_lX=new T(function(){return B(_lR(_cH));}),_lk=function(_lY,_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_m6,_m7){var _m8=function(_m9,_ma){return new F(function(){return _2W(_m2,_m4,_m5,_m3,_m1,_m6,_m7,_m9);});};return function(_mb,_mc){return new F(function(){return _lL(new T(function(){return B(_jW(function(_md,_me){return new F(function(){return _kC(_lY,_lZ,_m0,_m1,_m2,_m3,_m4,_m5,_m6,_m7,_md,_me);});},new T(function(){return B(_jr(_lX,_hm,new T(function(){return B(_jk(_m8));}),new T(function(){return B(_kv(_m8));}),_m2,_m4,_m5,_m1,_m3,_m6,_m7));}),_lQ,_lY,_lZ,_m0,_lP,_m1,_m2,_m3,_m4,_m5,_m6,_m7));}),_mb,_mc);});};},_mf=function(_mg,_mh,_mi){var _mj=E(_mh);if(!_mj[0]){return [0];}else{var _mk=E(_mi);return _mk[0]==0?[0]:[1,new T(function(){return B(A(_mg,[_mj[1],_mk[1]]));}),new T(function(){return B(_mf(_mg,_mj[2],_mk[2]));})];}},_ml=function(_mm,_mn,_mo,_mp,_mq,_mr,_ms,_mt,_mu,_mv,_mw,_mx){var _my=E(_mw);if(!_my[0]){return E(_j7);}else{var _mz=_my[1],_mA=E(_mx);if(!_mA[0]){return E(_j7);}else{var _mB=_mA[1];return B(_j8(_mz,0))!=B(_j8(_mB,0))?[0]:[1,new T(function(){return B(_mf(new T(function(){return B(_lk(_mm,_mn,_mo,_mp,_mq,_mr,_ms,_mt,_mu,_mv));}),_mz,_mB));})];}}},_mC=new T(function(){return B(_iw("w_szZr{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv azCB} [tv]"));}),_mD=new T(function(){return B(_iw("w_szZv{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv azCA} [tv]"));}),_mE=new T(function(){return B(_lR(_cH));}),_mF=function(_mG,_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_mO,_mP){var _mQ=new T(function(){return B(_iQ(function(_mR,_mS){return new F(function(){return _ml(_mG,_mH,_mI,_mJ,_mK,_mL,_mM,_mN,_mO,_mP,_mR,_mS);});},new T(function(){return B(_ik(_mE,_hm,new T(function(){return B(_3W(_mK,_mM,_mN,_mJ,_mL,_mO,_mP));}),new T(function(){return B(_bI(_mK,_mM,_mN,_mJ,_mL,_mO,_mP));}),_mK,_mM,_mN,_mJ,_mL,_mO,_mP));}),_mC,_mG,_mH,_mI,_mD,_mJ,_mK,_mL,_mM,_mN,_mO,_mP));});return function(_mT,_mU){var _mV=E(_mT),_mW=_mV[1],_mX=E(_mU),_mY=_mX[1];return B(_j8(_mW,0))!=B(_j8(_mY,0))?[0]:[1,[1,[0,_mQ,_mV[2],_mX[2]],new T(function(){return B(_mf(function(_g6,_eu){return [0,_mQ,_g6,_eu];},_mW,_mY));})]];};},_mZ=new T(function(){return B(_iw("w_sA23{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv azC8} [tv]"));}),_n0=new T(function(){return B(_iw("w_sA27{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv azC7} [tv]"));}),_n1=function(_n2,_n3,_n4,_n5,_n6,_n7,_n8,_n9,_na,_nb){var _nc=new T(function(){return B(_hQ(new T(function(){return B(_mF(_n2,_n3,_n4,_n5,_n6,_n7,_n8,_n9,_na,_nb));}),new T(function(){return B(_hB(_mE,_hm,new T(function(){return B(_cF(new T(function(){return B(_3W(_n6,_n8,_n9,_n5,_n7,_na,_nb));})));}),new T(function(){return B(_ha(new T(function(){return B(_bI(_n6,_n8,_n9,_n5,_n7,_na,_nb));})));}),_n6,_n8,_n9,_n5,_n7,_na,_nb));}),_mZ,_n2,_n3,_n4,_n0,_n5,_n6,_n7,_n8,_n9,_na,_nb));});return function(_nd,_ne){var _nf=E(_nd),_ng=_nf[1],_nh=E(_ne),_ni=_nh[1];return B(_j8(_ng,0))!=B(_j8(_ni,0))?[0]:[1,[1,[0,_nc,_nf[2],_nh[2]],new T(function(){return B(_mf(function(_g6,_eu){return [0,_nc,_g6,_eu];},_ng,_ni));})]];};},_nj=function(_nk,_nl){while(1){var _nm=E(_nl);if(!_nm[0]){return false;}else{var _nn=E(_nm[1]);if(!B(A(_ev,[_nn[1],_nk,_nn[2]]))){_nl=_nm[2];continue;}else{return true;}}}},_no=[1,_9],_np=function(_nq,_nr,_ns,_nt,_nu,_nv,_nw,_nx,_ny,_nz,_nA){var _nB=E(_nt);return !B(A(_nB[1],[new T(function(){return B(A(_ny,[_nz]));}),_nA]))?!B(_nj(_nz,B(A(_nv,[_nA]))))?[1,[1,[0,[0,_nq,[0,_nr,_ns,_nB,_nu,_nv,_nw],_nx,_ny],_nz,_nA],_9]]:[0,[1,_,[0,_nq,[0,_nr,_ns,_nB,_nu,_nv,_nw],_nx,_ny],[3,_ns,_nu,_nz,_nA]]]:E(_no);},_nC=function(_nD){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(55,15)-(57,42)|case");});},_nE=new T(function(){return B(_nC(_));}),_nF=new T(function(){return B(unCStr(": empty list"));}),_nG=new T(function(){return B(unCStr("Prelude."));}),_nH=function(_nI){return new F(function(){return err(B(_e(_nG,new T(function(){return B(_e(_nI,_nF));},1))));});},_nJ=new T(function(){return B(unCStr("head"));}),_nK=new T(function(){return B(_nH(_nJ));}),_nL=function(_nM){return E(E(_nM)[2]);},_nN=function(_nO,_nP){while(1){var _nQ=E(_nO);if(!_nQ){return E(_nP);}else{var _nR=E(_nP);if(!_nR[0]){return [0];}else{_nO=_nQ-1|0;_nP=_nR[2];continue;}}}},_nS=function(_nT,_nU){var _nV=E(_nT)[1];return _nV>=0?B(_nN(_nV,_nU)):E(_nU);},_nW=function(_nX){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:97:31-64|function conc");});},_nY=new T(function(){return B(_nW(_));}),_nZ=function(_o0){var _o1=E(_o0);switch(_o1[0]){case 3:return [2,_,_o1];case 4:return [4,_,_o1,_V];case 5:return [6,_,_o1,_V,_V];case 6:return [8,_,_o1,_S];case 7:return [10,_,_o1,_S,_S];default:return E(_k5);}},_o2=function(_o3){var _o4=E(_o3);if(!_o4[0]){return [0];}else{var _o5=E(_o4[1]);if(!_o5[0]){return [0];}else{return new F(function(){return _e(_o5[1],new T(function(){return B(_o2(_o4[2]));},1));});}}},_o6=function(_o7){var _o8=E(_o7);return [0,[1,[1,new T(function(){return B(_o2(_o8[1]));})],_9],_o8[2]];},_o9=function(_oa,_ob,_oc){return !B(_9r(_oa,_ob,_oc))?E(_oc):[1,_ob,new T(function(){return B(_8T(function(_od){return !B(A(_9p,[_oa,_od,_ob]))?true:false;},_oc));})];},_oe=function(_of,_og,_oh,_oi,_oj,_ok,_ol){return function(_om,_on){var _oo=E(_om);if(!_oo[0]){return new F(function(){return _o6(_on);});}else{var _op=E(_on);return [0,[1,[1,new T(function(){return B(_o9(new T(function(){return B(_jk(function(_oq,_or){return new F(function(){return _2W(_ol,_ok,_oj,_oh,_oi,_of,_og,_oq);});}));}),_oo[1],B(_o2(_op[1]))));})],_9],_op[2]];}};},_os=new T(function(){return B(_lR(_cH));}),_ot=function(_ou){return E(E(_ou)[1]);},_ov=function(_ow,_ox){var _oy=E(_ow);if(!_oy){return [0];}else{var _oz=E(_ox);return _oz[0]==0?[0]:[1,_oz[1],new T(function(){return B(_ov(_oy-1|0,_oz[2]));})];}},_oA=function(_oB,_oC){return _oB<0?[0]:B(_ov(_oB,_oC));},_oD=function(_oE,_oF){var _oG=E(_oE)[1];return _oG>0?B(_oA(_oG,_oF)):[0];},_oH=function(_oI,_oJ){return [1,_,_oI,_oJ];},_oK=function(_oL){return E(E(_oL)[2]);},_oM=function(_oN){return E(E(_oN)[4]);},_oO=function(_oP,_oQ,_oR){var _oS=E(_oP),_oT=E(_oS[2]);return new F(function(){return _np(_oS[1],_oT[1],_oT[2],_oT[3],_oT[4],_oT[5],_oT[6],_oS[3],_oS[4],_oQ,_oR);});},_oU=function(_oV,_oW,_oX,_oY,_oZ,_p0){var _p1=B(A(_oX,[_oZ,_p0]));if(!_p1[0]){var _p2=B(A(_oX,[_p0,_oZ]));if(!_p2[0]){var _p3=B(A(_oV,[_oZ,_p0]));if(!_p3[0]){return [0,[0,new T(function(){return B(_oM(_oW));}),_oZ,_p0]];}else{var _p4=B(_p5([0,_oV,_oW,_oX,_oY],_p3[1]));return _p4[0]==0?[0,[2,new T(function(){return B(_oM(_oW));}),_p4[1],_oZ,_p0]]:E(_p4);}}else{var _p6=E(_p2[1]);return new F(function(){return _oO(_p6[1],_p6[2],_p6[3]);});}}else{var _p7=E(_p1[1]);return new F(function(){return _oO(_p7[1],_p7[2],_p7[3]);});}},_p8=function(_p9){return E(E(_p9)[6]);},_p5=function(_pa,_pb){var _pc=E(_pb);if(!_pc[0]){return E(_no);}else{var _pd=E(_pc[1]),_pe=E(_pd[1]),_pf=B(_oU(_pe[1],_pe[2],_pe[3],_pe[4],_pd[2],_pd[3]));if(!_pf[0]){return [0,[1,_,_pe,_pf[1]]];}else{var _pg=_pf[1],_ph=B(_p5(_pa,B(_3d(function(_pi){var _pj=E(_pi),_pk=_pj[1];return [0,_pk,new T(function(){return B(A(_p8,[B(_oK(_pk)),_pg,_pj[2]]));}),new T(function(){return B(A(_p8,[B(_oK(_pk)),_pg,_pj[3]]));})];},_pc[2]))));if(!_ph[0]){return [0,new T(function(){return B(_oH(_pa,_ph[1]));})];}else{var _pl=_ph[1];return [1,new T(function(){var _pm=function(_pn){var _po=E(_pn);return _po[0]==0?E(_pl):[1,new T(function(){var _pp=E(_po[1]),_pq=_pp[1];return [0,_pq,_pp[2],new T(function(){return B(A(_p8,[B(_oK(_pq)),_pl,_pp[3]]));})];}),new T(function(){return B(_pm(_po[2]));})];};return B(_pm(_pg));})];}}}},_pr=function(_ps,_pt,_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_pC,_pD){var _pE=new T(function(){return B(_nL(_pD));}),_pF=function(_pG,_pH){return new F(function(){return _2W(_py,_px,_pw,_pu,_pv,_ps,_pt,_pG);});},_pI=new T(function(){return B(_jr(_os,_hm,new T(function(){return B(_jk(_pF));}),new T(function(){return B(_kv(_pF));}),_py,_px,_pw,_pv,_pu,_ps,_pt));}),_pJ=function(_pK,_pL){return new F(function(){return _kC(_pC,_pA,_pB,_pv,_py,_pu,_px,_pw,_ps,_pt,_pK,_pL);});};return function(_pM,_pN,_pO){var _pP=new T(function(){return B(A(_pz,[_pO]));});return [0,new T(function(){return B(_mf(function(_pQ,_pR){var _pS=B(A(new T(function(){return B(_oe(_ps,_pt,_pu,_pv,_pw,_px,_py));}),[new T(function(){var _pT=E(E(_pR)[1]);if(!_pT[0]){var _pU=[0];}else{var _pV=E(_pT[1]),_pU=_pV[0]==0?[0]:[1,new T(function(){var _pW=E(_pV[1]);return _pW[0]==0?E(_nK):B(_ds(new T(function(){var _pX=E(B(A(_pE,[_pM]))[2]);if(!_pX[0]){var _pY=E(_nY);}else{var _pZ=E(_pX[1]);if(!_pZ[0]){var _q0=E(_nY);}else{var _q1=_pZ[1];if(!E(_pZ[2])[0]){var _q2=B(_jQ(_pJ,_pI,_q1,_pP));if(!_q2[0]){var _q3=B(_jQ(_pJ,_pI,_pP,_q1));if(!_q3[0]){var _q4=B(_pJ(_q1,_pP));if(!_q4[0]){var _q5=[0];}else{var _q6=B(_p5([0,_pJ,_pI,function(_q7,_q8){return new F(function(){return _jQ(_pJ,_pI,_q7,_q8);});},_nZ],_q4[1])),_q5=_q6[0]==0?[0]:E(_q6[1]);}var _q9=_q5;}else{var _qa=E(_q3[1]),_qb=E(_qa[1]),_qc=E(_qb[2]),_qd=B(_np(_qb[1],_qc[1],_qc[2],_qc[3],_qc[4],_qc[5],_qc[6],_qb[3],_qb[4],_qa[2],_qa[3])),_q9=_qd[0]==0?[0]:E(_qd[1]);}var _qe=_q9;}else{var _qf=E(_q2[1]),_qg=E(_qf[1]),_qh=E(_qg[2]),_qi=B(_np(_qg[1],_qh[1],_qh[2],_qh[3],_qh[4],_qh[5],_qh[6],_qg[3],_qg[4],_qf[2],_qf[3])),_qe=_qi[0]==0?[0]:E(_qi[1]);}var _qj=_qe;}else{var _qj=E(_nY);}var _q0=_qj;}var _pY=_q0;}var _qk=_pY;return _qk;}),_pW[1]));})];}var _ql=_pU;return _ql;}),_pQ])),_qm=_pS[2],_qn=E(E(_pR)[1]);if(!_qn[0]){return E(_nE);}else{var _qo=E(_qn[1]);if(!_qo[0]){return E(_qn[2])[0]==0?E(_pS):E(_nE);}else{var _qp=E(_pS[1]);if(!_qp[0]){return [0,_9,_qm];}else{var _qq=E(_qp[1]);if(!_qq[0]){return E(_pS);}else{var _qr=_qq[1],_qs=new T(function(){return [0,B(_j8(_qo[1],0))];});return [0,[1,[1,new T(function(){return B(_oD(_qs,_qr));})],[1,[1,new T(function(){return B(_nS(_qs,_qr));})],_qp[2]]],_qm];}}}}},_pN,new T(function(){return B(A(new T(function(){return B(_ot(_pD));}),[_pM]));},1)));}),[0,new T(function(){return E(B(A(_pE,[_pM]))[1]);}),[1,[1,_pP,_9]]]];};},_qt=function(_qu){var _qv=E(_qu);return _qv[0]==0?E(_qv[1]):E(_1);},_qw=function(_qx,_qy){return [0];},_qz=function(_qA){while(1){var _qB=(function(_qC){var _qD=E(_qC);if(!_qD[0]){return [0];}else{var _qE=_qD[2],_qF=E(_qD[1]);if(!_qF[0]){_qA=_qE;return null;}else{return [1,_qF[1],new T(function(){return B(_qz(_qE));})];}}})(_qA);if(_qB!=null){return _qB;}}},_qG=function(_qH,_qI,_qJ,_qK,_qL,_qM,_qN,_qO,_qP,_qQ,_qR){var _qS=new T(function(){return B(_pr(_qH,_qI,_qJ,_qK,_qL,_qM,_qN,_qO,_qP,_qQ,_qR,_gb));}),_qT=new T(function(){return B(_n1(_qR,_qP,_qQ,_qK,_qN,_qJ,_qM,_qL,_qH,_qI));}),_qU=new T(function(){return B(_gI(new T(function(){return B(_ha(new T(function(){return B(_bI(_qN,_qM,_qL,_qK,_qJ,_qH,_qI));})));})));}),_qV=[0,_qT,new T(function(){return B(_fU(_os,_hm,new T(function(){return B(_cp(new T(function(){return B(_cF(new T(function(){return B(_3W(_qN,_qM,_qL,_qK,_qJ,_qH,_qI));})));})));}),_qU,_qN,_qM,_qL,_qK,_qJ,_qH,_qI));}),_qw,_1];return function(_qW,_qX,_qY){var _qZ=B(_3d(function(_r0){var _r1=new T(function(){return B(A(_qS,[_r0,_qX,_qY]));}),_r2=B(A(_qT,[_r1,_r0]));if(!_r2[0]){return [0,[0,_qU,_r1,_r0]];}else{var _r3=B(_p5(_qV,_r2[1]));return _r3[0]==0?[0,[2,_qU,_r3[1],_r1,_r0]]:[1,_r0];}},E(_qW)[1])),_r4=B(_qz(_qZ));if(!_r4[0]){return [0,new T(function(){return B(_3d(_qt,_qZ));})];}else{var _r5=_r4[1],_r6=new T(function(){return B(A(_qS,[_r5,_qX,_qY]));}),_r7=B(A(_qT,[_r5,_r6]));if(!_r7[0]){return [0,[1,[0,_qU,_r5,_r6],_9]];}else{var _r8=B(_p5(_qV,_r7[1]));if(!_r8[0]){return [0,[1,[2,_qU,_r8[1],_r5,_r6],_9]];}else{var _r9=_r8[1];return [1,new T(function(){var _ra=E(E(_r6)[2]);return [0,new T(function(){return B(_3d(function(_rb){return new F(function(){return _dZ(_r9,_rb);});},_ra[1]));}),new T(function(){return B(_dZ(_r9,_ra[2]));})];})];}}}};},_rc=[1,_9],_rd=[1],_re=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_rf=function(_rg){return new F(function(){return err(_re);});},_rh=new T(function(){return B(_rf(_));}),_ri=function(_rj,_rk,_rl){var _rm=E(_rl);if(!_rm[0]){var _rn=_rm[1],_ro=E(_rk);if(!_ro[0]){var _rp=_ro[1],_rq=_ro[2];if(_rp<=(imul(3,_rn)|0)){return [0,(1+_rp|0)+_rn|0,E(E(_rj)),E(_ro),E(_rm)];}else{var _rr=E(_ro[3]);if(!_rr[0]){var _rs=_rr[1],_rt=E(_ro[4]);if(!_rt[0]){var _ru=_rt[1],_rv=_rt[2],_rw=_rt[3];if(_ru>=(imul(2,_rs)|0)){var _rx=function(_ry){var _rz=E(_rt[4]);return _rz[0]==0?[0,(1+_rp|0)+_rn|0,E(_rv),E([0,(1+_rs|0)+_ry|0,E(_rq),E(_rr),E(_rw)]),E([0,(1+_rn|0)+_rz[1]|0,E(E(_rj)),E(_rz),E(_rm)])]:[0,(1+_rp|0)+_rn|0,E(_rv),E([0,(1+_rs|0)+_ry|0,E(_rq),E(_rr),E(_rw)]),E([0,1+_rn|0,E(E(_rj)),E(_rd),E(_rm)])];},_rA=E(_rw);return _rA[0]==0?B(_rx(_rA[1])):B(_rx(0));}else{return [0,(1+_rp|0)+_rn|0,E(_rq),E(_rr),E([0,(1+_rn|0)+_ru|0,E(E(_rj)),E(_rt),E(_rm)])];}}else{return E(_rh);}}else{return E(_rh);}}}else{return [0,1+_rn|0,E(E(_rj)),E(_rd),E(_rm)];}}else{var _rB=E(_rk);if(!_rB[0]){var _rC=_rB[1],_rD=_rB[2],_rE=_rB[4],_rF=E(_rB[3]);if(!_rF[0]){var _rG=_rF[1],_rH=E(_rE);if(!_rH[0]){var _rI=_rH[1],_rJ=_rH[2],_rK=_rH[3];if(_rI>=(imul(2,_rG)|0)){var _rL=function(_rM){var _rN=E(_rH[4]);return _rN[0]==0?[0,1+_rC|0,E(_rJ),E([0,(1+_rG|0)+_rM|0,E(_rD),E(_rF),E(_rK)]),E([0,1+_rN[1]|0,E(E(_rj)),E(_rN),E(_rd)])]:[0,1+_rC|0,E(_rJ),E([0,(1+_rG|0)+_rM|0,E(_rD),E(_rF),E(_rK)]),E([0,1,E(E(_rj)),E(_rd),E(_rd)])];},_rO=E(_rK);return _rO[0]==0?B(_rL(_rO[1])):B(_rL(0));}else{return [0,1+_rC|0,E(_rD),E(_rF),E([0,1+_rI|0,E(E(_rj)),E(_rH),E(_rd)])];}}else{return [0,3,E(_rD),E(_rF),E([0,1,E(E(_rj)),E(_rd),E(_rd)])];}}else{var _rP=E(_rE);return _rP[0]==0?[0,3,E(_rP[2]),E([0,1,E(_rD),E(_rd),E(_rd)]),E([0,1,E(E(_rj)),E(_rd),E(_rd)])]:[0,2,E(E(_rj)),E(_rB),E(_rd)];}}else{return [0,1,E(E(_rj)),E(_rd),E(_rd)];}}},_rQ=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_rR=function(_rS){return new F(function(){return err(_rQ);});},_rT=new T(function(){return B(_rR(_));}),_rU=function(_rV,_rW,_rX){var _rY=E(_rW);if(!_rY[0]){var _rZ=_rY[1],_s0=E(_rX);if(!_s0[0]){var _s1=_s0[1],_s2=_s0[2];if(_s1<=(imul(3,_rZ)|0)){return [0,(1+_rZ|0)+_s1|0,E(E(_rV)),E(_rY),E(_s0)];}else{var _s3=E(_s0[3]);if(!_s3[0]){var _s4=_s3[1],_s5=_s3[2],_s6=_s3[3],_s7=E(_s0[4]);if(!_s7[0]){var _s8=_s7[1];if(_s4>=(imul(2,_s8)|0)){var _s9=function(_sa){var _sb=E(_rV),_sc=E(_s3[4]);return _sc[0]==0?[0,(1+_rZ|0)+_s1|0,E(_s5),E([0,(1+_rZ|0)+_sa|0,E(_sb),E(_rY),E(_s6)]),E([0,(1+_s8|0)+_sc[1]|0,E(_s2),E(_sc),E(_s7)])]:[0,(1+_rZ|0)+_s1|0,E(_s5),E([0,(1+_rZ|0)+_sa|0,E(_sb),E(_rY),E(_s6)]),E([0,1+_s8|0,E(_s2),E(_rd),E(_s7)])];},_sd=E(_s6);return _sd[0]==0?B(_s9(_sd[1])):B(_s9(0));}else{return [0,(1+_rZ|0)+_s1|0,E(_s2),E([0,(1+_rZ|0)+_s4|0,E(E(_rV)),E(_rY),E(_s3)]),E(_s7)];}}else{return E(_rT);}}else{return E(_rT);}}}else{return [0,1+_rZ|0,E(E(_rV)),E(_rY),E(_rd)];}}else{var _se=E(_rX);if(!_se[0]){var _sf=_se[1],_sg=_se[2],_sh=_se[4],_si=E(_se[3]);if(!_si[0]){var _sj=_si[1],_sk=_si[2],_sl=_si[3],_sm=E(_sh);if(!_sm[0]){var _sn=_sm[1];if(_sj>=(imul(2,_sn)|0)){var _so=function(_sp){var _sq=E(_rV),_sr=E(_si[4]);return _sr[0]==0?[0,1+_sf|0,E(_sk),E([0,1+_sp|0,E(_sq),E(_rd),E(_sl)]),E([0,(1+_sn|0)+_sr[1]|0,E(_sg),E(_sr),E(_sm)])]:[0,1+_sf|0,E(_sk),E([0,1+_sp|0,E(_sq),E(_rd),E(_sl)]),E([0,1+_sn|0,E(_sg),E(_rd),E(_sm)])];},_ss=E(_sl);return _ss[0]==0?B(_so(_ss[1])):B(_so(0));}else{return [0,1+_sf|0,E(_sg),E([0,1+_sj|0,E(E(_rV)),E(_rd),E(_si)]),E(_sm)];}}else{return [0,3,E(_sk),E([0,1,E(E(_rV)),E(_rd),E(_rd)]),E([0,1,E(_sg),E(_rd),E(_rd)])];}}else{var _st=E(_sh);return _st[0]==0?[0,3,E(_sg),E([0,1,E(E(_rV)),E(_rd),E(_rd)]),E(_st)]:[0,2,E(E(_rV)),E(_rd),E(_se)];}}else{return [0,1,E(E(_rV)),E(_rd),E(_rd)];}}},_su=function(_sv){return [0,1,E(E(_sv)),E(_rd),E(_rd)];},_sw=function(_sx,_sy){var _sz=E(_sy);if(!_sz[0]){return new F(function(){return _ri(_sz[2],B(_sw(_sx,_sz[3])),_sz[4]);});}else{return new F(function(){return _su(_sx);});}},_sA=function(_sB,_sC){var _sD=E(_sC);if(!_sD[0]){return new F(function(){return _rU(_sD[2],_sD[3],B(_sA(_sB,_sD[4])));});}else{return new F(function(){return _su(_sB);});}},_sE=function(_sF,_sG,_sH,_sI,_sJ){return new F(function(){return _rU(_sH,_sI,B(_sA(_sF,_sJ)));});},_sK=function(_sL,_sM,_sN,_sO,_sP){return new F(function(){return _ri(_sN,B(_sw(_sL,_sO)),_sP);});},_sQ=function(_sR,_sS,_sT,_sU,_sV,_sW){var _sX=E(_sS);if(!_sX[0]){var _sY=_sX[1],_sZ=_sX[2],_t0=_sX[3],_t1=_sX[4];if((imul(3,_sY)|0)>=_sT){if((imul(3,_sT)|0)>=_sY){return [0,(_sY+_sT|0)+1|0,E(E(_sR)),E(_sX),E([0,_sT,E(_sU),E(_sV),E(_sW)])];}else{return new F(function(){return _rU(_sZ,_t0,B(_sQ(_sR,_t1,_sT,_sU,_sV,_sW)));});}}else{return new F(function(){return _ri(_sU,B(_t2(_sR,_sY,_sZ,_t0,_t1,_sV)),_sW);});}}else{return new F(function(){return _sK(_sR,_sT,_sU,_sV,_sW);});}},_t2=function(_t3,_t4,_t5,_t6,_t7,_t8){var _t9=E(_t8);if(!_t9[0]){var _ta=_t9[1],_tb=_t9[2],_tc=_t9[3],_td=_t9[4];if((imul(3,_t4)|0)>=_ta){if((imul(3,_ta)|0)>=_t4){return [0,(_t4+_ta|0)+1|0,E(E(_t3)),E([0,_t4,E(_t5),E(_t6),E(_t7)]),E(_t9)];}else{return new F(function(){return _rU(_t5,_t6,B(_sQ(_t3,_t7,_ta,_tb,_tc,_td)));});}}else{return new F(function(){return _ri(_tb,B(_t2(_t3,_t4,_t5,_t6,_t7,_tc)),_td);});}}else{return new F(function(){return _sE(_t3,_t4,_t5,_t6,_t7);});}},_te=function(_tf,_tg,_th){var _ti=E(_tg);if(!_ti[0]){var _tj=_ti[1],_tk=_ti[2],_tl=_ti[3],_tm=_ti[4],_tn=E(_th);if(!_tn[0]){var _to=_tn[1],_tp=_tn[2],_tq=_tn[3],_tr=_tn[4];if((imul(3,_tj)|0)>=_to){if((imul(3,_to)|0)>=_tj){return [0,(_tj+_to|0)+1|0,E(E(_tf)),E(_ti),E(_tn)];}else{return new F(function(){return _rU(_tk,_tl,B(_sQ(_tf,_tm,_to,_tp,_tq,_tr)));});}}else{return new F(function(){return _ri(_tp,B(_t2(_tf,_tj,_tk,_tl,_tm,_tq)),_tr);});}}else{return new F(function(){return _sE(_tf,_tj,_tk,_tl,_tm);});}}else{return new F(function(){return _sw(_tf,_th);});}},_ts=function(_tt,_tu,_tv,_tw){var _tx=E(_tw);if(!_tx[0]){var _ty=new T(function(){var _tz=B(_ts(_tx[1],_tx[2],_tx[3],_tx[4]));return [0,_tz[1],_tz[2]];});return [0,new T(function(){return E(E(_ty)[1]);}),new T(function(){return B(_ri(_tu,_tv,E(_ty)[2]));})];}else{return [0,_tu,_tv];}},_tA=function(_tB,_tC,_tD,_tE){var _tF=E(_tD);if(!_tF[0]){var _tG=new T(function(){var _tH=B(_tA(_tF[1],_tF[2],_tF[3],_tF[4]));return [0,_tH[1],_tH[2]];});return [0,new T(function(){return E(E(_tG)[1]);}),new T(function(){return B(_rU(_tC,E(_tG)[2],_tE));})];}else{return [0,_tC,_tE];}},_tI=function(_tJ,_tK){var _tL=E(_tJ);if(!_tL[0]){var _tM=_tL[1],_tN=E(_tK);if(!_tN[0]){var _tO=_tN[1];if(_tM<=_tO){var _tP=B(_tA(_tO,_tN[2],_tN[3],_tN[4]));return new F(function(){return _ri(_tP[1],_tL,_tP[2]);});}else{var _tQ=B(_ts(_tM,_tL[2],_tL[3],_tL[4]));return new F(function(){return _rU(_tQ[1],_tQ[2],_tN);});}}else{return E(_tL);}}else{return E(_tK);}},_tR=function(_tS,_tT,_tU,_tV,_tW){var _tX=E(_tS);if(!_tX[0]){var _tY=_tX[1],_tZ=_tX[2],_u0=_tX[3],_u1=_tX[4];if((imul(3,_tY)|0)>=_tT){if((imul(3,_tT)|0)>=_tY){return new F(function(){return _tI(_tX,[0,_tT,E(_tU),E(_tV),E(_tW)]);});}else{return new F(function(){return _rU(_tZ,_u0,B(_tR(_u1,_tT,_tU,_tV,_tW)));});}}else{return new F(function(){return _ri(_tU,B(_u2(_tY,_tZ,_u0,_u1,_tV)),_tW);});}}else{return [0,_tT,E(_tU),E(_tV),E(_tW)];}},_u2=function(_u3,_u4,_u5,_u6,_u7){var _u8=E(_u7);if(!_u8[0]){var _u9=_u8[1],_ua=_u8[2],_ub=_u8[3],_uc=_u8[4];if((imul(3,_u3)|0)>=_u9){if((imul(3,_u9)|0)>=_u3){return new F(function(){return _tI([0,_u3,E(_u4),E(_u5),E(_u6)],_u8);});}else{return new F(function(){return _rU(_u4,_u5,B(_tR(_u6,_u9,_ua,_ub,_uc)));});}}else{return new F(function(){return _ri(_ua,B(_u2(_u3,_u4,_u5,_u6,_ub)),_uc);});}}else{return [0,_u3,E(_u4),E(_u5),E(_u6)];}},_ud=function(_ue,_uf){var _ug=E(_ue);if(!_ug[0]){var _uh=_ug[1],_ui=_ug[2],_uj=_ug[3],_uk=_ug[4],_ul=E(_uf);if(!_ul[0]){var _um=_ul[1],_un=_ul[2],_uo=_ul[3],_up=_ul[4];if((imul(3,_uh)|0)>=_um){if((imul(3,_um)|0)>=_uh){return new F(function(){return _tI(_ug,_ul);});}else{return new F(function(){return _rU(_ui,_uj,B(_tR(_uk,_um,_un,_uo,_up)));});}}else{return new F(function(){return _ri(_un,B(_u2(_uh,_ui,_uj,_uk,_uo)),_up);});}}else{return E(_ug);}}else{return E(_uf);}},_uq=function(_ur,_us){var _ut=E(_us);if(!_ut[0]){var _uu=_ut[2],_uv=_ut[3],_uw=_ut[4];if(!B(A(_ur,[_uu]))){return new F(function(){return _ud(B(_uq(_ur,_uv)),B(_uq(_ur,_uw)));});}else{return new F(function(){return _te(_uu,B(_uq(_ur,_uv)),B(_uq(_ur,_uw)));});}}else{return [1];}},_ux=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_uy=new T(function(){return B(err(_ux));}),_uz=function(_uA,_uB,_uC,_uD){while(1){var _uE=E(_uC);if(!_uE[0]){_uA=_uE[1];_uB=_uE[2];_uC=_uE[3];_uD=_uE[4];continue;}else{return E(_uB);}}},_uF=function(_uG,_uH){var _uI=B(_uq(function(_uJ){return new F(function(){return _3x(E(_uJ)[2],_uG);});},_uH));if(!_uI[0]){var _uK=E(_uI[3]);return _uK[0]==0?B(_uz(_uK[1],_uK[2],_uK[3],_uK[4])):E(_uI[2]);}else{return E(_uy);}},_uL=function(_uM,_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ){var _v0=function(_v1,_v2,_v3){var _v4=E(_v3);if(!_v4[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_uT,[_v2]));}),_9]],_9],[1,[1,new T(function(){return B(A(_uT,[_v2]));}),_9]]]];}else{var _v5=function(_v6){var _v7=E(_v6);if(!_v7[0]){return E(_rc);}else{var _v8=E(_v7[1]),_v9=B(_v0(_v1,_v8[1],_v8[2]));if(!_v9[0]){return [0,_v9[1]];}else{var _va=B(_v5(_v7[2]));return _va[0]==0?E(_va):[1,[1,_v9[1],_va[1]]];}}},_vb=B(_v5(_v4[2]));return _vb[0]==0?[0,_vb[1]]:B(A(new T(function(){return B(_qG(_uM,_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW));}),[new T(function(){return B(_uF(_v4[1],_v1));}),_vb[1],_v2]));}};return new F(function(){return _v0(_uX,_uY,_uZ);});},_vc=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_vd=new T(function(){return B(err(_vc));}),_ve=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_vf=new T(function(){return B(err(_ve));}),_vg=function(_vh,_vi){while(1){var _vj=E(_vh);if(!_vj[0]){return E(_vf);}else{var _vk=E(_vi);if(!_vk){return E(_vj[1]);}else{_vh=_vj[2];_vi=_vk-1|0;continue;}}}},_vl=function(_vm,_vn){while(1){var _vo=E(_vn);if(!_vo[0]){return true;}else{if(!B(A(_vm,[_vo[1]]))){return false;}else{_vn=_vo[2];continue;}}}},_vp=[3],_vq=function(_vr){var _vs=E(_vr);switch(_vs[0]){case 1:return [0,_vs[1]];case 3:return [3];default:return E(_vs);}},_vt=function(_vu,_vv){return [0,_vp,new T(function(){var _vw=B(_j8(_vv,0))-E(_vu)[1]|0,_vx=new T(function(){return _vw>=0?B(_nN(_vw,_vv)):E(_vv);});if(_vw>0){var _vy=function(_vz,_vA){var _vB=E(_vz);if(!_vB[0]){return E(_vx);}else{var _vC=_vB[1];return _vA>1?[1,new T(function(){return B(_vq(_vC));}),new T(function(){return B(_vy(_vB[2],_vA-1|0));})]:[1,new T(function(){return B(_vq(_vC));}),_vx];}},_vD=B(_vy(_vv,_vw));}else{var _vD=E(_vx);}var _vE=_vD,_vF=_vE,_vG=_vF,_vH=_vG;return _vH;})];},_vI=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_vJ=[2,_vI],_vK=new T(function(){return B(unCStr(" is closed, and can\'t be used"));}),_vL=function(_vM){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_vM)[1],_9)),_vK));}));});},_vN=new T(function(){return B(unCStr(" has nothing on it"));}),_vO=function(_vP){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_vP)[1],_9)),_vN));}));});},_vQ=new T(function(){return B(unCStr(" depends on something not-well-formed, and can\'t be used"));}),_vR=function(_vS){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_vS)[1],_9)),_vQ));}));});},_vT=function(_vU,_vV,_vW,_vX,_vY,_vZ,_w0){var _w1=E(_vU);if(_w1[0]==1){var _w2=E(_vV);return _w2[0]==1?[0,[1,[0,_vW,[1,_vZ,[1,_w1[1],[1,_w2[1],_9]]]]],_w0]:[0,[2,new T(function(){switch(E(_w2)[0]){case 0:var _w3=B(_vL(_vY));break;case 2:var _w3=B(_vR(_vY));break;default:var _w3=B(_vO(_vY));}return _w3;})],_w0];}else{var _w4=E(_vV);return _w4[0]==1?[0,[2,new T(function(){switch(E(_w1)[0]){case 0:var _w5=B(_vL(_vX));break;case 2:var _w5=B(_vR(_vX));break;default:var _w5=B(_vO(_vX));}return _w5;})],_w0]:[0,[2,new T(function(){var _w6=new T(function(){return B(unAppCStr(" and ",new T(function(){switch(E(_w4)[0]){case 0:var _w7=B(_vL(_vY));break;case 2:var _w7=B(_vR(_vY));break;default:var _w7=B(_vO(_vY));}return _w7;})));},1);switch(E(_w1)[0]){case 0:var _w8=B(_e(B(_vL(_vX)),_w6));break;case 2:var _w8=B(_e(B(_vR(_vX)),_w6));break;default:var _w8=B(_e(B(_vO(_vX)),_w6));}return _w8;})],_w0];}},_w9=function(_wa,_wb){while(1){var _wc=E(_wa);if(!_wc[0]){return E(_wb);}else{_wa=_wc[2];var _wd=[1,_wc[1],_wb];_wb=_wd;continue;}}},_we=function(_wf){return new F(function(){return _w9(_wf,_9);});},_wg=function(_wh,_wi){return _wh<=B(_j8(_wi,0))?[1,new T(function(){var _wj=_wh-1|0;if(_wj>=0){var _wk=B(_vg(B(_we(_wi)),_wj));}else{var _wk=E(_vd);}var _wl=_wk,_wm=_wl;return _wm;})]:[0];},_wn=new T(function(){return B(unCStr(" is unavailable"));}),_wo=new T(function(){return B(unCStr(" are unavailable"));}),_wp=function(_wq,_wr,_ws,_wt,_wu,_wv,_ww){var _wx=B(_wy(_wq,_wr,[1,_vp,_ww])),_wz=B(_wg(_wt,_wx));if(!_wz[0]){return B(_wg(_wu,_wx))[0]==0?B(_wy(_wq,_wr,[1,[2,new T(function(){return B(unAppCStr("The lines ",new T(function(){return B(_e(B(_F(0,_wt,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_wu,_9)),_wo));})));},1)));})));})],_ww])):B(_wy(_wq,_wr,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_wt,_9)),_wn));})));})],_ww]));}else{var _wA=B(_wg(_wu,_wx));return _wA[0]==0?B(_wy(_wq,_wr,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_wu,_9)),_wn));})));})],_ww])):B(_wy(_wq,_wr,new T(function(){var _wB=B(_vT(_wz[1],_wA[1],_ws,[0,_wt],[0,_wu],_wv,_ww));return [1,_wB[1],_wB[2]];})));}},_wC=function(_wD,_wE,_wF,_wG,_wH,_wI,_wJ){return new F(function(){return _wp(_wD,_wE,_wF,E(_wG)[1],E(_wH)[1],_wI,_wJ);});},_wK=new T(function(){return B(unCStr("wrong number of lines cited"));}),_wL=[2,_wK],_wM=function(_wN,_wO,_wP,_wQ,_wR,_wS){var _wT=E(_wR);if(!_wT[0]){return new F(function(){return _wy(_wN,_wO,[1,_wL,_wS]);});}else{var _wU=E(_wT[2]);return _wU[0]==0?B(_wy(_wN,_wO,[1,_wL,_wS])):E(_wU[2])[0]==0?B(_wC(_wN,_wO,_wP,_wT[1],_wU[1],_wQ,_wS)):B(_wy(_wN,_wO,[1,_wL,_wS]));}},_wV=new T(function(){return B(unCStr("Open Subproof"));}),_wW=[2,_wV],_wX=new T(function(){return B(unCStr("Impossible Error 2"));}),_wY=[2,_wX],_wZ=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_x0=[2,_wZ],_x1=new T(function(){return B(unCStr("SHOW"));}),_x2=function(_x3,_x4,_x5,_x6,_x7,_x8){var _x9=new T(function(){return B(_wy(_x3,_x4,[1,_vp,_x8]));});if(_x6<=B(_j8(_x9,0))){var _xa=_x6-1|0;if(_xa>=0){var _xb=B(_vg(B(_we(_x9)),_xa));switch(_xb[0]){case 0:return new F(function(){return _wy(_x3,_x4,[1,[2,new T(function(){return B(_vL([0,_x6]));})],_x8]);});break;case 1:return new F(function(){return _wy(_x3,_x4,[1,[1,[0,_x5,[1,_x7,[1,_xb[1],_9]]]],_x8]);});break;case 2:return new F(function(){return _wy(_x3,_x4,[1,[2,new T(function(){return B(_vR([0,_x6]));})],_x8]);});break;default:return new F(function(){return _wy(_x3,_x4,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_x6,_9)),_vN));})));})],_x8]);});}}else{return E(_vd);}}else{return new F(function(){return _wy(_x3,_x4,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_x6,_9)),_wn));})));})],_x8]);});}},_xc=function(_xd,_xe,_xf,_xg,_xh,_xi){return new F(function(){return _x2(_xd,_xe,_xf,E(_xg)[1],_xh,_xi);});},_xj=function(_xk,_xl,_xm,_xn,_xo,_xp){var _xq=E(_xo);return _xq[0]==0?B(_wy(_xk,_xl,[1,_wL,_xp])):E(_xq[2])[0]==0?B(_xc(_xk,_xl,_xm,_xq[1],_xn,_xp)):B(_wy(_xk,_xl,[1,_wL,_xp]));},_xr=function(_xs,_xt,_xu,_xv,_xw,_xx){if(!B(_3x(_xt,_x1))){var _xy=B(A(_xv,[_xt]));if(!_xy[0]){return [0,_vJ,_xx];}else{var _xz=E(_xy[1]);if(!_xz[0]){return [0,_x0,_xx];}else{switch(E(E(_xz[1])[1])){case 1:return new F(function(){return _vt(new T(function(){return [0,B(_j8(_xx,0))+1|0];},1),new T(function(){return B(_xj(_xw,_xv,_xs,_xt,_xu,_xx));}));});break;case 2:return new F(function(){return _vt(new T(function(){return [0,B(_j8(_xx,0))+1|0];},1),new T(function(){return B(_wM(_xw,_xv,_xs,_xt,_xu,_xx));}));});break;default:return [0,_wY,_xx];}}}}else{return new F(function(){return _vt(new T(function(){return [0,B(_j8(_xx,0))+1|0];},1),new T(function(){return B(_wy(_xw,_xv,[1,_wW,_xx]));}));});}},_xA=[0],_xB=new T(function(){return B(unCStr("PR"));}),_xC=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_xD=[2,_xC],_xE=new T(function(){return B(unCStr("Impossible Error 1"));}),_xF=[2,_xE],_xG=function(_xH,_xI,_xJ,_xK,_xL){var _xM=B(_wg(_xI,_xL));if(!_xM[0]){return B(_wg(_xJ,_xL))[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the lines ",new T(function(){return B(_e(B(_F(0,_xI,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_xJ,_9)),_wo));})));},1)));})));})],_xL]:[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_xI,_9)),_wn));})));})],_xL];}else{var _xN=B(_wg(_xJ,_xL));return _xN[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_xJ,_9)),_wn));})));})],_xL]:B(_vT(_xM[1],_xN[1],_xH,[0,_xI],[0,_xJ],_xK,_xL));}},_xO=new T(function(){return B(unCStr("wrong number of premises"));}),_xP=[2,_xO],_xQ=function(_xR,_xS,_xT,_xU){var _xV=E(_xT);if(!_xV[0]){return [1,_xP,_xU];}else{var _xW=E(_xV[2]);if(!_xW[0]){return [1,_xP,_xU];}else{if(!E(_xW[2])[0]){var _xX=B(_xG(_xR,E(_xV[1])[1],E(_xW[1])[1],_xS,_xU));return [1,_xX[1],_xX[2]];}else{return [1,_xP,_xU];}}}},_xY=new T(function(){return B(unCStr("has nothing on it"));}),_xZ=new T(function(){return B(unCStr("is unavailable"));}),_y0=function(_y1,_y2,_y3,_y4){var _y5=B(_wg(_y2,_y4));if(!_y5[0]){return [0,[2,new T(function(){return B(unAppCStr("line",new T(function(){return B(_e(B(_F(0,_y2,_9)),_xZ));})));})],_y4];}else{var _y6=E(_y5[1]);switch(_y6[0]){case 0:return [0,[2,new T(function(){return B(_vL([0,_y2]));})],_y4];case 1:return [0,[1,[0,_y1,[1,_y3,[1,_y6[1],_9]]]],_y4];case 2:return [0,[2,new T(function(){return B(_vR([0,_y2]));})],_y4];default:return [0,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_y2,_9)),_xY));})));})],_y4];}}},_y7=function(_y8,_y9,_ya,_yb){var _yc=B(_y0(_y8,E(_y9)[1],_ya,_yb));return [1,_yc[1],_yc[2]];},_yd=function(_ye,_yf,_yg,_yh){var _yi=E(_yg);return _yi[0]==0?[1,_xP,_yh]:E(_yi[2])[0]==0?B(_y7(_ye,_yi[1],_yf,_yh)):[1,_xP,_yh];},_yj=function(_yk,_yl,_ym,_yn,_yo){var _yp=function(_yq){var _yr=B(A(_yn,[_yl]));if(!_yr[0]){return [1,_vJ,_yo];}else{var _ys=E(_yr[1]);if(!_ys[0]){switch(E(E(_ys[1])[1])){case 1:return new F(function(){return _yd(_yk,_yl,_ym,_yo);});break;case 2:return new F(function(){return _xQ(_yk,_yl,_ym,_yo);});break;default:return [1,_xF,_yo];}}else{return [1,_xD,_yo];}}};return !B(_3x(_yl,_xB))?B(_yp(_)):E(_ym)[0]==0?[1,[1,[0,_yk,_xA]],_yo]:B(_yp(_));},_yt=function(_yu,_yv,_yw){var _yx=E(_yu);return new F(function(){return _yj(_yx[1],_yx[2],_yx[3],_yv,_yw);});},_yy=new T(function(){return B(unCStr("shouldn\'t happen"));}),_yz=[2,_yy],_yA=new T(function(){return B(unCStr("incomplete line"));}),_yB=[2,_yA],_yC=function(_yD,_yE,_yF,_yG){var _yH=E(_yD);if(!_yH[0]){return E(_yE)[0]==0?[1,_yB,_yG]:[1,_yz,_yG];}else{var _yI=_yH[1],_yJ=E(_yE);if(!_yJ[0]){return new F(function(){return _yt(_yI,_yF,_yG);});}else{var _yK=E(_yI),_yL=B(_xr(_yK[1],_yK[2],_yK[3],_yF,_yJ,_yG));return [1,_yL[1],_yL[2]];}}},_yM=function(_yN,_yO,_yP){var _yQ=E(_yN);return new F(function(){return _yC(_yQ[1],_yQ[2],_yO,_yP);});},_wy=function(_yR,_yS,_yT){return new F(function(){return (function(_yU,_yV){while(1){var _yW=(function(_yX,_yY){var _yZ=E(_yY);if(!_yZ[0]){return E(_yX);}else{_yU=new T(function(){return B(_yM(_yZ[1],_yS,_yX));});_yV=_yZ[2];return null;}})(_yU,_yV);if(_yW!=null){return _yW;}}})(_yT,_yR);});},_z0=[0,666],_z1=[0,_,_z0],_z2=[1,_z1],_z3=[0,_z2,_xA],_z4=function(_z5,_z6,_z7,_z8,_z9,_za,_zb,_zc,_zd,_ze,_zf,_zg,_zh,_zi){var _zj=B(_wy(_zg,_zh,_9)),_zk=function(_zl,_zm,_zn){return B(_uL(_z5,_z6,_z7,_z8,_z9,_za,_zb,_zl,_zd,_ze,_zf,_zi,_zm,_zn))[0]==0?false:true;};return !B(_vl(function(_zo){var _zp=E(_zo);switch(_zp[0]){case 0:var _zq=E(_zp[1]);return new F(function(){return _zk(_zc,_zq[1],_zq[2]);});break;case 1:var _zr=E(_zp[1]);return new F(function(){return _zk(_zc,_zr[1],_zr[2]);});break;case 2:return false;default:return true;}},_zj))?[0,_zj]:[1,new T(function(){var _zs=B(_j8(_zg,0))-1|0;if(_zs>=0){var _zt=B(_vg(B(_we(_zj)),_zs)),_zu=_zt[0]==1?E(_zt[1]):E(_z3);}else{var _zu=E(_vd);}var _zv=_zu,_zw=_zv,_zx=_zw;return _zx;})];},_zy=function(_zz,_zA,_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI,_zJ,_zK,_zL,_zM){var _zN=B(_z4(_zz,_zA,_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI,_zJ,_zK,_zL,_zM));return _zN[0]==0?[0,_zN[1]]:[1,new T(function(){var _zO=E(_zN[1]);return B(_uL(_zz,_zA,_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI,_zJ,_zM,_zO[1],_zO[2]));})];},_zP=function(_zQ,_zR,_){var _zS=E(_zQ);if(!_zS[0]){return _zR;}else{var _zT=B(A(_zS[1],[_zR,_])),_zU=_zT,_zV=B(_zP(_zS[2],_zR,_)),_zW=_zV;return _zR;}},_zX=function(_zY){return E(E(_zY)[2]);},_zZ=new T(function(){return B(unCStr("But that\'s impossible."));}),_A0=new T(function(){return B(unCStr(" = "));}),_A1=new T(function(){return B(unCStr("Cannot construct infinite type "));}),_A2=new T(function(){return B(unCStr("so "));}),_A3=new T(function(){return B(unCStr("class"));}),_A4=new T(function(){return B(unCStr("uniblock"));}),_A5=new T(function(){return B(unCStr(" with "));}),_A6=new T(function(){return B(unCStr("I need to match "));}),_A7=[0,46],_A8=[1,_A7,_9],_A9=new T(function(){return B(unCStr("br"));}),_Aa=function(_Ab,_){var _Ac=jsCreateElem(toJSStr(E(_A9))),_Ad=_Ac,_Ae=jsAppendChild(_Ad,E(_Ab)[1]);return [0,_Ad];},_Af=new T(function(){return B(unCStr("div"));}),_Ag=function(_Ah,_Ai,_Aj,_){var _Ak=jsCreateElem(toJSStr(E(_Af))),_Al=_Ak,_Am=jsAppendChild(_Al,E(_Aj)[1]),_An=[0,_Al],_Ao=B(A(_Ah,[_Ai,_An,_])),_Ap=_Ao;return _An;},_Aq=function(_Ar,_As,_At){while(1){var _Au=(function(_Av,_Aw,_Ax){var _Ay=E(_Ax);switch(_Ay[0]){case 0:return function(_Az,_){var _AA=B(_6v(_A6,_Az,_)),_AB=_AA,_AC=B(A(new T(function(){return B(A(_Aw,[_Ay[2]]));}),[_Az,_])),_AD=_AC,_AE=B(_6v(_A5,_Az,_)),_AF=_AE,_AG=B(A(new T(function(){return B(A(_Aw,[_Ay[3]]));}),[_Az,_])),_AH=_AG,_AI=B(_6v(_A8,_Az,_)),_AJ=_AI,_AK=B(_Aa(_Az,_)),_AL=_AK,_AM=B(_6v(_zZ,_Az,_)),_AN=_AM;return _Az;};case 1:var _AO=new T(function(){return B(_oK(_Ay[2]));});_Ar=function(_AP){return function(_mb,_mc){return new F(function(){return _6v(new T(function(){return B(A(_bT,[B(_zX(_AO)),_AP]));}),_mb,_mc);});};};_As=function(_AQ){return function(_mb,_mc){return new F(function(){return _6v(new T(function(){return B(A(new T(function(){return B(_bT(new T(function(){return B(_oM(_AO));})));}),[_AQ]));}),_mb,_mc);});};};_At=_Ay[3];return null;case 2:return function(_AR,_){var _AS=B(_6v(_A6,_AR,_)),_AT=_AS,_AU=B(_Ag(_7s,new T(function(){return B(A(_Aw,[_Ay[3]]));}),_AR,_)),_AV=_AU,_AW=B(A(_6C,[_6P,_AV,_A3,_A4,_])),_AX=_AW,_AY=B(_6v(_A5,_AR,_)),_AZ=_AY,_B0=B(_Ag(_7s,new T(function(){return B(A(_Aw,[_Ay[4]]));}),_AR,_)),_B1=_B0,_B2=B(A(_6C,[_6P,_B1,_A3,_A4,_])),_B3=_B2,_B4=B(_6v(_A2,_AR,_)),_B5=_B4,_B6=B(A(new T(function(){return B(_Aq(_Av,_Aw,_Ay[2]));}),[_AR,_])),_B7=_B6;return _AR;};default:return function(_B8,_){var _B9=B(_6v(_A1,_B8,_)),_Ba=_B9,_Bb=B(A(new T(function(){return B(A(_Av,[_Ay[3]]));}),[_B8,_])),_Bc=_Bb,_Bd=B(_6v(_A0,_B8,_)),_Be=_Bd,_Bf=B(A(new T(function(){return B(A(_Aw,[_Ay[4]]));}),[_B8,_])),_Bg=_Bf;return _B8;};}})(_Ar,_As,_At);if(_Au!=null){return _Au;}}},_Bh=function(_Bi,_Bj,_Bk){return function(_Bl,_){var _Bm=B(_zP(new T(function(){var _Bn=B(_3d(_Bi,_Bj));return _Bn[0]==0?[0]:[1,_Bn[1],new T(function(){return B(_3h(_Aa,_Bn[2]));})];}),_Bl,_)),_Bo=_Bm,_Bp=B(_Aa(_Bl,_)),_Bq=_Bp,_Br=B(_6v(_bR,_Bl,_)),_Bs=_Br,_Bt=B(A(new T(function(){return B(A(_Bi,[_Bk]));}),[_Bl,_])),_Bu=_Bt;return _Bl;};},_Bv=new T(function(){return B(unCStr(" \u22a2 "));}),_Bw=new T(function(){return B(unCStr(", "));}),_Bx=function(_By,_){return new F(function(){return _6v(_Bw,_By,_);});},_Bz=function(_BA,_BB,_BC){return function(_BD,_){var _BE=B(_zP(new T(function(){var _BF=B(_3d(_BA,_BB));return _BF[0]==0?[0]:[1,_BF[1],new T(function(){return B(_3h(_Bx,_BF[2]));})];}),_BD,_)),_BG=_BE,_BH=B(_6v(_Bv,_BD,_)),_BI=_BH,_BJ=B(A(new T(function(){return B(A(_BA,[_BC]));}),[_BD,_])),_BK=_BJ;return _BD;};},_BL=function(_BM){return function(_mb,_mc){return new F(function(){return _6v(new T(function(){return B(_1r(_BM));}),_mb,_mc);});};},_BN=new T(function(){return B(unCStr("errormsg"));}),_BO=function(_By,_){return new F(function(){return _Ag(_6v,_9,_By,_);});},_BP=function(_BQ,_){return _BQ;},_BR=new T(function(){return B(unCStr("hr"));}),_BS=function(_BT,_){var _BU=jsCreateElem(toJSStr(E(_BR))),_BV=_BU,_BW=jsAppendChild(_BV,E(_BT)[1]);return [0,_BV];},_BX=[0,10006],_BY=[1,_BX,_9],_BZ=[0,10003],_C0=[1,_BZ,_9],_C1=function(_C2,_C3,_C4,_C5,_C6,_C7,_C8,_C9,_Ca,_Cb,_Cc){return function(_Cd,_Ce){return function(_mb,_mc){return new F(function(){return _Ag(_7s,new T(function(){var _Cf=function(_Cg,_Ch){var _Ci=B(_uL(_C2,_C3,_C4,_C5,_C6,_C7,_C8,_C9,_Ca,_Cb,_Cc,new T(function(){return E(E(_Cd)[2]);}),_Cg,_Ch));return _Ci[0]==0?function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_Cj,_){var _Ck=B(_Ag(_6v,_BY,_Cj,_)),_Cl=_Ck,_Cm=B(_Ag(_7s,function(_Cn,_){return new F(function(){return _zP(new T(function(){var _Co=B(_3d(function(_Cp){return function(_mb,_mc){return new F(function(){return _Ag(_7s,new T(function(){return B(_Aq(_BL,function(_Cq){var _Cr=E(_Cq);return new F(function(){return _Bh(function(_Cs){var _Ct=E(_Cs);return new F(function(){return _Bz(function(_Cu){return function(_mb,_mc){return new F(function(){return _6v(new T(function(){return B(_3l(_C8,_C7,_C6,_C5,_C4,_C2,_C3,_Cu));}),_mb,_mc);});};},_Ct[1],_Ct[2]);});},_Cr[1],_Cr[2]);});},_Cp));}),_mb,_mc);});};},_Ci[1]));return _Co[0]==0?[0]:[1,_Co[1],new T(function(){return B(_3h(_BS,_Co[2]));})];}),_Cn,_);});},_Cj,_)),_Cv=_Cm,_Cw=B(A(_6C,[_6P,_Cv,_A3,_BN,_])),_Cx=_Cw;return _Cj;},_mb,_mc);});}:function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_Cy,_){var _Cz=B(_Ag(_6v,_C0,_Cy,_)),_CA=_Cz,_CB=B(_Ag(_6v,new T(function(){var _CC=E(_Ci[1]);return B(_bV(new T(function(){return B(_bI(_C8,_C7,_C6,_C5,_C4,_C2,_C3));}),new T(function(){return B(_3W(_C8,_C7,_C6,_C5,_C4,_C2,_C3));}),_CC[1],_CC[2]));}),_Cy,_)),_CD=_CB,_CE=B(A(_6C,[_6P,_CD,_A3,_BN,_])),_CF=_CE;return _Cy;},_mb,_mc);});};},_CG=function(_CH){var _CI=E(_CH);return _CI[0]==0?E(_BP):function(_CJ,_){var _CK=B(A(new T(function(){var _CL=E(_CI[1]);switch(_CL[0]){case 0:var _CM=E(_CL[1]),_CN=B(_Cf(_CM[1],_CM[2]));break;case 1:var _CO=E(_CL[1]),_CN=B(_Cf(_CO[1],_CO[2]));break;case 2:var _CN=function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_CP,_){var _CQ=B(_Ag(_6v,_BY,_CP,_)),_CR=_CQ,_CS=B(_Ag(_6v,_CL[1],_CP,_)),_CT=_CS,_CU=B(A(_6C,[_6P,_CT,_A3,_BN,_])),_CV=_CU;return _CP;},_mb,_mc);});};break;default:var _CN=E(_BO);}return _CN;}),[_CJ,_])),_CW=_CK,_CX=B(A(new T(function(){return B(_CG(_CI[2]));}),[_CJ,_])),_CY=_CX;return _CJ;};};return B(_CG(_Ce));}),_mb,_mc);});};};},_CZ=2,_D0=new T(function(){return B(unCStr("lined"));}),_D1=function(_D2,_){return [0,[0,_6S,[1,_D2]],_D2];},_D3=function(_D4){return function(_D5,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _D6=E(_D4);return B(_e(B(_F(0,E(_D6[2])[1],_9)),_D6[1]));})]]],_D5];};},_D7=function(_By,_){return new F(function(){return _7u(_D1,_D3,_By,_);});},_D8=function(_D9){return function(_Da,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _Db=E(_D9);return B(_e(B(_F(0,E(_Db[2])[1],_9)),_Db[1]));})]]],_Da];};},_Dc=function(_By,_){return new F(function(){return _7u(_D1,_D8,_By,_);});},_Dd=function(_De){return function(_Df,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _Dg=E(_De);return B(_e(B(_F(0,E(_Dg[2])[1],_9)),_Dg[1]));})]]],_Df];};},_Dh=function(_By,_){return new F(function(){return _7u(_D1,_Dd,_By,_);});},_Di=new T(function(){return B(unCStr("rslt"));}),_Dj=new T(function(){return B(unCStr("root"));}),_Dk=new T(function(){return B(unCStr("analysis"));}),_Dl=new T(function(){return B(unCStr("invalid"));}),_Dm=function(_By,_){return new F(function(){return _7i(_6v,_Dl,_By,_);});},_Dn=[1,_6B],_Do=[0,_Dm,_Dn],_Dp=function(_Dq,_){return [0,_Do,_Dq];},_Dr=new T(function(){return B(unCStr("span"));}),_Ds=function(_Dt,_Du,_Dv,_Dw,_){var _Dx=B(A(_Dv,[_Dw,_])),_Dy=_Dx,_Dz=E(_Dy),_DA=E(_Dz[1]),_DB=_DA[1];return [0,[0,function(_DC,_){var _DD=jsFind(toJSStr(E(_Dt))),_DE=_DD,_DF=E(_DE);if(!_DF[0]){return _DC;}else{var _DG=_DF[1];switch(E(_Du)){case 0:var _DH=B(A(_DB,[_DG,_])),_DI=_DH;return _DC;case 1:var _DJ=E(_DG),_DK=_DJ[1],_DL=jsGetChildren(_DK),_DM=_DL,_DN=E(_DM);if(!_DN[0]){var _DO=B(A(_DB,[_DJ,_])),_DP=_DO;return _DC;}else{var _DQ=jsCreateElem(toJSStr(E(_Dr))),_DR=_DQ,_DS=jsAddChildBefore(_DR,_DK,E(_DN[1])[1]),_DT=B(A(_DB,[[0,_DR],_])),_DU=_DT;return _DC;}break;default:var _DV=E(_DG),_DW=jsClearChildren(_DV[1]),_DX=B(A(_DB,[_DV,_])),_DY=_DX;return _DC;}}},_DA[2]],_Dz[2]];},_DZ=function(_E0,_E1){while(1){var _E2=E(_E0);if(!_E2[0]){return E(_E1)[0]==0?1:0;}else{var _E3=E(_E1);if(!_E3[0]){return 2;}else{var _E4=E(_E2[1])[1],_E5=E(_E3[1])[1];if(_E4!=_E5){return _E4>_E5?2:0;}else{_E0=_E2[2];_E1=_E3[2];continue;}}}}},_E6=new T(function(){return B(_e(_9,_9));}),_E7=function(_E8,_E9,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef){var _Eg=[0,_E8,_E9,_Ea],_Eh=function(_Ei){var _Ej=E(_Eb);if(!_Ej[0]){var _Ek=E(_Ef);if(!_Ek[0]){switch(B(_DZ(_E8,_Ec))){case 0:return [0,[0,_Ec,_Ed,_Ee],_9];case 1:return _E9>=_Ed?_E9!=_Ed?[0,_Eg,_9]:_Ea>=_Ee?_Ea!=_Ee?[0,_Eg,_9]:[0,_Eg,_E6]:[0,[0,_Ec,_Ed,_Ee],_9]:[0,[0,_Ec,_Ed,_Ee],_9];default:return [0,_Eg,_9];}}else{return [0,[0,_Ec,_Ed,_Ee],_Ek];}}else{switch(B(_DZ(_E8,_Ec))){case 0:return [0,[0,_Ec,_Ed,_Ee],_Ef];case 1:return _E9>=_Ed?_E9!=_Ed?[0,_Eg,_Ej]:_Ea>=_Ee?_Ea!=_Ee?[0,_Eg,_Ej]:[0,_Eg,new T(function(){return B(_e(_Ej,_Ef));})]:[0,[0,_Ec,_Ed,_Ee],_Ef]:[0,[0,_Ec,_Ed,_Ee],_Ef];default:return [0,_Eg,_Ej];}}};if(!E(_Ef)[0]){var _El=E(_Eb);return _El[0]==0?B(_Eh(_)):[0,_Eg,_El];}else{return new F(function(){return _Eh(_);});}},_Em=new T(function(){return B(_w9(_9,_9));}),_En=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_Eo=new T(function(){return B(err(_En));}),_Ep=function(_Eq,_Er,_Es,_Et,_Eu){var _Ev=function(_Ew,_Ex,_Ey){var _Ez=[1,_Ex,_Ew];return new F(function(){return A(_Eq,[_Ey,new T(function(){var _EA=E(_Ew);return function(_EB,_EC,_ED){return new F(function(){return _Ev(_Ez,_EB,_EC);});};}),_Et,_Eo,function(_EE){return new F(function(){return A(_Es,[new T(function(){return B(_w9(_Ez,_9));}),_Ey,new T(function(){var _EF=E(E(_Ey)[2]),_EG=E(_EE),_EH=E(_EG[1]),_EI=B(_E7(_EH[1],_EH[2],_EH[3],_EG[2],_EF[1],_EF[2],_EF[3],_9));return [0,E(_EI[1]),_EI[2]];})]);});}]);});};return new F(function(){return A(_Eq,[_Er,function(_EJ,_EK,_EL){return new F(function(){return _Ev(_9,_EJ,_EK);});},_Et,_Eo,function(_EM){return new F(function(){return A(_Eu,[_Em,_Er,new T(function(){var _EN=E(E(_Er)[2]),_EO=E(_EM),_EP=E(_EO[1]),_EQ=B(_E7(_EP[1],_EP[2],_EP[3],_EO[2],_EN[1],_EN[2],_EN[3],_9));return [0,E(_EQ[1]),_EQ[2]];})]);});}]);});},_ER=function(_ES,_ET){var _EU=E(_ES),_EV=E(_EU[1]),_EW=E(_ET),_EX=E(_EW[1]),_EY=B(_E7(_EV[1],_EV[2],_EV[3],_EU[2],_EX[1],_EX[2],_EX[3],_EW[2]));return [0,E(_EY[1]),_EY[2]];},_EZ=function(_F0,_F1,_F2,_F3,_F4,_F5){var _F6=function(_F7,_F8,_F9,_Fa,_Fb){return new F(function(){return _Ep(_F0,_F8,function(_Fc,_Fd,_Fe){return new F(function(){return A(_F9,[[1,_F7,_Fc],_Fd,new T(function(){var _Ff=E(E(_Fd)[2]),_Fg=E(_Fe),_Fh=E(_Fg[1]),_Fi=B(_E7(_Fh[1],_Fh[2],_Fh[3],_Fg[2],_Ff[1],_Ff[2],_Ff[3],_9));return [0,E(_Fi[1]),_Fi[2]];})]);});},_Fa,function(_Fj,_Fk,_Fl){return new F(function(){return A(_Fb,[[1,_F7,_Fj],_Fk,new T(function(){var _Fm=E(E(_Fk)[2]),_Fn=E(_Fl),_Fo=E(_Fn[1]),_Fp=B(_E7(_Fo[1],_Fo[2],_Fo[3],_Fn[2],_Fm[1],_Fm[2],_Fm[3],_9));return [0,E(_Fp[1]),_Fp[2]];})]);});});});};return new F(function(){return A(_F0,[_F1,function(_Fq,_Fr,_Fs){return new F(function(){return _F6(_Fq,_Fr,_F2,_F3,function(_Ft,_Fu,_Fv){return new F(function(){return A(_F2,[_Ft,_Fu,new T(function(){return B(_ER(_Fs,_Fv));})]);});});});},_F3,function(_Fw,_Fx,_Fy){return new F(function(){return _F6(_Fw,_Fx,_F2,_F3,function(_Fz,_FA,_FB){return new F(function(){return A(_F4,[_Fz,_FA,new T(function(){return B(_ER(_Fy,_FB));})]);});});});},_F5]);});},_FC=function(_FD,_FE,_FF,_FG,_FH){var _FI=function(_FJ,_FK){return new F(function(){return A(_FD,[_FK,new T(function(){var _FL=E(_FJ);return function(_FM,_FN,_FO){return new F(function(){return _FI(_9,_FN);});};}),_FG,_Eo,function(_FP){return new F(function(){return A(_FF,[_6B,_FK,new T(function(){var _FQ=E(E(_FK)[2]),_FR=E(_FP),_FS=E(_FR[1]),_FT=B(_E7(_FS[1],_FS[2],_FS[3],_FR[2],_FQ[1],_FQ[2],_FQ[3],_9));return [0,E(_FT[1]),_FT[2]];})]);});}]);});};return new F(function(){return A(_FD,[_FE,function(_FU,_FV,_FW){return new F(function(){return _FI(_9,_FV);});},_FG,_Eo,function(_FX){return new F(function(){return A(_FH,[_6B,_FE,new T(function(){var _FY=E(E(_FE)[2]),_FZ=E(_FX),_G0=E(_FZ[1]),_G1=B(_E7(_G0[1],_G0[2],_G0[3],_FZ[2],_FY[1],_FY[2],_FY[3],_9));return [0,E(_G1[1]),_G1[2]];})]);});}]);});},_G2=function(_G3,_G4,_G5,_G6,_G7,_G8,_G9){var _Ga=function(_Gb,_Gc,_Gd,_Ge,_Gf){var _Gg=[1,_Gb,_9],_Gh=function(_Gi,_Gj,_Gk,_Gl){return new F(function(){return _G2(_G3,_G4,_Gi,function(_Gm,_Gn,_Go){return new F(function(){return A(_Gj,[[1,_Gb,_Gm],_Gn,new T(function(){var _Gp=E(E(_Gn)[2]),_Gq=E(_Go),_Gr=E(_Gq[1]),_Gs=B(_E7(_Gr[1],_Gr[2],_Gr[3],_Gq[2],_Gp[1],_Gp[2],_Gp[3],_9));return [0,E(_Gs[1]),_Gs[2]];})]);});},_Gk,function(_Gt,_Gu,_Gv){return new F(function(){return A(_Gl,[[1,_Gb,_Gt],_Gu,new T(function(){var _Gw=E(E(_Gu)[2]),_Gx=E(_Gv),_Gy=E(_Gx[1]),_Gz=B(_E7(_Gy[1],_Gy[2],_Gy[3],_Gx[2],_Gw[1],_Gw[2],_Gw[3],_9));return [0,E(_Gz[1]),_Gz[2]];})]);});},function(_GA){return new F(function(){return A(_Gl,[_Gg,_Gi,new T(function(){var _GB=E(E(_Gi)[2]),_GC=_GB[1],_GD=_GB[2],_GE=_GB[3],_GF=E(_GA),_GG=E(_GF[1]),_GH=B(_E7(_GG[1],_GG[2],_GG[3],_GF[2],_GC,_GD,_GE,_9)),_GI=E(_GH[1]),_GJ=B(_E7(_GI[1],_GI[2],_GI[3],_GH[2],_GC,_GD,_GE,_9));return [0,E(_GJ[1]),_GJ[2]];})]);});});});};return new F(function(){return A(_G4,[_Gc,function(_GK,_GL,_GM){return new F(function(){return _Gh(_GL,_Gd,_Ge,function(_GN,_GO,_GP){return new F(function(){return A(_Gd,[_GN,_GO,new T(function(){return B(_ER(_GM,_GP));})]);});});});},_Ge,function(_GQ,_GR,_GS){return new F(function(){return _Gh(_GR,_Gd,_Ge,function(_GT,_GU,_GV){return new F(function(){return A(_Gf,[_GT,_GU,new T(function(){return B(_ER(_GS,_GV));})]);});});});},function(_GW){return new F(function(){return A(_Gf,[_Gg,_Gc,new T(function(){var _GX=E(E(_Gc)[2]),_GY=E(_GW),_GZ=E(_GY[1]),_H0=B(_E7(_GZ[1],_GZ[2],_GZ[3],_GY[2],_GX[1],_GX[2],_GX[3],_9));return [0,E(_H0[1]),_H0[2]];})]);});}]);});};return new F(function(){return A(_G3,[_G5,function(_H1,_H2,_H3){return new F(function(){return _Ga(_H1,_H2,_G6,_G7,function(_H4,_H5,_H6){return new F(function(){return A(_G6,[_H4,_H5,new T(function(){return B(_ER(_H3,_H6));})]);});});});},_G7,function(_H7,_H8,_H9){return new F(function(){return _Ga(_H7,_H8,_G6,_G7,function(_Ha,_Hb,_Hc){return new F(function(){return A(_G8,[_Ha,_Hb,new T(function(){return B(_ER(_H9,_Hc));})]);});});});},_G9]);});},_Hd=function(_He,_Hf){return new F(function(){return A(_Hf,[_He]);});},_Hg=[0,34],_Hh=[1,_Hg,_9],_Hi=[0,E(_9)],_Hj=[1,_Hi,_9],_Hk=function(_Hl,_Hm){var _Hn=_Hl%_Hm;if(_Hl<=0){if(_Hl>=0){return E(_Hn);}else{if(_Hm<=0){return E(_Hn);}else{var _Ho=E(_Hn);return _Ho==0?0:_Ho+_Hm|0;}}}else{if(_Hm>=0){if(_Hl>=0){return E(_Hn);}else{if(_Hm<=0){return E(_Hn);}else{var _Hp=E(_Hn);return _Hp==0?0:_Hp+_Hm|0;}}}else{var _Hq=E(_Hn);return _Hq==0?0:_Hq+_Hm|0;}}},_Hr=new T(function(){return B(unCStr("ACK"));}),_Hs=new T(function(){return B(unCStr("BEL"));}),_Ht=new T(function(){return B(unCStr("BS"));}),_Hu=new T(function(){return B(unCStr("SP"));}),_Hv=[1,_Hu,_9],_Hw=new T(function(){return B(unCStr("US"));}),_Hx=[1,_Hw,_Hv],_Hy=new T(function(){return B(unCStr("RS"));}),_Hz=[1,_Hy,_Hx],_HA=new T(function(){return B(unCStr("GS"));}),_HB=[1,_HA,_Hz],_HC=new T(function(){return B(unCStr("FS"));}),_HD=[1,_HC,_HB],_HE=new T(function(){return B(unCStr("ESC"));}),_HF=[1,_HE,_HD],_HG=new T(function(){return B(unCStr("SUB"));}),_HH=[1,_HG,_HF],_HI=new T(function(){return B(unCStr("EM"));}),_HJ=[1,_HI,_HH],_HK=new T(function(){return B(unCStr("CAN"));}),_HL=[1,_HK,_HJ],_HM=new T(function(){return B(unCStr("ETB"));}),_HN=[1,_HM,_HL],_HO=new T(function(){return B(unCStr("SYN"));}),_HP=[1,_HO,_HN],_HQ=new T(function(){return B(unCStr("NAK"));}),_HR=[1,_HQ,_HP],_HS=new T(function(){return B(unCStr("DC4"));}),_HT=[1,_HS,_HR],_HU=new T(function(){return B(unCStr("DC3"));}),_HV=[1,_HU,_HT],_HW=new T(function(){return B(unCStr("DC2"));}),_HX=[1,_HW,_HV],_HY=new T(function(){return B(unCStr("DC1"));}),_HZ=[1,_HY,_HX],_I0=new T(function(){return B(unCStr("DLE"));}),_I1=[1,_I0,_HZ],_I2=new T(function(){return B(unCStr("SI"));}),_I3=[1,_I2,_I1],_I4=new T(function(){return B(unCStr("SO"));}),_I5=[1,_I4,_I3],_I6=new T(function(){return B(unCStr("CR"));}),_I7=[1,_I6,_I5],_I8=new T(function(){return B(unCStr("FF"));}),_I9=[1,_I8,_I7],_Ia=new T(function(){return B(unCStr("VT"));}),_Ib=[1,_Ia,_I9],_Ic=new T(function(){return B(unCStr("LF"));}),_Id=[1,_Ic,_Ib],_Ie=new T(function(){return B(unCStr("HT"));}),_If=[1,_Ie,_Id],_Ig=[1,_Ht,_If],_Ih=[1,_Hs,_Ig],_Ii=[1,_Hr,_Ih],_Ij=new T(function(){return B(unCStr("ENQ"));}),_Ik=[1,_Ij,_Ii],_Il=new T(function(){return B(unCStr("EOT"));}),_Im=[1,_Il,_Ik],_In=new T(function(){return B(unCStr("ETX"));}),_Io=[1,_In,_Im],_Ip=new T(function(){return B(unCStr("STX"));}),_Iq=[1,_Ip,_Io],_Ir=new T(function(){return B(unCStr("SOH"));}),_Is=[1,_Ir,_Iq],_It=new T(function(){return B(unCStr("NUL"));}),_Iu=[1,_It,_Is],_Iv=[0,92],_Iw=new T(function(){return B(unCStr("\\DEL"));}),_Ix=new T(function(){return B(unCStr("\\a"));}),_Iy=new T(function(){return B(unCStr("\\\\"));}),_Iz=new T(function(){return B(unCStr("\\SO"));}),_IA=new T(function(){return B(unCStr("\\r"));}),_IB=new T(function(){return B(unCStr("\\f"));}),_IC=new T(function(){return B(unCStr("\\v"));}),_ID=new T(function(){return B(unCStr("\\n"));}),_IE=new T(function(){return B(unCStr("\\t"));}),_IF=new T(function(){return B(unCStr("\\b"));}),_IG=function(_IH,_II){if(_IH<=127){var _IJ=E(_IH);switch(_IJ){case 92:return new F(function(){return _e(_Iy,_II);});break;case 127:return new F(function(){return _e(_Iw,_II);});break;default:if(_IJ<32){var _IK=E(_IJ);switch(_IK){case 7:return new F(function(){return _e(_Ix,_II);});break;case 8:return new F(function(){return _e(_IF,_II);});break;case 9:return new F(function(){return _e(_IE,_II);});break;case 10:return new F(function(){return _e(_ID,_II);});break;case 11:return new F(function(){return _e(_IC,_II);});break;case 12:return new F(function(){return _e(_IB,_II);});break;case 13:return new F(function(){return _e(_IA,_II);});break;case 14:return new F(function(){return _e(_Iz,new T(function(){var _IL=E(_II);if(!_IL[0]){var _IM=[0];}else{var _IM=E(E(_IL[1])[1])==72?B(unAppCStr("\\&",_IL)):E(_IL);}return _IM;},1));});break;default:return new F(function(){return _e([1,_Iv,new T(function(){var _IN=_IK;return _IN>=0?B(_vg(_Iu,_IN)):E(_vd);})],_II);});}}else{return [1,[0,_IJ],_II];}}}else{return [1,_Iv,new T(function(){var _IO=jsShowI(_IH),_IP=_IO;return B(_e(fromJSStr(_IP),new T(function(){var _IQ=E(_II);if(!_IQ[0]){var _IR=[0];}else{var _IS=E(_IQ[1])[1];if(_IS<48){var _IT=E(_IQ);}else{var _IT=_IS>57?E(_IQ):B(unAppCStr("\\&",_IQ));}var _IU=_IT,_IV=_IU,_IR=_IV;}return _IR;},1)));})];}},_IW=new T(function(){return B(unCStr("\\\""));}),_IX=function(_IY,_IZ){var _J0=E(_IY);if(!_J0[0]){return E(_IZ);}else{var _J1=_J0[2],_J2=E(E(_J0[1])[1]);if(_J2==34){return new F(function(){return _e(_IW,new T(function(){return B(_IX(_J1,_IZ));},1));});}else{return new F(function(){return _IG(_J2,new T(function(){return B(_IX(_J1,_IZ));}));});}}},_J3=function(_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd){var _Je=[0,_J8,_J9,_Ja];return new F(function(){return A(_J4,[new T(function(){return B(A(_J5,[_J7]));}),function(_Jf){var _Jg=E(_Jf);if(!_Jg[0]){return E(new T(function(){return B(A(_Jd,[[0,E(_Je),_Hj]]));}));}else{var _Jh=E(_Jg[1]),_Ji=_Jh[1],_Jj=_Jh[2];if(!B(A(_J6,[_Ji]))){return new F(function(){return A(_Jd,[[0,E(_Je),[1,[0,E([1,_Hg,new T(function(){return B(_IX([1,_Ji,_9],_Hh));})])],_9]]]);});}else{var _Jk=E(_Ji);switch(E(_Jk[1])){case 9:var _Jl=[0,_J8,_J9,(_Ja+8|0)-B(_Hk(_Ja-1|0,8))|0];break;case 10:var _Jl=E([0,_J8,_J9+1|0,1]);break;default:var _Jl=E([0,_J8,_J9,_Ja+1|0]);}var _Jm=_Jl,_Jn=[0,E(_Jm),_9],_Jo=[0,_Jj,E(_Jm),E(_Jb)];return new F(function(){return A(_Jc,[_Jk,_Jo,_Jn]);});}}}]);});},_Jp=function(_Jq,_Jr){return E(_Jq)[1]!=E(_Jr)[1];},_Js=function(_Jt,_Ju){return E(_Jt)[1]==E(_Ju)[1];},_Jv=[0,_Js,_Jp],_Jw=new T(function(){return B(unCStr(" 	"));}),_Jx=function(_Jy){return new F(function(){return _9r(_Jv,_Jy,_Jw);});},_Jz=function(_JA,_JB){return E(_JB);},_JC=function(_JD){return new F(function(){return err(_JD);});},_JE=function(_JF){return E(_JF);},_JG=[0,_Hd,_Jz,_JE,_JC],_JH=function(_JI){return E(E(_JI)[3]);},_JJ=function(_JK,_JL){var _JM=E(_JL);return _JM[0]==0?B(A(_JH,[_JK,_4O])):B(A(_JH,[_JK,[1,[0,_JM[1],_JM[2]]]]));},_JN=function(_JO){return new F(function(){return _JJ(_JG,_JO);});},_JP=function(_JQ,_JR,_JS,_JT,_JU){var _JV=E(_JQ),_JW=E(_JV[2]);return new F(function(){return _J3(_Hd,_JN,_Jx,_JV[1],_JW[1],_JW[2],_JW[3],_JV[3],_JR,_JU);});},_JX=function(_JY){return [2,E(E(_JY))];},_JZ=function(_K0,_K1){switch(E(_K0)[0]){case 0:switch(E(_K1)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_K1)[0]==1?false:true;case 2:return E(_K1)[0]==2?false:true;default:return E(_K1)[0]==3?false:true;}},_K2=[2,E(_9)],_K3=function(_K4){return new F(function(){return _JZ(_K2,_K4);});},_K5=function(_K6,_K7,_K8){var _K9=E(_K8);if(!_K9[0]){return [0,_K6,[1,_K2,new T(function(){return B(_8T(_K3,_K7));})]];}else{var _Ka=_K9[1],_Kb=E(_K9[2]);if(!_Kb[0]){var _Kc=new T(function(){return [2,E(E(_Ka))];});return [0,_K6,[1,_Kc,new T(function(){return B(_8T(function(_K4){return new F(function(){return _JZ(_Kc,_K4);});},_K7));})]];}else{var _Kd=new T(function(){return [2,E(E(_Ka))];}),_Ke=function(_Kf){var _Kg=E(_Kf);if(!_Kg[0]){return [0,_K6,[1,_Kd,new T(function(){return B(_8T(function(_K4){return new F(function(){return _JZ(_Kd,_K4);});},_K7));})]];}else{var _Kh=B(_Ke(_Kg[2]));return [0,_Kh[1],[1,new T(function(){return B(_JX(_Kg[1]));}),_Kh[2]]];}};return new F(function(){return (function(_Ki,_Kj){var _Kk=B(_Ke(_Kj));return [0,_Kk[1],[1,new T(function(){return B(_JX(_Ki));}),_Kk[2]]];})(_Kb[1],_Kb[2]);});}}},_Kl=function(_Km,_Kn){var _Ko=E(_Km),_Kp=B(_K5(_Ko[1],_Ko[2],_Kn));return [0,E(_Kp[1]),_Kp[2]];},_Kq=function(_Kr,_Ks,_Kt,_Ku,_Kv,_Kw,_Kx){return new F(function(){return A(_Kr,[_Kt,_Ku,_Kv,function(_Ky,_Kz,_KA){return new F(function(){return A(_Kw,[_Ky,_Kz,new T(function(){var _KB=E(_KA),_KC=E(_KB[2]);if(!_KC[0]){var _KD=E(_KB);}else{var _KE=B(_K5(_KB[1],_KC,_Ks)),_KD=[0,E(_KE[1]),_KE[2]];}var _KF=_KD;return _KF;})]);});},function(_KG){return new F(function(){return A(_Kx,[new T(function(){return B(_Kl(_KG,_Ks));})]);});}]);});},_KH=new T(function(){return B(unCStr("digit"));}),_KI=[1,_KH,_9],_KJ=function(_KK){return new F(function(){return _JJ(_JG,_KK);});},_KL=function(_KM){var _KN=E(_KM)[1];return _KN<48?false:_KN<=57;},_KO=function(_KP,_KQ,_KR,_KS,_KT){var _KU=E(_KP),_KV=E(_KU[2]);return new F(function(){return _J3(_Hd,_KJ,_KL,_KU[1],_KV[1],_KV[2],_KV[3],_KU[3],_KQ,_KT);});},_KW=function(_KX,_KY,_KZ,_L0,_L1){return new F(function(){return _Kq(_KO,_KI,_KX,_KY,_KZ,_L0,_L1);});},_L2=function(_L3,_L4,_L5,_L6,_L7){return new F(function(){return _EZ(_KW,_L3,_L4,_L5,_L6,_L7);});},_L8=function(_L9){return [0,_L9,function(_K4){return new F(function(){return _JJ(_L9,_K4);});}];},_La=new T(function(){return B(_L8(_JG));}),_Lb=function(_Lc,_Ld){return function(_Le,_Lf,_Lg,_Lh,_Li){return new F(function(){return _Kq(function(_Lj,_Lk,_Ll,_Lm,_Ln){var _Lo=E(_Lc),_Lp=E(_Lj),_Lq=E(_Lp[2]);return new F(function(){return _J3(E(_Lo[1])[1],_Lo[2],function(_Lr){return new F(function(){return _Js(_Lr,_Ld);});},_Lp[1],_Lq[1],_Lq[2],_Lq[3],_Lp[3],_Lk,_Ln);});},[1,[1,_Hg,new T(function(){return B(_IX([1,_Ld,_9],_Hh));})],_9],_Le,_Lf,_Lg,_Lh,_Li);});};},_Ls=[0,44],_Lt=new T(function(){return B(_Lb(_La,_Ls));}),_Lu=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_Lv=new T(function(){return B(err(_Lu));}),_Lw=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_Lx=new T(function(){return B(err(_Lw));}),_Ly=new T(function(){return B(_2L("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_Lz=function(_LA,_LB){while(1){var _LC=(function(_LD,_LE){var _LF=E(_LD);switch(_LF[0]){case 0:var _LG=E(_LE);if(!_LG[0]){return [0];}else{_LA=B(A(_LF[1],[_LG[1]]));_LB=_LG[2];return null;}break;case 1:var _LH=B(A(_LF[1],[_LE])),_LI=_LE;_LA=_LH;_LB=_LI;return null;case 2:return [0];case 3:return [1,[0,_LF[1],_LE],new T(function(){return B(_Lz(_LF[2],_LE));})];default:return E(_LF[1]);}})(_LA,_LB);if(_LC!=null){return _LC;}}},_LJ=function(_LK,_LL){var _LM=function(_LN){var _LO=E(_LL);if(_LO[0]==3){return [3,_LO[1],new T(function(){return B(_LJ(_LK,_LO[2]));})];}else{var _LP=E(_LK);if(_LP[0]==2){return E(_LO);}else{var _LQ=E(_LO);if(_LQ[0]==2){return E(_LP);}else{var _LR=function(_LS){var _LT=E(_LQ);if(_LT[0]==4){return [1,function(_LU){return [4,new T(function(){return B(_e(B(_Lz(_LP,_LU)),_LT[1]));})];}];}else{var _LV=E(_LP);if(_LV[0]==1){var _LW=_LV[1],_LX=E(_LT);return _LX[0]==0?[1,function(_LY){return new F(function(){return _LJ(B(A(_LW,[_LY])),_LX);});}]:[1,function(_LZ){return new F(function(){return _LJ(B(A(_LW,[_LZ])),new T(function(){return B(A(_LX[1],[_LZ]));}));});}];}else{var _M0=E(_LT);return _M0[0]==0?E(_Ly):[1,function(_M1){return new F(function(){return _LJ(_LV,new T(function(){return B(A(_M0[1],[_M1]));}));});}];}}},_M2=E(_LP);switch(_M2[0]){case 1:var _M3=E(_LQ);if(_M3[0]==4){return [1,function(_M4){return [4,new T(function(){return B(_e(B(_Lz(B(A(_M2[1],[_M4])),_M4)),_M3[1]));})];}];}else{return new F(function(){return _LR(_);});}break;case 4:var _M5=_M2[1],_M6=E(_LQ);switch(_M6[0]){case 0:return [1,function(_M7){return [4,new T(function(){return B(_e(_M5,new T(function(){return B(_Lz(_M6,_M7));},1)));})];}];case 1:return [1,function(_M8){return [4,new T(function(){return B(_e(_M5,new T(function(){return B(_Lz(B(A(_M6[1],[_M8])),_M8));},1)));})];}];default:return [4,new T(function(){return B(_e(_M5,_M6[1]));})];}break;default:return new F(function(){return _LR(_);});}}}}},_M9=E(_LK);switch(_M9[0]){case 0:var _Ma=E(_LL);if(!_Ma[0]){return [0,function(_Mb){return new F(function(){return _LJ(B(A(_M9[1],[_Mb])),new T(function(){return B(A(_Ma[1],[_Mb]));}));});}];}else{return new F(function(){return _LM(_);});}break;case 3:return [3,_M9[1],new T(function(){return B(_LJ(_M9[2],_LL));})];default:return new F(function(){return _LM(_);});}},_Mc=[0,41],_Md=[1,_Mc,_9],_Me=[0,40],_Mf=[1,_Me,_9],_Mg=function(_Mh,_Mi){var _Mj=E(_Mh);switch(_Mj[0]){case 0:return [0,function(_Mk){return new F(function(){return _Mg(B(A(_Mj[1],[_Mk])),_Mi);});}];case 1:return [1,function(_Ml){return new F(function(){return _Mg(B(A(_Mj[1],[_Ml])),_Mi);});}];case 2:return [2];case 3:return new F(function(){return _LJ(B(A(_Mi,[_Mj[1]])),new T(function(){return B(_Mg(_Mj[2],_Mi));}));});break;default:var _Mm=function(_Mn){var _Mo=E(_Mn);if(!_Mo[0]){return [0];}else{var _Mp=E(_Mo[1]);return new F(function(){return _e(B(_Lz(B(A(_Mi,[_Mp[1]])),_Mp[2])),new T(function(){return B(_Mm(_Mo[2]));},1));});}},_Mq=B(_Mm(_Mj[1]));return _Mq[0]==0?[2]:[4,_Mq];}},_Mr=[2],_Ms=function(_Mt){return [3,_Mt,_Mr];},_Mu=function(_Mv,_Mw){var _Mx=E(_Mv);if(!_Mx){return new F(function(){return A(_Mw,[_6B]);});}else{return [0,function(_My){return E(new T(function(){return B(_Mu(_Mx-1|0,_Mw));}));}];}},_Mz=function(_MA,_MB,_MC){return function(_MD){return new F(function(){return A(function(_ME,_MF,_MG){while(1){var _MH=(function(_MI,_MJ,_MK){var _ML=E(_MI);switch(_ML[0]){case 0:var _MM=E(_MJ);if(!_MM[0]){return E(_MB);}else{_ME=B(A(_ML[1],[_MM[1]]));_MF=_MM[2];var _MN=_MK+1|0;_MG=_MN;return null;}break;case 1:var _MO=B(A(_ML[1],[_MJ])),_MP=_MJ,_MN=_MK;_ME=_MO;_MF=_MP;_MG=_MN;return null;case 2:return E(_MB);case 3:return function(_MQ){return new F(function(){return _Mu(_MK,function(_MR){return E(new T(function(){return B(_Mg(_ML,_MQ));}));});});};default:return function(_mb){return new F(function(){return _Mg(_ML,_mb);});};}})(_ME,_MF,_MG);if(_MH!=null){return _MH;}}},[new T(function(){return B(A(_MA,[_Ms]));}),_MD,0,_MC]);});};},_MS=function(_MT){return new F(function(){return A(_MT,[_9]);});},_MU=function(_MV,_MW){var _MX=function(_MY){var _MZ=E(_MY);if(!_MZ[0]){return E(_MS);}else{var _N0=_MZ[1];return !B(A(_MV,[_N0]))?E(_MS):function(_N1){return [0,function(_N2){return E(new T(function(){return B(A(new T(function(){return B(_MX(_MZ[2]));}),[function(_N3){return new F(function(){return A(_N1,[[1,_N0,_N3]]);});}]));}));}];};}};return function(_N4){return new F(function(){return A(_MX,[_N4,_MW]);});};},_N5=[6],_N6=new T(function(){return B(unCStr("valDig: Bad base"));}),_N7=new T(function(){return B(err(_N6));}),_N8=function(_N9,_Na){var _Nb=function(_Nc,_Nd){var _Ne=E(_Nc);if(!_Ne[0]){return function(_Nf){return new F(function(){return A(_Nf,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{var _Ng=E(_Ne[1])[1],_Nh=function(_Ni){return function(_Nj){return [0,function(_Nk){return E(new T(function(){return B(A(new T(function(){return B(_Nb(_Ne[2],function(_Nl){return new F(function(){return A(_Nd,[[1,_Ni,_Nl]]);});}));}),[_Nj]));}));}];};};switch(E(E(_N9)[1])){case 8:if(48>_Ng){return function(_Nm){return new F(function(){return A(_Nm,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{if(_Ng>55){return function(_Nn){return new F(function(){return A(_Nn,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{return new F(function(){return _Nh([0,_Ng-48|0]);});}}break;case 10:if(48>_Ng){return function(_No){return new F(function(){return A(_No,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{if(_Ng>57){return function(_Np){return new F(function(){return A(_Np,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{return new F(function(){return _Nh([0,_Ng-48|0]);});}}break;case 16:if(48>_Ng){if(97>_Ng){if(65>_Ng){return function(_Nq){return new F(function(){return A(_Nq,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{if(_Ng>70){return function(_Nr){return new F(function(){return A(_Nr,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{return new F(function(){return _Nh([0,(_Ng-65|0)+10|0]);});}}}else{if(_Ng>102){if(65>_Ng){return function(_Ns){return new F(function(){return A(_Ns,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{if(_Ng>70){return function(_Nt){return new F(function(){return A(_Nt,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{return new F(function(){return _Nh([0,(_Ng-65|0)+10|0]);});}}}else{return new F(function(){return _Nh([0,(_Ng-97|0)+10|0]);});}}}else{if(_Ng>57){if(97>_Ng){if(65>_Ng){return function(_Nu){return new F(function(){return A(_Nu,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{if(_Ng>70){return function(_Nv){return new F(function(){return A(_Nv,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{return new F(function(){return _Nh([0,(_Ng-65|0)+10|0]);});}}}else{if(_Ng>102){if(65>_Ng){return function(_Nw){return new F(function(){return A(_Nw,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{if(_Ng>70){return function(_Nx){return new F(function(){return A(_Nx,[new T(function(){return B(A(_Nd,[_9]));})]);});};}else{return new F(function(){return _Nh([0,(_Ng-65|0)+10|0]);});}}}else{return new F(function(){return _Nh([0,(_Ng-97|0)+10|0]);});}}}else{return new F(function(){return _Nh([0,_Ng-48|0]);});}}break;default:return E(_N7);}}};return function(_Ny){return new F(function(){return A(_Nb,[_Ny,_6P,function(_Nz){var _NA=E(_Nz);return _NA[0]==0?[2]:B(A(_Na,[_NA]));}]);});};},_NB=[0,10],_NC=[0,1],_ND=[0,2147483647],_NE=function(_NF,_NG){while(1){var _NH=E(_NF);if(!_NH[0]){var _NI=_NH[1],_NJ=E(_NG);if(!_NJ[0]){var _NK=_NJ[1],_NL=addC(_NI,_NK);if(!E(_NL[2])){return [0,_NL[1]];}else{_NF=[1,I_fromInt(_NI)];_NG=[1,I_fromInt(_NK)];continue;}}else{_NF=[1,I_fromInt(_NI)];_NG=_NJ;continue;}}else{var _NM=E(_NG);if(!_NM[0]){_NF=_NH;_NG=[1,I_fromInt(_NM[1])];continue;}else{return [1,I_add(_NH[1],_NM[1])];}}}},_NN=new T(function(){return B(_NE(_ND,_NC));}),_NO=function(_NP){var _NQ=E(_NP);if(!_NQ[0]){var _NR=E(_NQ[1]);return _NR==(-2147483648)?E(_NN):[0, -_NR];}else{return [1,I_negate(_NQ[1])];}},_NS=[0,10],_NT=[0,0],_NU=function(_NV){return [0,_NV];},_NW=function(_NX,_NY){while(1){var _NZ=E(_NX);if(!_NZ[0]){var _O0=_NZ[1],_O1=E(_NY);if(!_O1[0]){var _O2=_O1[1];if(!(imul(_O0,_O2)|0)){return [0,imul(_O0,_O2)|0];}else{_NX=[1,I_fromInt(_O0)];_NY=[1,I_fromInt(_O2)];continue;}}else{_NX=[1,I_fromInt(_O0)];_NY=_O1;continue;}}else{var _O3=E(_NY);if(!_O3[0]){_NX=_NZ;_NY=[1,I_fromInt(_O3[1])];continue;}else{return [1,I_mul(_NZ[1],_O3[1])];}}}},_O4=function(_O5,_O6,_O7){while(1){var _O8=E(_O7);if(!_O8[0]){return E(_O6);}else{var _O9=B(_NE(B(_NW(_O6,_O5)),B(_NU(E(_O8[1])[1]))));_O7=_O8[2];_O6=_O9;continue;}}},_Oa=function(_Ob){var _Oc=new T(function(){return B(_LJ(B(_LJ([0,function(_Od){return E(E(_Od)[1])==45?[1,B(_N8(_NB,function(_Oe){return new F(function(){return A(_Ob,[[1,new T(function(){return B(_NO(B(_O4(_NS,_NT,_Oe))));})]]);});}))]:[2];}],[0,function(_Of){return E(E(_Of)[1])==43?[1,B(_N8(_NB,function(_Og){return new F(function(){return A(_Ob,[[1,new T(function(){return B(_O4(_NS,_NT,_Og));})]]);});}))]:[2];}])),new T(function(){return [1,B(_N8(_NB,function(_Oh){return new F(function(){return A(_Ob,[[1,new T(function(){return B(_O4(_NS,_NT,_Oh));})]]);});}))];})));});return new F(function(){return _LJ([0,function(_Oi){return E(E(_Oi)[1])==101?E(_Oc):[2];}],[0,function(_Oj){return E(E(_Oj)[1])==69?E(_Oc):[2];}]);});},_Ok=function(_Ol){return new F(function(){return A(_Ol,[_4O]);});},_Om=function(_On){return new F(function(){return A(_On,[_4O]);});},_Oo=function(_Op){return function(_Oq){return E(E(_Oq)[1])==46?[1,B(_N8(_NB,function(_Or){return new F(function(){return A(_Op,[[1,_Or]]);});}))]:[2];};},_Os=function(_Ot){return [0,B(_Oo(_Ot))];},_Ou=function(_Ov){return new F(function(){return _N8(_NB,function(_Ow){return [1,B(_Mz(_Os,_Ok,function(_Ox){return [1,B(_Mz(_Oa,_Om,function(_Oy){return new F(function(){return A(_Ov,[[5,[1,_Ow,_Ox,_Oy]]]);});}))];}))];});});},_Oz=function(_OA){return [1,B(_Ou(_OA))];},_OB=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_OC=function(_OD){return new F(function(){return _9r(_Jv,_OD,_OB);});},_OE=[0,8],_OF=[0,16],_OG=function(_OH){var _OI=function(_OJ){return new F(function(){return A(_OH,[[5,[0,_OE,_OJ]]]);});},_OK=function(_OL){return new F(function(){return A(_OH,[[5,[0,_OF,_OL]]]);});};return function(_OM){return E(E(_OM)[1])==48?E([0,function(_ON){switch(E(E(_ON)[1])){case 79:return [1,B(_N8(_OE,_OI))];case 88:return [1,B(_N8(_OF,_OK))];case 111:return [1,B(_N8(_OE,_OI))];case 120:return [1,B(_N8(_OF,_OK))];default:return [2];}}]):[2];};},_OO=function(_OP){return [0,B(_OG(_OP))];},_OQ=true,_OR=function(_OS){var _OT=new T(function(){return B(A(_OS,[_OE]));}),_OU=new T(function(){return B(A(_OS,[_OF]));});return function(_OV){switch(E(E(_OV)[1])){case 79:return E(_OT);case 88:return E(_OU);case 111:return E(_OT);case 120:return E(_OU);default:return [2];}};},_OW=function(_OX){return [0,B(_OR(_OX))];},_OY=[0,92],_OZ=function(_P0){return new F(function(){return A(_P0,[_NB]);});},_P1=function(_P2){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_P2,_9));}))));});},_P3=function(_P4){var _P5=E(_P4);return _P5[0]==0?E(_P5[1]):I_toInt(_P5[1]);},_P6=function(_P7,_P8){var _P9=E(_P7);if(!_P9[0]){var _Pa=_P9[1],_Pb=E(_P8);return _Pb[0]==0?_Pa<=_Pb[1]:I_compareInt(_Pb[1],_Pa)>=0;}else{var _Pc=_P9[1],_Pd=E(_P8);return _Pd[0]==0?I_compareInt(_Pc,_Pd[1])<=0:I_compare(_Pc,_Pd[1])<=0;}},_Pe=function(_Pf){return [2];},_Pg=function(_Ph){var _Pi=E(_Ph);if(!_Pi[0]){return E(_Pe);}else{var _Pj=_Pi[1],_Pk=E(_Pi[2]);return _Pk[0]==0?E(_Pj):function(_Pl){return new F(function(){return _LJ(B(A(_Pj,[_Pl])),new T(function(){return B(A(new T(function(){return B(_Pg(_Pk));}),[_Pl]));}));});};}},_Pm=function(_Pn){return [2];},_Po=function(_Pp,_Pq){var _Pr=function(_Ps,_Pt){var _Pu=E(_Ps);if(!_Pu[0]){return function(_Pv){return new F(function(){return A(_Pv,[_Pp]);});};}else{var _Pw=E(_Pt);return _Pw[0]==0?E(_Pm):E(_Pu[1])[1]!=E(_Pw[1])[1]?E(_Pm):function(_Px){return [0,function(_Py){return E(new T(function(){return B(A(new T(function(){return B(_Pr(_Pu[2],_Pw[2]));}),[_Px]));}));}];};}};return function(_Pz){return new F(function(){return A(_Pr,[_Pp,_Pz,_Pq]);});};},_PA=new T(function(){return B(unCStr("SOH"));}),_PB=[0,1],_PC=function(_PD){return [1,B(_Po(_PA,function(_PE){return E(new T(function(){return B(A(_PD,[_PB]));}));}))];},_PF=new T(function(){return B(unCStr("SO"));}),_PG=[0,14],_PH=function(_PI){return [1,B(_Po(_PF,function(_PJ){return E(new T(function(){return B(A(_PI,[_PG]));}));}))];},_PK=function(_PL){return [1,B(_Mz(_PC,_PH,_PL))];},_PM=new T(function(){return B(unCStr("NUL"));}),_PN=[0,0],_PO=function(_PP){return [1,B(_Po(_PM,function(_PQ){return E(new T(function(){return B(A(_PP,[_PN]));}));}))];},_PR=new T(function(){return B(unCStr("STX"));}),_PS=[0,2],_PT=function(_PU){return [1,B(_Po(_PR,function(_PV){return E(new T(function(){return B(A(_PU,[_PS]));}));}))];},_PW=new T(function(){return B(unCStr("ETX"));}),_PX=[0,3],_PY=function(_PZ){return [1,B(_Po(_PW,function(_Q0){return E(new T(function(){return B(A(_PZ,[_PX]));}));}))];},_Q1=new T(function(){return B(unCStr("EOT"));}),_Q2=[0,4],_Q3=function(_Q4){return [1,B(_Po(_Q1,function(_Q5){return E(new T(function(){return B(A(_Q4,[_Q2]));}));}))];},_Q6=new T(function(){return B(unCStr("ENQ"));}),_Q7=[0,5],_Q8=function(_Q9){return [1,B(_Po(_Q6,function(_Qa){return E(new T(function(){return B(A(_Q9,[_Q7]));}));}))];},_Qb=new T(function(){return B(unCStr("ACK"));}),_Qc=[0,6],_Qd=function(_Qe){return [1,B(_Po(_Qb,function(_Qf){return E(new T(function(){return B(A(_Qe,[_Qc]));}));}))];},_Qg=new T(function(){return B(unCStr("BEL"));}),_Qh=[0,7],_Qi=function(_Qj){return [1,B(_Po(_Qg,function(_Qk){return E(new T(function(){return B(A(_Qj,[_Qh]));}));}))];},_Ql=new T(function(){return B(unCStr("BS"));}),_Qm=[0,8],_Qn=function(_Qo){return [1,B(_Po(_Ql,function(_Qp){return E(new T(function(){return B(A(_Qo,[_Qm]));}));}))];},_Qq=new T(function(){return B(unCStr("HT"));}),_Qr=[0,9],_Qs=function(_Qt){return [1,B(_Po(_Qq,function(_Qu){return E(new T(function(){return B(A(_Qt,[_Qr]));}));}))];},_Qv=new T(function(){return B(unCStr("LF"));}),_Qw=[0,10],_Qx=function(_Qy){return [1,B(_Po(_Qv,function(_Qz){return E(new T(function(){return B(A(_Qy,[_Qw]));}));}))];},_QA=new T(function(){return B(unCStr("VT"));}),_QB=[0,11],_QC=function(_QD){return [1,B(_Po(_QA,function(_QE){return E(new T(function(){return B(A(_QD,[_QB]));}));}))];},_QF=new T(function(){return B(unCStr("FF"));}),_QG=[0,12],_QH=function(_QI){return [1,B(_Po(_QF,function(_QJ){return E(new T(function(){return B(A(_QI,[_QG]));}));}))];},_QK=new T(function(){return B(unCStr("CR"));}),_QL=[0,13],_QM=function(_QN){return [1,B(_Po(_QK,function(_QO){return E(new T(function(){return B(A(_QN,[_QL]));}));}))];},_QP=new T(function(){return B(unCStr("SI"));}),_QQ=[0,15],_QR=function(_QS){return [1,B(_Po(_QP,function(_QT){return E(new T(function(){return B(A(_QS,[_QQ]));}));}))];},_QU=new T(function(){return B(unCStr("DLE"));}),_QV=[0,16],_QW=function(_QX){return [1,B(_Po(_QU,function(_QY){return E(new T(function(){return B(A(_QX,[_QV]));}));}))];},_QZ=new T(function(){return B(unCStr("DC1"));}),_R0=[0,17],_R1=function(_R2){return [1,B(_Po(_QZ,function(_R3){return E(new T(function(){return B(A(_R2,[_R0]));}));}))];},_R4=new T(function(){return B(unCStr("DC2"));}),_R5=[0,18],_R6=function(_R7){return [1,B(_Po(_R4,function(_R8){return E(new T(function(){return B(A(_R7,[_R5]));}));}))];},_R9=new T(function(){return B(unCStr("DC3"));}),_Ra=[0,19],_Rb=function(_Rc){return [1,B(_Po(_R9,function(_Rd){return E(new T(function(){return B(A(_Rc,[_Ra]));}));}))];},_Re=new T(function(){return B(unCStr("DC4"));}),_Rf=[0,20],_Rg=function(_Rh){return [1,B(_Po(_Re,function(_Ri){return E(new T(function(){return B(A(_Rh,[_Rf]));}));}))];},_Rj=new T(function(){return B(unCStr("NAK"));}),_Rk=[0,21],_Rl=function(_Rm){return [1,B(_Po(_Rj,function(_Rn){return E(new T(function(){return B(A(_Rm,[_Rk]));}));}))];},_Ro=new T(function(){return B(unCStr("SYN"));}),_Rp=[0,22],_Rq=function(_Rr){return [1,B(_Po(_Ro,function(_Rs){return E(new T(function(){return B(A(_Rr,[_Rp]));}));}))];},_Rt=new T(function(){return B(unCStr("ETB"));}),_Ru=[0,23],_Rv=function(_Rw){return [1,B(_Po(_Rt,function(_Rx){return E(new T(function(){return B(A(_Rw,[_Ru]));}));}))];},_Ry=new T(function(){return B(unCStr("CAN"));}),_Rz=[0,24],_RA=function(_RB){return [1,B(_Po(_Ry,function(_RC){return E(new T(function(){return B(A(_RB,[_Rz]));}));}))];},_RD=new T(function(){return B(unCStr("EM"));}),_RE=[0,25],_RF=function(_RG){return [1,B(_Po(_RD,function(_RH){return E(new T(function(){return B(A(_RG,[_RE]));}));}))];},_RI=new T(function(){return B(unCStr("SUB"));}),_RJ=[0,26],_RK=function(_RL){return [1,B(_Po(_RI,function(_RM){return E(new T(function(){return B(A(_RL,[_RJ]));}));}))];},_RN=new T(function(){return B(unCStr("ESC"));}),_RO=[0,27],_RP=function(_RQ){return [1,B(_Po(_RN,function(_RR){return E(new T(function(){return B(A(_RQ,[_RO]));}));}))];},_RS=new T(function(){return B(unCStr("FS"));}),_RT=[0,28],_RU=function(_RV){return [1,B(_Po(_RS,function(_RW){return E(new T(function(){return B(A(_RV,[_RT]));}));}))];},_RX=new T(function(){return B(unCStr("GS"));}),_RY=[0,29],_RZ=function(_S0){return [1,B(_Po(_RX,function(_S1){return E(new T(function(){return B(A(_S0,[_RY]));}));}))];},_S2=new T(function(){return B(unCStr("RS"));}),_S3=[0,30],_S4=function(_S5){return [1,B(_Po(_S2,function(_S6){return E(new T(function(){return B(A(_S5,[_S3]));}));}))];},_S7=new T(function(){return B(unCStr("US"));}),_S8=[0,31],_S9=function(_Sa){return [1,B(_Po(_S7,function(_Sb){return E(new T(function(){return B(A(_Sa,[_S8]));}));}))];},_Sc=new T(function(){return B(unCStr("SP"));}),_Sd=[0,32],_Se=function(_Sf){return [1,B(_Po(_Sc,function(_Sg){return E(new T(function(){return B(A(_Sf,[_Sd]));}));}))];},_Sh=new T(function(){return B(unCStr("DEL"));}),_Si=[0,127],_Sj=function(_Sk){return [1,B(_Po(_Sh,function(_Sl){return E(new T(function(){return B(A(_Sk,[_Si]));}));}))];},_Sm=[1,_Sj,_9],_Sn=[1,_Se,_Sm],_So=[1,_S9,_Sn],_Sp=[1,_S4,_So],_Sq=[1,_RZ,_Sp],_Sr=[1,_RU,_Sq],_Ss=[1,_RP,_Sr],_St=[1,_RK,_Ss],_Su=[1,_RF,_St],_Sv=[1,_RA,_Su],_Sw=[1,_Rv,_Sv],_Sx=[1,_Rq,_Sw],_Sy=[1,_Rl,_Sx],_Sz=[1,_Rg,_Sy],_SA=[1,_Rb,_Sz],_SB=[1,_R6,_SA],_SC=[1,_R1,_SB],_SD=[1,_QW,_SC],_SE=[1,_QR,_SD],_SF=[1,_QM,_SE],_SG=[1,_QH,_SF],_SH=[1,_QC,_SG],_SI=[1,_Qx,_SH],_SJ=[1,_Qs,_SI],_SK=[1,_Qn,_SJ],_SL=[1,_Qi,_SK],_SM=[1,_Qd,_SL],_SN=[1,_Q8,_SM],_SO=[1,_Q3,_SN],_SP=[1,_PY,_SO],_SQ=[1,_PT,_SP],_SR=[1,_PO,_SQ],_SS=[1,_PK,_SR],_ST=new T(function(){return B(_Pg(_SS));}),_SU=[0,1114111],_SV=[0,34],_SW=[0,39],_SX=function(_SY){var _SZ=new T(function(){return B(A(_SY,[_Qh]));}),_T0=new T(function(){return B(A(_SY,[_Qm]));}),_T1=new T(function(){return B(A(_SY,[_Qr]));}),_T2=new T(function(){return B(A(_SY,[_Qw]));}),_T3=new T(function(){return B(A(_SY,[_QB]));}),_T4=new T(function(){return B(A(_SY,[_QG]));}),_T5=new T(function(){return B(A(_SY,[_QL]));});return new F(function(){return _LJ([0,function(_T6){switch(E(E(_T6)[1])){case 34:return E(new T(function(){return B(A(_SY,[_SV]));}));case 39:return E(new T(function(){return B(A(_SY,[_SW]));}));case 92:return E(new T(function(){return B(A(_SY,[_OY]));}));case 97:return E(_SZ);case 98:return E(_T0);case 102:return E(_T4);case 110:return E(_T2);case 114:return E(_T5);case 116:return E(_T1);case 118:return E(_T3);default:return [2];}}],new T(function(){return B(_LJ([1,B(_Mz(_OW,_OZ,function(_T7){return [1,B(_N8(_T7,function(_T8){var _T9=B(_O4(new T(function(){return B(_NU(E(_T7)[1]));}),_NT,_T8));return !B(_P6(_T9,_SU))?[2]:B(A(_SY,[new T(function(){var _Ta=B(_P3(_T9));if(_Ta>>>0>1114111){var _Tb=B(_P1(_Ta));}else{var _Tb=[0,_Ta];}var _Tc=_Tb,_Td=_Tc,_Te=_Td;return _Te;})]));}))];}))],new T(function(){return B(_LJ([0,function(_Tf){return E(E(_Tf)[1])==94?E([0,function(_Tg){switch(E(E(_Tg)[1])){case 64:return E(new T(function(){return B(A(_SY,[_PN]));}));case 65:return E(new T(function(){return B(A(_SY,[_PB]));}));case 66:return E(new T(function(){return B(A(_SY,[_PS]));}));case 67:return E(new T(function(){return B(A(_SY,[_PX]));}));case 68:return E(new T(function(){return B(A(_SY,[_Q2]));}));case 69:return E(new T(function(){return B(A(_SY,[_Q7]));}));case 70:return E(new T(function(){return B(A(_SY,[_Qc]));}));case 71:return E(_SZ);case 72:return E(_T0);case 73:return E(_T1);case 74:return E(_T2);case 75:return E(_T3);case 76:return E(_T4);case 77:return E(_T5);case 78:return E(new T(function(){return B(A(_SY,[_PG]));}));case 79:return E(new T(function(){return B(A(_SY,[_QQ]));}));case 80:return E(new T(function(){return B(A(_SY,[_QV]));}));case 81:return E(new T(function(){return B(A(_SY,[_R0]));}));case 82:return E(new T(function(){return B(A(_SY,[_R5]));}));case 83:return E(new T(function(){return B(A(_SY,[_Ra]));}));case 84:return E(new T(function(){return B(A(_SY,[_Rf]));}));case 85:return E(new T(function(){return B(A(_SY,[_Rk]));}));case 86:return E(new T(function(){return B(A(_SY,[_Rp]));}));case 87:return E(new T(function(){return B(A(_SY,[_Ru]));}));case 88:return E(new T(function(){return B(A(_SY,[_Rz]));}));case 89:return E(new T(function(){return B(A(_SY,[_RE]));}));case 90:return E(new T(function(){return B(A(_SY,[_RJ]));}));case 91:return E(new T(function(){return B(A(_SY,[_RO]));}));case 92:return E(new T(function(){return B(A(_SY,[_RT]));}));case 93:return E(new T(function(){return B(A(_SY,[_RY]));}));case 94:return E(new T(function(){return B(A(_SY,[_S3]));}));case 95:return E(new T(function(){return B(A(_SY,[_S8]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_ST,[_SY]));})));})));}));});},_Th=function(_Ti){return new F(function(){return A(_Ti,[_6B]);});},_Tj=function(_Tk){var _Tl=E(_Tk);if(!_Tl[0]){return E(_Th);}else{var _Tm=_Tl[2],_Tn=E(E(_Tl[1])[1]);switch(_Tn){case 9:return function(_To){return [0,function(_Tp){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_To]));}));}];};case 10:return function(_Tq){return [0,function(_Tr){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_Tq]));}));}];};case 11:return function(_Ts){return [0,function(_Tt){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_Ts]));}));}];};case 12:return function(_Tu){return [0,function(_Tv){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_Tu]));}));}];};case 13:return function(_Tw){return [0,function(_Tx){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_Tw]));}));}];};case 32:return function(_Ty){return [0,function(_Tz){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_Ty]));}));}];};case 160:return function(_TA){return [0,function(_TB){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_TA]));}));}];};default:var _TC=u_iswspace(_Tn),_TD=_TC;return E(_TD)==0?E(_Th):function(_TE){return [0,function(_TF){return E(new T(function(){return B(A(new T(function(){return B(_Tj(_Tm));}),[_TE]));}));}];};}}},_TG=function(_TH){var _TI=new T(function(){return B(_TG(_TH));}),_TJ=[1,function(_TK){return new F(function(){return A(_Tj,[_TK,function(_TL){return E([0,function(_TM){return E(E(_TM)[1])==92?E(_TI):[2];}]);}]);});}];return new F(function(){return _LJ([0,function(_TN){return E(E(_TN)[1])==92?E([0,function(_TO){var _TP=E(E(_TO)[1]);switch(_TP){case 9:return E(_TJ);case 10:return E(_TJ);case 11:return E(_TJ);case 12:return E(_TJ);case 13:return E(_TJ);case 32:return E(_TJ);case 38:return E(_TI);case 160:return E(_TJ);default:var _TQ=u_iswspace(_TP),_TR=_TQ;return E(_TR)==0?[2]:E(_TJ);}}]):[2];}],[0,function(_TS){var _TT=E(_TS);return E(_TT[1])==92?E(new T(function(){return B(_SX(function(_TU){return new F(function(){return A(_TH,[[0,_TU,_OQ]]);});}));})):B(A(_TH,[[0,_TT,_4y]]));}]);});},_TV=function(_TW,_TX){return new F(function(){return _TG(function(_TY){var _TZ=E(_TY),_U0=E(_TZ[1]);if(E(_U0[1])==34){if(!E(_TZ[2])){return E(new T(function(){return B(A(_TX,[[1,new T(function(){return B(A(_TW,[_9]));})]]));}));}else{return new F(function(){return _TV(function(_U1){return new F(function(){return A(_TW,[[1,_U0,_U1]]);});},_TX);});}}else{return new F(function(){return _TV(function(_U2){return new F(function(){return A(_TW,[[1,_U0,_U2]]);});},_TX);});}});});},_U3=new T(function(){return B(unCStr("_\'"));}),_U4=function(_U5){var _U6=u_iswalnum(_U5),_U7=_U6;return E(_U7)==0?B(_9r(_Jv,[0,_U5],_U3)):true;},_U8=function(_U9){return new F(function(){return _U4(E(_U9)[1]);});},_Ua=new T(function(){return B(unCStr(",;()[]{}`"));}),_Ub=new T(function(){return B(unCStr(".."));}),_Uc=new T(function(){return B(unCStr("::"));}),_Ud=new T(function(){return B(unCStr("->"));}),_Ue=[0,64],_Uf=[1,_Ue,_9],_Ug=[0,126],_Uh=[1,_Ug,_9],_Ui=new T(function(){return B(unCStr("=>"));}),_Uj=[1,_Ui,_9],_Uk=[1,_Uh,_Uj],_Ul=[1,_Uf,_Uk],_Um=[1,_Ud,_Ul],_Un=new T(function(){return B(unCStr("<-"));}),_Uo=[1,_Un,_Um],_Up=[0,124],_Uq=[1,_Up,_9],_Ur=[1,_Uq,_Uo],_Us=[1,_OY,_9],_Ut=[1,_Us,_Ur],_Uu=[0,61],_Uv=[1,_Uu,_9],_Uw=[1,_Uv,_Ut],_Ux=[1,_Uc,_Uw],_Uy=[1,_Ub,_Ux],_Uz=function(_UA){return new F(function(){return _LJ([1,function(_UB){return E(_UB)[0]==0?E(new T(function(){return B(A(_UA,[_N5]));})):[2];}],new T(function(){return B(_LJ([0,function(_UC){return E(E(_UC)[1])==39?E([0,function(_UD){var _UE=E(_UD);switch(E(_UE[1])){case 39:return [2];case 92:return E(new T(function(){return B(_SX(function(_UF){return [0,function(_UG){return E(E(_UG)[1])==39?E(new T(function(){return B(A(_UA,[[0,_UF]]));})):[2];}];}));}));default:return [0,function(_UH){return E(E(_UH)[1])==39?E(new T(function(){return B(A(_UA,[[0,_UE]]));})):[2];}];}}]):[2];}],new T(function(){return B(_LJ([0,function(_UI){return E(E(_UI)[1])==34?E(new T(function(){return B(_TV(_6P,_UA));})):[2];}],new T(function(){return B(_LJ([0,function(_UJ){return !B(_9r(_Jv,_UJ,_Ua))?[2]:B(A(_UA,[[2,[1,_UJ,_9]]]));}],new T(function(){return B(_LJ([0,function(_UK){return !B(_9r(_Jv,_UK,_OB))?[2]:[1,B(_MU(_OC,function(_UL){var _UM=[1,_UK,_UL];return !B(_9r(_8H,_UM,_Uy))?B(A(_UA,[[4,_UM]])):B(A(_UA,[[2,_UM]]));}))];}],new T(function(){return B(_LJ([0,function(_UN){var _UO=E(_UN),_UP=_UO[1],_UQ=u_iswalpha(_UP),_UR=_UQ;return E(_UR)==0?E(_UP)==95?[1,B(_MU(_U8,function(_US){return new F(function(){return A(_UA,[[3,[1,_UO,_US]]]);});}))]:[2]:[1,B(_MU(_U8,function(_UT){return new F(function(){return A(_UA,[[3,[1,_UO,_UT]]]);});}))];}],new T(function(){return [1,B(_Mz(_OO,_Oz,_UA))];})));})));})));})));})));}));});},_UU=[0,0],_UV=function(_UW,_UX){return function(_UY){return new F(function(){return A(_Tj,[_UY,function(_UZ){return E(new T(function(){return B(_Uz(function(_V0){var _V1=E(_V0);return _V1[0]==2?!B(_3x(_V1[1],_Mf))?[2]:E(new T(function(){return B(A(_UW,[_UU,function(_V2){return [1,function(_V3){return new F(function(){return A(_Tj,[_V3,function(_V4){return E(new T(function(){return B(_Uz(function(_V5){var _V6=E(_V5);return _V6[0]==2?!B(_3x(_V6[1],_Md))?[2]:E(new T(function(){return B(A(_UX,[_V2]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_V7=function(_V8,_V9,_Va){var _Vb=function(_Vc,_Vd){return new F(function(){return _LJ([1,function(_Ve){return new F(function(){return A(_Tj,[_Ve,function(_Vf){return E(new T(function(){return B(_Uz(function(_Vg){var _Vh=E(_Vg);if(_Vh[0]==4){var _Vi=E(_Vh[1]);if(!_Vi[0]){return new F(function(){return A(_V8,[_Vh,_Vc,_Vd]);});}else{return E(E(_Vi[1])[1])==45?E(_Vi[2])[0]==0?E([1,function(_Vj){return new F(function(){return A(_Tj,[_Vj,function(_Vk){return E(new T(function(){return B(_Uz(function(_Vl){return new F(function(){return A(_V8,[_Vl,_Vc,function(_Vm){return new F(function(){return A(_Vd,[new T(function(){return [0, -E(_Vm)[1]];})]);});}]);});}));}));}]);});}]):B(A(_V8,[_Vh,_Vc,_Vd])):B(A(_V8,[_Vh,_Vc,_Vd]));}}else{return new F(function(){return A(_V8,[_Vh,_Vc,_Vd]);});}}));}));}]);});}],new T(function(){return [1,B(_UV(_Vb,_Vd))];}));});};return new F(function(){return _Vb(_V9,_Va);});},_Vn=function(_Vo,_Vp){return [2];},_Vq=function(_Vr){var _Vs=E(_Vr);return _Vs[0]==0?[1,new T(function(){return B(_O4(new T(function(){return B(_NU(E(_Vs[1])[1]));}),_NT,_Vs[2]));})]:E(_Vs[2])[0]==0?E(_Vs[3])[0]==0?[1,new T(function(){return B(_O4(_NS,_NT,_Vs[1]));})]:[0]:[0];},_Vt=function(_Vu){var _Vv=E(_Vu);if(_Vv[0]==5){var _Vw=B(_Vq(_Vv[1]));return _Vw[0]==0?E(_Vn):function(_Vx,_Vy){return new F(function(){return A(_Vy,[new T(function(){return [0,B(_P3(_Vw[1]))];})]);});};}else{return E(_Vn);}},_Vz=function(_VA){return [1,function(_VB){return new F(function(){return A(_Tj,[_VB,function(_VC){return E([3,_VA,_Mr]);}]);});}];},_VD=new T(function(){return B(_V7(_Vt,_UU,_Vz));}),_VE=function(_VF){while(1){var _VG=(function(_VH){var _VI=E(_VH);if(!_VI[0]){return [0];}else{var _VJ=_VI[2],_VK=E(_VI[1]);if(!E(_VK[2])[0]){return [1,_VK[1],new T(function(){return B(_VE(_VJ));})];}else{_VF=_VJ;return null;}}})(_VF);if(_VG!=null){return _VG;}}},_VL=function(_VM){var _VN=B(_VE(B(_Lz(_VD,_VM))));return _VN[0]==0?E(_Lv):E(_VN[2])[0]==0?E(_VN[1]):E(_Lx);},_VO=function(_VP,_VQ,_VR,_VS,_VT){var _VU=function(_VV,_VW,_VX){var _VY=function(_VZ,_W0,_W1){return new F(function(){return A(_VX,[[0,_VP,new T(function(){return B(_3d(_VL,_VZ));})],_W0,new T(function(){var _W2=E(E(_W0)[2]),_W3=E(_W1),_W4=E(_W3[1]),_W5=B(_E7(_W4[1],_W4[2],_W4[3],_W3[2],_W2[1],_W2[2],_W2[3],_9));return [0,E(_W5[1]),_W5[2]];})]);});},_W6=function(_W7){return new F(function(){return _VY(_9,_VV,new T(function(){var _W8=E(E(_VV)[2]),_W9=E(_W7),_Wa=E(_W9[1]),_Wb=B(_E7(_Wa[1],_Wa[2],_Wa[3],_W9[2],_W8[1],_W8[2],_W8[3],_9));return [0,E(_Wb[1]),_Wb[2]];},1));});};return new F(function(){return _G2(_L2,_Lt,_VV,function(_Wc,_Wd,_We){return new F(function(){return A(_VW,[[0,_VP,new T(function(){return B(_3d(_VL,_Wc));})],_Wd,new T(function(){var _Wf=E(E(_Wd)[2]),_Wg=E(_We),_Wh=E(_Wg[1]),_Wi=B(_E7(_Wh[1],_Wh[2],_Wh[3],_Wg[2],_Wf[1],_Wf[2],_Wf[3],_9));return [0,E(_Wi[1]),_Wi[2]];})]);});},_W6,_VY,_W6);});};return new F(function(){return _FC(_JP,_VQ,function(_Wj,_Wk,_Wl){return new F(function(){return _VU(_Wk,_VR,function(_Wm,_Wn,_Wo){return new F(function(){return A(_VR,[_Wm,_Wn,new T(function(){return B(_ER(_Wl,_Wo));})]);});});});},_VS,function(_Wp,_Wq,_Wr){return new F(function(){return _VU(_Wq,_VR,function(_Ws,_Wt,_Wu){return new F(function(){return A(_VT,[_Ws,_Wt,new T(function(){return B(_ER(_Wr,_Wu));})]);});});});});});},_Wv=new T(function(){return B(unCStr("letter or digit"));}),_Ww=[1,_Wv,_9],_Wx=function(_Wy){var _Wz=u_iswalnum(E(_Wy)[1]),_WA=_Wz;return E(_WA)==0?false:true;},_WB=function(_WC,_WD,_WE,_WF,_WG){var _WH=E(_WC),_WI=E(_WH[2]);return new F(function(){return _J3(_Hd,_KJ,_Wx,_WH[1],_WI[1],_WI[2],_WI[3],_WH[3],_WD,_WG);});},_WJ=function(_WK,_WL,_WM,_WN,_WO){return new F(function(){return _Kq(_WB,_Ww,_WK,_WL,_WM,_WN,_WO);});},_WP=function(_WQ,_WR,_WS,_WT,_WU){return new F(function(){return _EZ(_WJ,_WQ,function(_WV,_WW,_WX){return new F(function(){return _VO(_WV,_WW,_WR,_WS,function(_WY,_WZ,_X0){return new F(function(){return A(_WR,[_WY,_WZ,new T(function(){return B(_ER(_WX,_X0));})]);});});});},_WU,function(_X1,_X2,_X3){return new F(function(){return _VO(_X1,_X2,_WR,_WS,function(_X4,_X5,_X6){return new F(function(){return A(_WT,[_X4,_X5,new T(function(){return B(_ER(_X3,_X6));})]);});});});},_WU);});},_X7=new T(function(){return B(unCStr("SHOW"));}),_X8=[0,_X7,_9],_X9=function(_Xa,_Xb,_Xc,_Xd){var _Xe=function(_Xf){return new F(function(){return A(_Xd,[[0,_Xa,_X8],_Xb,new T(function(){var _Xg=E(E(_Xb)[2]),_Xh=_Xg[1],_Xi=_Xg[2],_Xj=_Xg[3],_Xk=E(_Xf),_Xl=E(_Xk[1]),_Xm=B(_E7(_Xl[1],_Xl[2],_Xl[3],_Xk[2],_Xh,_Xi,_Xj,_9)),_Xn=E(_Xm[1]),_Xo=B(_E7(_Xn[1],_Xn[2],_Xn[3],_Xm[2],_Xh,_Xi,_Xj,_9));return [0,E(_Xo[1]),_Xo[2]];})]);});};return new F(function(){return _WP(_Xb,function(_Xp,_Xq,_Xr){return new F(function(){return A(_Xc,[[0,_Xa,_Xp],_Xq,new T(function(){var _Xs=E(E(_Xq)[2]),_Xt=E(_Xr),_Xu=E(_Xt[1]),_Xv=B(_E7(_Xu[1],_Xu[2],_Xu[3],_Xt[2],_Xs[1],_Xs[2],_Xs[3],_9));return [0,E(_Xv[1]),_Xv[2]];})]);});},_Xe,function(_Xw,_Xx,_Xy){return new F(function(){return A(_Xd,[[0,_Xa,_Xw],_Xx,new T(function(){var _Xz=E(E(_Xx)[2]),_XA=E(_Xy),_XB=E(_XA[1]),_XC=B(_E7(_XB[1],_XB[2],_XB[3],_XA[2],_Xz[1],_Xz[2],_Xz[3],_9));return [0,E(_XC[1]),_XC[2]];})]);});},_Xe);});},_XD=new T(function(){return B(unCStr("sS"));}),_XE=new T(function(){return B(_L8(_JG));}),_XF=[0,58],_XG=new T(function(){return B(_Lb(_XE,_XF));}),_XH=[1,_Wv,_9],_XI=function(_XJ,_XK,_XL,_XM,_XN,_XO,_XP,_XQ,_XR){var _XS=function(_XT){var _XU=new T(function(){var _XV=E(_XT),_XW=B(_K5(_XV[1],_XV[2],_XH));return [0,E(_XW[1]),_XW[2]];});return new F(function(){return A(_XG,[[0,_XJ,E([0,_XK,_XL,_XM]),E(_XN)],_XO,_XP,function(_XX,_XY,_XZ){return new F(function(){return A(_XQ,[_XX,_XY,new T(function(){return B(_ER(_XU,_XZ));})]);});},function(_Y0){return new F(function(){return A(_XR,[new T(function(){return B(_ER(_XU,_Y0));})]);});}]);});},_Y1=E(_XJ);if(!_Y1[0]){return new F(function(){return _XS([0,E([0,_XK,_XL,_XM]),_Hj]);});}else{var _Y2=_Y1[2],_Y3=E(_Y1[1]),_Y4=_Y3[1],_Y5=u_iswalnum(_Y4),_Y6=_Y5;if(!E(_Y6)){return new F(function(){return _XS([0,E([0,_XK,_XL,_XM]),[1,[0,E([1,_Hg,new T(function(){return B(_IX([1,_Y3,_9],_Hh));})])],_9]]);});}else{switch(E(_Y4)){case 9:var _Y7=[0,_XK,_XL,(_XM+8|0)-B(_Hk(_XM-1|0,8))|0];break;case 10:var _Y7=[0,_XK,_XL+1|0,1];break;default:var _Y7=[0,_XK,_XL,_XM+1|0];}var _Y8=_Y7,_Y9=[0,E(_Y8),_9],_Ya=[0,_Y2,E(_Y8),E(_XN)];return new F(function(){return A(_XO,[_Y3,_Ya,_Y9]);});}}},_Yb=function(_Yc,_Yd,_Ye,_Yf,_Yg){var _Yh=E(_Yc),_Yi=E(_Yh[2]);return new F(function(){return _XI(_Yh[1],_Yi[1],_Yi[2],_Yi[3],_Yh[3],_Yd,_Ye,_Yf,_Yg);});},_Yj=[0,10],_Yk=new T(function(){return B(unCStr("lf new-line"));}),_Yl=[1,_Yk,_9],_Ym=function(_Yn){return function(_Yo,_Yp,_Yq,_Yr,_Ys){return new F(function(){return _Kq(new T(function(){return B(_Lb(_Yn,_Yj));}),_Yl,_Yo,_Yp,_Yq,_Yr,_Ys);});};},_Yt=new T(function(){return B(_Ym(_XE));}),_Yu=function(_Yv,_Yw,_Yx,_Yy,_Yz,_YA,_YB){var _YC=function(_YD,_YE,_YF,_YG,_YH,_YI){return new F(function(){return _YJ(_YE,function(_YK,_YL,_YM){return new F(function(){return A(_YF,[[1,_YD,_YK],_YL,new T(function(){var _YN=E(E(_YL)[2]),_YO=E(_YM),_YP=E(_YO[1]),_YQ=B(_E7(_YP[1],_YP[2],_YP[3],_YO[2],_YN[1],_YN[2],_YN[3],_9));return [0,E(_YQ[1]),_YQ[2]];})]);});},_YG,function(_YR,_YS,_YT){return new F(function(){return A(_YH,[[1,_YD,_YR],_YS,new T(function(){var _YU=E(E(_YS)[2]),_YV=E(_YT),_YW=E(_YV[1]),_YX=B(_E7(_YW[1],_YW[2],_YW[3],_YV[2],_YU[1],_YU[2],_YU[3],_9));return [0,E(_YX[1]),_YX[2]];})]);});},_YI);});},_YJ=function(_YY,_YZ,_Z0,_Z1,_Z2){return new F(function(){return A(_Yw,[_YY,function(_Z3,_Z4,_Z5){return new F(function(){return A(_YZ,[_9,_Z4,new T(function(){var _Z6=E(E(_Z4)[2]),_Z7=E(_Z5),_Z8=E(_Z7[1]),_Z9=B(_E7(_Z8[1],_Z8[2],_Z8[3],_Z7[2],_Z6[1],_Z6[2],_Z6[3],_9));return [0,E(_Z9[1]),_Z9[2]];})]);});},_Z0,function(_Za,_Zb,_Zc){return new F(function(){return A(_Z1,[_9,_Zb,new T(function(){var _Zd=E(E(_Zb)[2]),_Ze=E(_Zc),_Zf=E(_Ze[1]),_Zg=B(_E7(_Zf[1],_Zf[2],_Zf[3],_Ze[2],_Zd[1],_Zd[2],_Zd[3],_9));return [0,E(_Zg[1]),_Zg[2]];})]);});},function(_Zh){return new F(function(){return A(_Yv,[_YY,function(_Zi,_Zj,_Zk){return new F(function(){return _YC(_Zi,_Zj,_YZ,_Z0,function(_Zl,_Zm,_Zn){return new F(function(){return A(_YZ,[_Zl,_Zm,new T(function(){return B(_ER(_Zk,_Zn));})]);});},function(_Zo){return new F(function(){return A(_Z0,[new T(function(){return B(_ER(_Zk,_Zo));})]);});});});},_Z0,function(_Zp,_Zq,_Zr){return new F(function(){return _YC(_Zp,_Zq,_YZ,_Z0,function(_Zs,_Zt,_Zu){return new F(function(){return A(_Z1,[_Zs,_Zt,new T(function(){var _Zv=E(_Zh),_Zw=E(_Zv[1]),_Zx=E(_Zr),_Zy=E(_Zx[1]),_Zz=E(_Zu),_ZA=E(_Zz[1]),_ZB=B(_E7(_Zy[1],_Zy[2],_Zy[3],_Zx[2],_ZA[1],_ZA[2],_ZA[3],_Zz[2])),_ZC=E(_ZB[1]),_ZD=B(_E7(_Zw[1],_Zw[2],_Zw[3],_Zv[2],_ZC[1],_ZC[2],_ZC[3],_ZB[2]));return [0,E(_ZD[1]),_ZD[2]];})]);});},function(_ZE){return new F(function(){return A(_Z2,[new T(function(){var _ZF=E(_Zh),_ZG=E(_ZF[1]),_ZH=E(_Zr),_ZI=E(_ZH[1]),_ZJ=E(_ZE),_ZK=E(_ZJ[1]),_ZL=B(_E7(_ZI[1],_ZI[2],_ZI[3],_ZH[2],_ZK[1],_ZK[2],_ZK[3],_ZJ[2])),_ZM=E(_ZL[1]),_ZN=B(_E7(_ZG[1],_ZG[2],_ZG[3],_ZF[2],_ZM[1],_ZM[2],_ZM[3],_ZL[2]));return [0,E(_ZN[1]),_ZN[2]];})]);});});});},function(_ZO){return new F(function(){return A(_Z2,[new T(function(){return B(_ER(_Zh,_ZO));})]);});}]);});}]);});};return new F(function(){return _YJ(_Yx,_Yy,_Yz,_YA,_YB);});},_ZP=new T(function(){return B(unCStr("tab"));}),_ZQ=[1,_ZP,_9],_ZR=[0,9],_ZS=function(_ZT){return function(_ZU,_ZV,_ZW,_ZX,_ZY){return new F(function(){return _Kq(new T(function(){return B(_Lb(_ZT,_ZR));}),_ZQ,_ZU,_ZV,_ZW,_ZX,_ZY);});};},_ZZ=new T(function(){return B(_ZS(_XE));}),_100=[0,39],_101=[1,_100,_9],_102=new T(function(){return B(unCStr("\'\\\'\'"));}),_103=function(_104){var _105=E(E(_104)[1]);return _105==39?E(_102):[1,_100,new T(function(){return B(_IG(_105,_101));})];},_106=function(_107,_108){return [1,_Hg,new T(function(){return B(_IX(_107,[1,_Hg,_108]));})];},_109=function(_10a){return new F(function(){return _e(_102,_10a);});},_10b=function(_10c,_10d){var _10e=E(E(_10d)[1]);return _10e==39?E(_109):function(_10f){return [1,_100,new T(function(){return B(_IG(_10e,[1,_100,_10f]));})];};},_10g=[0,_10b,_103,_106],_10h=function(_10i,_10j,_10k,_10l,_10m){var _10n=new T(function(){return B(_bT(_10i));}),_10o=function(_10p){return new F(function(){return A(_10l,[_6B,_10k,new T(function(){var _10q=E(E(_10k)[2]),_10r=E(_10p),_10s=E(_10r[1]),_10t=B(_E7(_10s[1],_10s[2],_10s[3],_10r[2],_10q[1],_10q[2],_10q[3],_9));return [0,E(_10t[1]),_10t[2]];})]);});};return new F(function(){return A(_10j,[_10k,function(_10u,_10v,_10w){return new F(function(){return A(_10m,[new T(function(){var _10x=E(E(_10v)[2]),_10y=E(_10w),_10z=E(_10y[1]),_10A=B(_E7(_10z[1],_10z[2],_10z[3],_10y[2],_10x[1],_10x[2],_10x[3],[1,new T(function(){return [1,E(B(A(_10n,[_10u])))];}),_9]));return [0,E(_10A[1]),_10A[2]];})]);});},_10o,function(_10B,_10C,_10D){return new F(function(){return A(_10l,[_6B,_10k,new T(function(){var _10E=E(E(_10k)[2]),_10F=E(E(_10C)[2]),_10G=E(_10D),_10H=E(_10G[1]),_10I=B(_E7(_10H[1],_10H[2],_10H[3],_10G[2],_10F[1],_10F[2],_10F[3],[1,new T(function(){return [1,E(B(A(_10n,[_10B])))];}),_9])),_10J=E(_10I[1]),_10K=B(_E7(_10J[1],_10J[2],_10J[3],_10I[2],_10E[1],_10E[2],_10E[3],_9));return [0,E(_10K[1]),_10K[2]];})]);});},_10o]);});},_10L=function(_10M,_10N,_10O){return new F(function(){return _10h(_10g,_ZZ,_10M,function(_10P,_10Q,_10R){return new F(function(){return A(_10N,[_6B,_10Q,new T(function(){var _10S=E(E(_10Q)[2]),_10T=E(_10R),_10U=E(_10T[1]),_10V=B(_E7(_10U[1],_10U[2],_10U[3],_10T[2],_10S[1],_10S[2],_10S[3],_9));return [0,E(_10V[1]),_10V[2]];})]);});},_10O);});},_10W=function(_10X,_10Y,_10Z,_110,_111){return new F(function(){return A(_Yt,[_10X,function(_112,_113,_114){return new F(function(){return _10L(_113,function(_115,_116,_117){return new F(function(){return A(_10Y,[_115,_116,new T(function(){return B(_ER(_114,_117));})]);});},function(_118){return new F(function(){return A(_10Z,[new T(function(){return B(_ER(_114,_118));})]);});});});},_10Z,function(_119,_11a,_11b){return new F(function(){return _10L(_11a,function(_11c,_11d,_11e){return new F(function(){return A(_110,[_11c,_11d,new T(function(){return B(_ER(_11b,_11e));})]);});},function(_11f){return new F(function(){return A(_111,[new T(function(){return B(_ER(_11b,_11f));})]);});});});},_111]);});},_11g=[0,E(_9)],_11h=[1,_11g,_9],_11i=function(_11j,_11k,_11l,_11m,_11n,_11o,_11p){return new F(function(){return A(_11j,[new T(function(){return B(A(_11k,[_11l]));}),function(_11q){var _11r=E(_11q);if(!_11r[0]){return E(new T(function(){return B(A(_11p,[[0,E(_11m),_11h]]));}));}else{var _11s=E(_11r[1]);return new F(function(){return A(_11o,[_11s[1],[0,_11s[2],E(_11m),E(_11n)],[0,E(_11m),_9]]);});}}]);});},_11t=new T(function(){return B(unCStr("end of input"));}),_11u=[1,_11t,_9],_11v=function(_11w,_11x,_11y,_11z,_11A,_11B,_11C,_11D){return new F(function(){return _Kq(function(_11E,_11F,_11G,_11H,_11I){return new F(function(){return _10h(_11y,function(_11J,_11K,_11L,_11M,_11N){var _11O=E(_11J);return new F(function(){return _11i(_11w,_11x,_11O[1],_11O[2],_11O[3],_11K,_11N);});},_11E,_11H,_11I);});},_11u,_11z,_11A,_11B,_11C,_11D);});},_11P=function(_11Q,_11R,_11S,_11T,_11U){return new F(function(){return _Ep(_Yt,_11Q,function(_11V,_11W,_11X){return new F(function(){return _11v(_Hd,_JN,_10g,_11W,_11R,_11S,function(_11Y,_11Z,_120){return new F(function(){return A(_11R,[_11Y,_11Z,new T(function(){return B(_ER(_11X,_120));})]);});},function(_121){return new F(function(){return A(_11S,[new T(function(){return B(_ER(_11X,_121));})]);});});});},_11S,function(_122,_123,_124){return new F(function(){return _11v(_Hd,_JN,_10g,_123,_11R,_11S,function(_125,_126,_127){return new F(function(){return A(_11T,[_125,_126,new T(function(){return B(_ER(_124,_127));})]);});},function(_128){return new F(function(){return A(_11U,[new T(function(){return B(_ER(_124,_128));})]);});});});});});},_129=function(_12a,_12b,_12c,_12d){var _12e=function(_12f){var _12g=function(_12h){return new F(function(){return A(_12d,[new T(function(){return B(_ER(_12f,_12h));})]);});};return new F(function(){return _10W(_12a,_12b,_12g,function(_12i,_12j,_12k){return new F(function(){return A(_12c,[_12i,_12j,new T(function(){return B(_ER(_12f,_12k));})]);});},_12g);});};return new F(function(){return _11P(_12a,_12b,_12e,_12c,_12e);});},_12l=function(_12m,_12n,_12o,_12p,_12q){return new F(function(){return _129(_12m,_12n,_12p,_12q);});},_12r=function(_12s){return true;},_12t=function(_12u,_12v,_12w,_12x,_12y){var _12z=E(_12u),_12A=E(_12z[2]);return new F(function(){return _J3(_Hd,_JN,_12r,_12z[1],_12A[1],_12A[2],_12A[3],_12z[3],_12v,_12y);});},_12B=function(_12C,_12D,_12E,_12F,_12G){return new F(function(){return A(_ZZ,[_12C,function(_12H,_12I,_12J){return new F(function(){return _Yu(_12t,_12l,_12I,_12D,_12E,function(_12K,_12L,_12M){return new F(function(){return A(_12D,[_12K,_12L,new T(function(){return B(_ER(_12J,_12M));})]);});},function(_12N){return new F(function(){return A(_12E,[new T(function(){return B(_ER(_12J,_12N));})]);});});});},_12E,function(_12O,_12P,_12Q){return new F(function(){return _Yu(_12t,_12l,_12P,_12D,_12E,function(_12R,_12S,_12T){return new F(function(){return A(_12F,[_12R,_12S,new T(function(){return B(_ER(_12Q,_12T));})]);});},function(_12U){return new F(function(){return A(_12G,[new T(function(){return B(_ER(_12Q,_12U));})]);});});});},_12G]);});},_12V=[0,_X7,_9],_12W=[0,_9,1,1],_12X=function(_12Y){return E(_12Y);},_12Z=new T(function(){return B(_iw("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_130=new T(function(){return B(_iw("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_131=[0,_Hd,_130,_12X,_12Z],_132=function(_133){return new F(function(){return unAppCStr("string error",new T(function(){return B(_bh(_133));}));});},_134=function(_135,_136,_137,_138,_139){return new F(function(){return A(_ZZ,[_136,function(_13a,_13b,_13c){return new F(function(){return A(_137,[_135,_13b,new T(function(){var _13d=E(E(_13b)[2]),_13e=E(_13c),_13f=E(_13e[1]),_13g=B(_E7(_13f[1],_13f[2],_13f[3],_13e[2],_13d[1],_13d[2],_13d[3],_9));return [0,E(_13g[1]),_13g[2]];})]);});},_139,function(_13h,_13i,_13j){return new F(function(){return A(_138,[_135,_13i,new T(function(){var _13k=E(E(_13i)[2]),_13l=E(_13j),_13m=E(_13l[1]),_13n=B(_E7(_13m[1],_13m[2],_13m[3],_13l[2],_13k[1],_13k[2],_13k[3],_9));return [0,E(_13n[1]),_13n[2]];})]);});},_139]);});},_13o=function(_13p,_13q,_13r,_13s,_13t){return new F(function(){return A(_Yt,[_13p,function(_13u,_13v,_13w){return new F(function(){return _134(_13u,_13v,_13q,function(_13x,_13y,_13z){return new F(function(){return A(_13q,[_13x,_13y,new T(function(){return B(_ER(_13w,_13z));})]);});},function(_13A){return new F(function(){return A(_13r,[new T(function(){return B(_ER(_13w,_13A));})]);});});});},_13r,function(_13B,_13C,_13D){return new F(function(){return _134(_13B,_13C,_13q,function(_13E,_13F,_13G){return new F(function(){return A(_13s,[_13E,_13F,new T(function(){return B(_ER(_13D,_13G));})]);});},function(_13H){return new F(function(){return A(_13t,[new T(function(){return B(_ER(_13D,_13H));})]);});});});},_13t]);});},_13I=function(_13J,_13K,_13L,_13M,_13N){return new F(function(){return _13o(_13J,_13K,_13L,_13M,function(_13O){var _13P=E(_13J),_13Q=E(_13P[2]),_13R=E(_13P[1]);return _13R[0]==0?B(A(_13N,[new T(function(){var _13S=E(_13O),_13T=E(_13S[1]),_13U=B(_E7(_13T[1],_13T[2],_13T[3],_13S[2],_13Q[1],_13Q[2],_13Q[3],_11h));return [0,E(_13U[1]),_13U[2]];})])):B(A(_13K,[_13R[1],[0,_13R[2],E(_13Q),E(_13P[3])],[0,E(_13Q),_9]]));});});},_13V=function(_13W,_13X,_13Y,_13Z,_140){return new F(function(){return _Ep(_13I,_13W,_13X,_13Y,_13Z);});},_141=function(_142,_143,_144){return [0,_142,E(E(_143)),_144];},_145=function(_146,_147,_148){var _149=new T(function(){return B(_JH(_146));}),_14a=new T(function(){return B(_JH(_146));});return new F(function(){return A(_147,[_148,function(_14b,_14c,_14d){return new F(function(){return A(_149,[[0,new T(function(){return B(A(_14a,[new T(function(){return B(_141(_14b,_14c,_14d));})]));})]]);});},function(_14e){return new F(function(){return A(_149,[[0,new T(function(){return B(A(_14a,[[1,_14e]]));})]]);});},function(_14f,_14g,_14h){return new F(function(){return A(_149,[new T(function(){return [1,E(B(A(_14a,[new T(function(){return B(_141(_14f,_14g,_14h));})])))];})]);});},function(_14i){return new F(function(){return A(_149,[new T(function(){return [1,E(B(A(_14a,[[1,_14i]])))];})]);});}]);});},_14j=function(_14k){return function(_14l,_14m,_14n,_14o,_14p){return new F(function(){return A(_14o,[new T(function(){var _14q=B(_145(_131,_14r,[0,new T(function(){var _14s=B(_145(_131,_13V,[0,_14k,E(_12W),E(_6B)]));if(!_14s[0]){var _14t=E(_14s[1]),_14u=_14t[0]==0?E(_14t[1]):B(_132(_14t[1]));}else{var _14v=E(_14s[1]),_14u=_14v[0]==0?E(_14v[1]):B(_132(_14v[1]));}return _14u;}),E(_12W),E(_6B)]));if(!_14q[0]){var _14w=E(_14q[1]),_14x=_14w[0]==0?E(_14w[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_14w[1]));})));})],_9],_9],_12V];}else{var _14y=E(_14q[1]),_14x=_14y[0]==0?E(_14y[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_14y[1]));})));})],_9],_9],_12V];}return _14x;}),_14l,new T(function(){return [0,E(E(_14l)[2]),_9];})]);});};},_14z=function(_14A,_14B,_14C,_14D,_14E){return new F(function(){return _12B(_14A,function(_14F,_14G,_14H){return new F(function(){return A(_14j,[_14F,_14G,_14B,_14C,function(_14I,_14J,_14K){return new F(function(){return A(_14B,[_14I,_14J,new T(function(){return B(_ER(_14H,_14K));})]);});},function(_14L){return new F(function(){return A(_14C,[new T(function(){return B(_ER(_14H,_14L));})]);});}]);});},_14C,function(_14M,_14N,_14O){return new F(function(){return A(_14j,[_14M,_14N,_14B,_14C,function(_14P,_14Q,_14R){return new F(function(){return A(_14D,[_14P,_14Q,new T(function(){return B(_ER(_14O,_14R));})]);});},function(_14S){return new F(function(){return A(_14E,[new T(function(){return B(_ER(_14O,_14S));})]);});}]);});},_14E);});},_14T=function(_14U,_14V,_14W,_14X,_14Y,_14Z){var _150=function(_151,_152,_153,_154,_155){var _156=function(_157,_158,_159,_15a,_15b){return new F(function(){return A(_154,[[0,[1,[0,_14U,_158,_159]],_157],_15a,new T(function(){var _15c=E(_15b),_15d=E(_15c[1]),_15e=E(E(_15a)[2]),_15f=B(_E7(_15d[1],_15d[2],_15d[3],_15c[2],_15e[1],_15e[2],_15e[3],_9));return [0,E(_15f[1]),_15f[2]];})]);});},_15g=function(_15h){return new F(function(){return _156(_9,_X7,_9,_151,new T(function(){var _15i=E(E(_151)[2]),_15j=E(_15h),_15k=E(_15j[1]),_15l=B(_E7(_15k[1],_15k[2],_15k[3],_15j[2],_15i[1],_15i[2],_15i[3],_9));return [0,E(_15l[1]),_15l[2]];}));});};return new F(function(){return _14z(_151,function(_15m,_15n,_15o){var _15p=E(_15m),_15q=E(_15p[2]);return new F(function(){return A(_152,[[0,[1,[0,_14U,_15q[1],_15q[2]]],_15p[1]],_15n,new T(function(){var _15r=E(_15o),_15s=E(_15r[1]),_15t=E(E(_15n)[2]),_15u=B(_E7(_15s[1],_15s[2],_15s[3],_15r[2],_15t[1],_15t[2],_15t[3],_9));return [0,E(_15u[1]),_15u[2]];})]);});},_15g,function(_15v,_15w,_15x){var _15y=E(_15v),_15z=E(_15y[2]);return new F(function(){return _156(_15y[1],_15z[1],_15z[2],_15w,_15x);});},_15g);});};return new F(function(){return A(_Yt,[_14V,function(_15A,_15B,_15C){return new F(function(){return _150(_15B,_14W,_14X,function(_15D,_15E,_15F){return new F(function(){return A(_14W,[_15D,_15E,new T(function(){return B(_ER(_15C,_15F));})]);});},function(_15G){return new F(function(){return A(_14X,[new T(function(){return B(_ER(_15C,_15G));})]);});});});},_14X,function(_15H,_15I,_15J){return new F(function(){return _150(_15I,_14W,_14X,function(_15K,_15L,_15M){return new F(function(){return A(_14Y,[_15K,_15L,new T(function(){return B(_ER(_15J,_15M));})]);});},function(_15N){return new F(function(){return A(_14Z,[new T(function(){return B(_ER(_15J,_15N));})]);});});});},_14Z]);});},_15O=new T(function(){return B(unCStr(" associative operator"));}),_15P=function(_15Q,_15R){var _15S=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_15Q,_15O));}))))];}),_9];return function(_15T,_15U,_15V,_15W,_15X){return new F(function(){return A(_15R,[_15T,function(_15Y,_15Z,_160){return new F(function(){return A(_15X,[new T(function(){var _161=E(E(_15Z)[2]),_162=E(_160),_163=E(_162[1]),_164=B(_E7(_163[1],_163[2],_163[3],_162[2],_161[1],_161[2],_161[3],_15S));return [0,E(_164[1]),_164[2]];})]);});},_15X,function(_165,_166,_167){return new F(function(){return A(_15X,[new T(function(){var _168=E(E(_166)[2]),_169=E(_167),_16a=E(_169[1]),_16b=B(_E7(_16a[1],_16a[2],_16a[3],_169[2],_168[1],_168[2],_168[3],_15S));return [0,E(_16b[1]),_16b[2]];})]);});},_15X]);});};},_16c=function(_16d,_16e,_16f,_16g,_16h,_16i){var _16j=E(_16d);if(!_16j[0]){return new F(function(){return A(_16i,[new T(function(){return [0,E(E(_16e)[2]),_9];})]);});}else{return new F(function(){return A(_16j[1],[_16e,_16f,_16g,_16h,function(_16k){return new F(function(){return _16c(_16j[2],_16e,_16f,_16g,function(_16l,_16m,_16n){return new F(function(){return A(_16h,[_16l,_16m,new T(function(){return B(_ER(_16k,_16n));})]);});},function(_16o){return new F(function(){return A(_16i,[new T(function(){return B(_ER(_16k,_16o));})]);});});});}]);});}},_16p=new T(function(){return B(unCStr("right"));}),_16q=new T(function(){return B(unCStr("left"));}),_16r=new T(function(){return B(unCStr("non"));}),_16s=new T(function(){return B(unCStr("operator"));}),_16t=[1,_16s,_9],_16u=[1,_9,_9],_16v=function(_16w){var _16x=E(_16w);if(!_16x[0]){return [0,_9,_9,_9,_9,_9];}else{var _16y=_16x[2],_16z=E(_16x[1]);switch(_16z[0]){case 0:var _16A=_16z[1],_16B=B(_16v(_16y)),_16C=_16B[1],_16D=_16B[2],_16E=_16B[3],_16F=_16B[4],_16G=_16B[5];switch(E(_16z[2])){case 0:return [0,_16C,_16D,[1,_16A,_16E],_16F,_16G];case 1:return [0,_16C,[1,_16A,_16D],_16E,_16F,_16G];default:return [0,[1,_16A,_16C],_16D,_16E,_16F,_16G];}break;case 1:var _16H=B(_16v(_16y));return [0,_16H[1],_16H[2],_16H[3],[1,_16z[1],_16H[4]],_16H[5]];default:var _16I=B(_16v(_16y));return [0,_16I[1],_16I[2],_16I[3],_16I[4],[1,_16z[1],_16I[5]]];}}},_16J=function(_16K,_16L){while(1){var _16M=(function(_16N,_16O){var _16P=E(_16O);if(!_16P[0]){return E(_16N);}else{var _16Q=new T(function(){var _16R=B(_16v(_16P[1]));return [0,_16R[1],_16R[2],_16R[3],_16R[4],_16R[5]];}),_16S=new T(function(){return E(E(_16Q)[2]);}),_16T=new T(function(){return B(_15P(_16q,function(_16U,_16V,_16W,_16X,_16Y){return new F(function(){return _16c(_16S,_16U,_16V,_16W,_16X,_16Y);});}));}),_16Z=new T(function(){return E(E(_16Q)[1]);}),_170=new T(function(){return E(E(_16Q)[3]);}),_171=new T(function(){return B(_15P(_16r,function(_172,_173,_174,_175,_176){return new F(function(){return _16c(_170,_172,_173,_174,_175,_176);});}));}),_177=function(_178,_179,_17a,_17b,_17c,_17d){var _17e=function(_17f,_17g,_17h,_17i,_17j){var _17k=new T(function(){return B(A(_178,[_17f]));});return new F(function(){return _16c(new T(function(){return E(E(_16Q)[5]);}),_17g,function(_17l,_17m,_17n){return new F(function(){return A(_17h,[new T(function(){return B(A(_17l,[_17k]));}),_17m,new T(function(){var _17o=E(E(_17m)[2]),_17p=E(_17n),_17q=E(_17p[1]),_17r=B(_E7(_17q[1],_17q[2],_17q[3],_17p[2],_17o[1],_17o[2],_17o[3],_9));return [0,E(_17r[1]),_17r[2]];})]);});},_17i,function(_17s,_17t,_17u){return new F(function(){return A(_17j,[new T(function(){return B(A(_17s,[_17k]));}),_17t,new T(function(){var _17v=E(E(_17t)[2]),_17w=_17v[1],_17x=_17v[2],_17y=_17v[3],_17z=E(_17u),_17A=E(_17z[1]),_17B=_17A[2],_17C=_17A[3],_17D=E(_17z[2]);if(!_17D[0]){switch(B(_DZ(_17A[1],_17w))){case 0:var _17E=[0,E(_17v),_9];break;case 1:if(_17B>=_17x){if(_17B!=_17x){var _17F=[0,E(_17A),_9];}else{if(_17C>=_17y){var _17G=_17C!=_17y?[0,E(_17A),_9]:[0,E(_17A),_E6];}else{var _17G=[0,E(_17v),_9];}var _17H=_17G,_17F=_17H;}var _17I=_17F,_17J=_17I;}else{var _17J=[0,E(_17v),_9];}var _17K=_17J,_17E=_17K;break;default:var _17E=[0,E(_17A),_9];}var _17L=_17E;}else{var _17M=B(_K5(_17A,_17D,_16u)),_17N=E(_17M[1]),_17O=B(_E7(_17N[1],_17N[2],_17N[3],_17M[2],_17w,_17x,_17y,_9)),_17L=[0,E(_17O[1]),_17O[2]];}var _17P=_17L,_17Q=_17P,_17R=_17Q,_17S=_17R;return _17S;})]);});},function(_17T){return new F(function(){return A(_17j,[_17k,_17g,new T(function(){var _17U=E(E(_17g)[2]),_17V=_17U[1],_17W=_17U[2],_17X=_17U[3],_17Y=E(_17T),_17Z=B(_K5(_17Y[1],_17Y[2],_16u)),_180=E(_17Z[1]),_181=B(_E7(_180[1],_180[2],_180[3],_17Z[2],_17V,_17W,_17X,_9)),_182=E(_181[1]),_183=B(_E7(_182[1],_182[2],_182[3],_181[2],_17V,_17W,_17X,_9));return [0,E(_183[1]),_183[2]];})]);});});});};return new F(function(){return A(_16N,[_179,function(_184,_185,_186){return new F(function(){return _17e(_184,_185,_17a,_17b,function(_187,_188,_189){return new F(function(){return A(_17a,[_187,_188,new T(function(){return B(_ER(_186,_189));})]);});});});},_17b,function(_18a,_18b,_18c){return new F(function(){return _17e(_18a,_18b,_17a,_17b,function(_18d,_18e,_18f){return new F(function(){return A(_17c,[_18d,_18e,new T(function(){return B(_ER(_18c,_18f));})]);});});});},_17d]);});},_18g=function(_18h,_18i,_18j,_18k,_18l){var _18m=function(_18n,_18o,_18p){return new F(function(){return _177(_18n,_18o,_18i,_18j,function(_18q,_18r,_18s){return new F(function(){return A(_18k,[_18q,_18r,new T(function(){return B(_ER(_18p,_18s));})]);});},function(_18t){return new F(function(){return A(_18l,[new T(function(){return B(_ER(_18p,_18t));})]);});});});};return new F(function(){return _16c(new T(function(){return E(E(_16Q)[4]);}),_18h,function(_18u,_18v,_18w){return new F(function(){return _177(_18u,_18v,_18i,_18j,function(_18x,_18y,_18z){return new F(function(){return A(_18i,[_18x,_18y,new T(function(){return B(_ER(_18w,_18z));})]);});},function(_18A){return new F(function(){return A(_18j,[new T(function(){return B(_ER(_18w,_18A));})]);});});});},_18j,function(_18B,_18C,_18D){return new F(function(){return _18m(_18B,_18C,new T(function(){var _18E=E(_18D),_18F=E(_18E[2]);if(!_18F[0]){var _18G=E(_18E);}else{var _18H=B(_K5(_18E[1],_18F,_16u)),_18G=[0,E(_18H[1]),_18H[2]];}var _18I=_18G;return _18I;}));});},function(_18J){return new F(function(){return _18m(_6P,_18h,new T(function(){var _18K=E(E(_18h)[2]),_18L=E(_18J),_18M=B(_K5(_18L[1],_18L[2],_16u)),_18N=E(_18M[1]),_18O=B(_E7(_18N[1],_18N[2],_18N[3],_18M[2],_18K[1],_18K[2],_18K[3],_9));return [0,E(_18O[1]),_18O[2]];}));});});});},_18P=function(_18Q,_18R,_18S,_18T,_18U,_18V){var _18W=function(_18X){return new F(function(){return A(_16T,[_18R,_18S,_18T,function(_18Y,_18Z,_190){return new F(function(){return A(_18U,[_18Y,_18Z,new T(function(){return B(_ER(_18X,_190));})]);});},function(_191){return new F(function(){return A(_171,[_18R,_18S,_18T,function(_192,_193,_194){return new F(function(){return A(_18U,[_192,_193,new T(function(){var _195=E(_18X),_196=E(_195[1]),_197=E(_191),_198=E(_197[1]),_199=E(_194),_19a=E(_199[1]),_19b=B(_E7(_198[1],_198[2],_198[3],_197[2],_19a[1],_19a[2],_19a[3],_199[2])),_19c=E(_19b[1]),_19d=B(_E7(_196[1],_196[2],_196[3],_195[2],_19c[1],_19c[2],_19c[3],_19b[2]));return [0,E(_19d[1]),_19d[2]];})]);});},function(_19e){return new F(function(){return A(_18V,[new T(function(){var _19f=E(_18X),_19g=E(_19f[1]),_19h=E(_191),_19i=E(_19h[1]),_19j=E(_19e),_19k=E(_19j[1]),_19l=B(_E7(_19i[1],_19i[2],_19i[3],_19h[2],_19k[1],_19k[2],_19k[3],_19j[2])),_19m=E(_19l[1]),_19n=B(_E7(_19g[1],_19g[2],_19g[3],_19f[2],_19m[1],_19m[2],_19m[3],_19l[2]));return [0,E(_19n[1]),_19n[2]];})]);});}]);});}]);});},_19o=function(_19p,_19q,_19r,_19s,_19t,_19u){var _19v=function(_19w,_19x,_19y){return new F(function(){return A(_19r,[new T(function(){return B(A(_19p,[_18Q,_19w]));}),_19x,new T(function(){var _19z=E(E(_19x)[2]),_19A=E(_19y),_19B=E(_19A[1]),_19C=B(_E7(_19B[1],_19B[2],_19B[3],_19A[2],_19z[1],_19z[2],_19z[3],_9));return [0,E(_19C[1]),_19C[2]];})]);});};return new F(function(){return _18g(_19q,function(_19D,_19E,_19F){return new F(function(){return _18P(_19D,_19E,_19v,_19s,function(_19G,_19H,_19I){return new F(function(){return _19v(_19G,_19H,new T(function(){var _19J=E(_19F),_19K=E(_19J[1]),_19L=E(_19I),_19M=E(_19L[1]),_19N=B(_E7(_19K[1],_19K[2],_19K[3],_19J[2],_19M[1],_19M[2],_19M[3],_19L[2]));return [0,E(_19N[1]),_19N[2]];},1));});},function(_19O){return new F(function(){return _19v(_19D,_19E,new T(function(){var _19P=E(E(_19E)[2]),_19Q=E(_19F),_19R=E(_19Q[1]),_19S=E(_19O),_19T=E(_19S[1]),_19U=B(_E7(_19T[1],_19T[2],_19T[3],_19S[2],_19P[1],_19P[2],_19P[3],_9)),_19V=E(_19U[1]),_19W=B(_E7(_19R[1],_19R[2],_19R[3],_19Q[2],_19V[1],_19V[2],_19V[3],_19U[2]));return [0,E(_19W[1]),_19W[2]];},1));});});});},_19s,function(_19X,_19Y,_19Z){var _1a0=function(_1a1,_1a2,_1a3){return new F(function(){return A(_19t,[new T(function(){return B(A(_19p,[_18Q,_1a1]));}),_1a2,new T(function(){var _1a4=E(E(_1a2)[2]),_1a5=E(_19Z),_1a6=E(_1a5[1]),_1a7=E(_1a3),_1a8=E(_1a7[1]),_1a9=B(_E7(_1a6[1],_1a6[2],_1a6[3],_1a5[2],_1a8[1],_1a8[2],_1a8[3],_1a7[2])),_1aa=E(_1a9[1]),_1ab=B(_E7(_1aa[1],_1aa[2],_1aa[3],_1a9[2],_1a4[1],_1a4[2],_1a4[3],_9));return [0,E(_1ab[1]),_1ab[2]];})]);});};return new F(function(){return _18P(_19X,_19Y,_19v,_19s,_1a0,function(_1ac){return new F(function(){return _1a0(_19X,_19Y,new T(function(){var _1ad=E(E(_19Y)[2]),_1ae=E(_1ac),_1af=E(_1ae[1]),_1ag=B(_E7(_1af[1],_1af[2],_1af[3],_1ae[2],_1ad[1],_1ad[2],_1ad[3],_9));return [0,E(_1ag[1]),_1ag[2]];},1));});});});},_19u);});};return new F(function(){return _16c(_16Z,_18R,function(_1ah,_1ai,_1aj){return new F(function(){return _19o(_1ah,_1ai,_18S,_18T,function(_1ak,_1al,_1am){return new F(function(){return A(_18S,[_1ak,_1al,new T(function(){return B(_ER(_1aj,_1am));})]);});},function(_1an){return new F(function(){return A(_18T,[new T(function(){return B(_ER(_1aj,_1an));})]);});});});},_18T,function(_1ao,_1ap,_1aq){return new F(function(){return _19o(_1ao,_1ap,_18S,_18T,function(_1ar,_1as,_1at){return new F(function(){return A(_18U,[_1ar,_1as,new T(function(){return B(_ER(_1aq,_1at));})]);});},function(_1au){return new F(function(){return _18W(new T(function(){return B(_ER(_1aq,_1au));}));});});});},_18W);});},_1av=new T(function(){return B(_15P(_16p,function(_1aw,_1ax,_1ay,_1az,_1aA){return new F(function(){return _16c(_16Z,_1aw,_1ax,_1ay,_1az,_1aA);});}));}),_1aB=function(_1aC,_1aD,_1aE,_1aF,_1aG,_1aH){var _1aI=function(_1aJ){return new F(function(){return A(_1av,[_1aD,_1aE,_1aF,function(_1aK,_1aL,_1aM){return new F(function(){return A(_1aG,[_1aK,_1aL,new T(function(){return B(_ER(_1aJ,_1aM));})]);});},function(_1aN){return new F(function(){return A(_171,[_1aD,_1aE,_1aF,function(_1aO,_1aP,_1aQ){return new F(function(){return A(_1aG,[_1aO,_1aP,new T(function(){var _1aR=E(_1aJ),_1aS=E(_1aR[1]),_1aT=E(_1aN),_1aU=E(_1aT[1]),_1aV=E(_1aQ),_1aW=E(_1aV[1]),_1aX=B(_E7(_1aU[1],_1aU[2],_1aU[3],_1aT[2],_1aW[1],_1aW[2],_1aW[3],_1aV[2])),_1aY=E(_1aX[1]),_1aZ=B(_E7(_1aS[1],_1aS[2],_1aS[3],_1aR[2],_1aY[1],_1aY[2],_1aY[3],_1aX[2]));return [0,E(_1aZ[1]),_1aZ[2]];})]);});},function(_1b0){return new F(function(){return A(_1aH,[new T(function(){var _1b1=E(_1aJ),_1b2=E(_1b1[1]),_1b3=E(_1aN),_1b4=E(_1b3[1]),_1b5=E(_1b0),_1b6=E(_1b5[1]),_1b7=B(_E7(_1b4[1],_1b4[2],_1b4[3],_1b3[2],_1b6[1],_1b6[2],_1b6[3],_1b5[2])),_1b8=E(_1b7[1]),_1b9=B(_E7(_1b2[1],_1b2[2],_1b2[3],_1b1[2],_1b8[1],_1b8[2],_1b8[3],_1b7[2]));return [0,E(_1b9[1]),_1b9[2]];})]);});}]);});}]);});},_1ba=function(_1bb,_1bc,_1bd,_1be,_1bf,_1bg){var _1bh=function(_1bi){var _1bj=new T(function(){return B(A(_1bb,[_1aC,_1bi]));});return function(_1bk,_1bl,_1bm,_1bn,_1bo){return new F(function(){return _1aB(_1bj,_1bk,_1bl,_1bm,_1bn,function(_1bp){return new F(function(){return A(_1bn,[_1bj,_1bk,new T(function(){var _1bq=E(E(_1bk)[2]),_1br=E(_1bp),_1bs=E(_1br[1]),_1bt=B(_E7(_1bs[1],_1bs[2],_1bs[3],_1br[2],_1bq[1],_1bq[2],_1bq[3],_9));return [0,E(_1bt[1]),_1bt[2]];})]);});});});};};return new F(function(){return _18g(_1bc,function(_1bu,_1bv,_1bw){return new F(function(){return A(_1bh,[_1bu,_1bv,_1bd,_1be,function(_1bx,_1by,_1bz){return new F(function(){return A(_1bd,[_1bx,_1by,new T(function(){return B(_ER(_1bw,_1bz));})]);});},function(_1bA){return new F(function(){return A(_1be,[new T(function(){return B(_ER(_1bw,_1bA));})]);});}]);});},_1be,function(_1bB,_1bC,_1bD){return new F(function(){return A(_1bh,[_1bB,_1bC,_1bd,_1be,function(_1bE,_1bF,_1bG){return new F(function(){return A(_1bf,[_1bE,_1bF,new T(function(){return B(_ER(_1bD,_1bG));})]);});},function(_1bH){return new F(function(){return A(_1bg,[new T(function(){return B(_ER(_1bD,_1bH));})]);});}]);});},_1bg);});};return new F(function(){return _16c(_16S,_1aD,function(_1bI,_1bJ,_1bK){return new F(function(){return _1ba(_1bI,_1bJ,_1aE,_1aF,function(_1bL,_1bM,_1bN){return new F(function(){return A(_1aE,[_1bL,_1bM,new T(function(){return B(_ER(_1bK,_1bN));})]);});},function(_1bO){return new F(function(){return A(_1aF,[new T(function(){return B(_ER(_1bK,_1bO));})]);});});});},_1aF,function(_1bP,_1bQ,_1bR){return new F(function(){return _1ba(_1bP,_1bQ,_1aE,_1aF,function(_1bS,_1bT,_1bU){return new F(function(){return A(_1aG,[_1bS,_1bT,new T(function(){return B(_ER(_1bR,_1bU));})]);});},function(_1bV){return new F(function(){return _1aI(new T(function(){return B(_ER(_1bR,_1bV));}));});});});},_1aI);});},_1bW=function(_1bX,_1bY,_1bZ,_1c0,_1c1,_1c2){var _1c3=function(_1c4,_1c5,_1c6,_1c7,_1c8,_1c9){var _1ca=function(_1cb){return function(_1cc,_1cd,_1ce,_1cf,_1cg){return new F(function(){return A(_1av,[_1cc,_1cd,_1ce,_1cf,function(_1ch){return new F(function(){return A(_16T,[_1cc,_1cd,_1ce,function(_1ci,_1cj,_1ck){return new F(function(){return A(_1cf,[_1ci,_1cj,new T(function(){return B(_ER(_1ch,_1ck));})]);});},function(_1cl){return new F(function(){return A(_171,[_1cc,_1cd,_1ce,function(_1cm,_1cn,_1co){return new F(function(){return A(_1cf,[_1cm,_1cn,new T(function(){var _1cp=E(_1ch),_1cq=E(_1cp[1]),_1cr=E(_1cl),_1cs=E(_1cr[1]),_1ct=E(_1co),_1cu=E(_1ct[1]),_1cv=B(_E7(_1cs[1],_1cs[2],_1cs[3],_1cr[2],_1cu[1],_1cu[2],_1cu[3],_1ct[2])),_1cw=E(_1cv[1]),_1cx=B(_E7(_1cq[1],_1cq[2],_1cq[3],_1cp[2],_1cw[1],_1cw[2],_1cw[3],_1cv[2]));return [0,E(_1cx[1]),_1cx[2]];})]);});},function(_1cy){return new F(function(){return A(_1cf,[new T(function(){return B(A(_1c4,[_1bX,_1cb]));}),_1cc,new T(function(){var _1cz=E(E(_1cc)[2]),_1cA=E(_1ch),_1cB=E(_1cA[1]),_1cC=E(_1cl),_1cD=E(_1cC[1]),_1cE=E(_1cy),_1cF=E(_1cE[1]),_1cG=B(_E7(_1cF[1],_1cF[2],_1cF[3],_1cE[2],_1cz[1],_1cz[2],_1cz[3],_9)),_1cH=E(_1cG[1]),_1cI=B(_E7(_1cD[1],_1cD[2],_1cD[3],_1cC[2],_1cH[1],_1cH[2],_1cH[3],_1cG[2])),_1cJ=E(_1cI[1]),_1cK=B(_E7(_1cB[1],_1cB[2],_1cB[3],_1cA[2],_1cJ[1],_1cJ[2],_1cJ[3],_1cI[2]));return [0,E(_1cK[1]),_1cK[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _18g(_1c5,function(_1cL,_1cM,_1cN){return new F(function(){return A(_1ca,[_1cL,_1cM,_1c6,_1c7,function(_1cO,_1cP,_1cQ){return new F(function(){return A(_1c6,[_1cO,_1cP,new T(function(){return B(_ER(_1cN,_1cQ));})]);});},function(_1cR){return new F(function(){return A(_1c7,[new T(function(){return B(_ER(_1cN,_1cR));})]);});}]);});},_1c7,function(_1cS,_1cT,_1cU){return new F(function(){return A(_1ca,[_1cS,_1cT,_1c6,_1c7,function(_1cV,_1cW,_1cX){return new F(function(){return A(_1c8,[_1cV,_1cW,new T(function(){return B(_ER(_1cU,_1cX));})]);});},function(_1cY){return new F(function(){return A(_1c9,[new T(function(){return B(_ER(_1cU,_1cY));})]);});}]);});},_1c9);});};return new F(function(){return _Kq(function(_1cZ,_1d0,_1d1,_1d2,_1d3){return new F(function(){return _18P(_1bX,_1cZ,_1d0,_1d1,_1d2,function(_1d4){return new F(function(){return _1aB(_1bX,_1cZ,_1d0,_1d1,function(_1d5,_1d6,_1d7){return new F(function(){return A(_1d2,[_1d5,_1d6,new T(function(){return B(_ER(_1d4,_1d7));})]);});},function(_1d8){var _1d9=function(_1da){return new F(function(){return A(_1d2,[_1bX,_1cZ,new T(function(){var _1db=E(E(_1cZ)[2]),_1dc=E(_1d4),_1dd=E(_1dc[1]),_1de=E(_1d8),_1df=E(_1de[1]),_1dg=E(_1da),_1dh=E(_1dg[1]),_1di=B(_E7(_1dh[1],_1dh[2],_1dh[3],_1dg[2],_1db[1],_1db[2],_1db[3],_9)),_1dj=E(_1di[1]),_1dk=B(_E7(_1df[1],_1df[2],_1df[3],_1de[2],_1dj[1],_1dj[2],_1dj[3],_1di[2])),_1dl=E(_1dk[1]),_1dm=B(_E7(_1dd[1],_1dd[2],_1dd[3],_1dc[2],_1dl[1],_1dl[2],_1dl[3],_1dk[2]));return [0,E(_1dm[1]),_1dm[2]];})]);});};return new F(function(){return _16c(_170,_1cZ,function(_1dn,_1do,_1dp){return new F(function(){return _1c3(_1dn,_1do,_1d0,_1d1,function(_1dq,_1dr,_1ds){return new F(function(){return A(_1d0,[_1dq,_1dr,new T(function(){return B(_ER(_1dp,_1ds));})]);});},function(_1dt){return new F(function(){return A(_1d1,[new T(function(){return B(_ER(_1dp,_1dt));})]);});});});},_1d1,function(_1du,_1dv,_1dw){return new F(function(){return _1c3(_1du,_1dv,_1d0,_1d1,function(_1dx,_1dy,_1dz){return new F(function(){return A(_1d2,[_1dx,_1dy,new T(function(){var _1dA=E(_1d4),_1dB=E(_1dA[1]),_1dC=E(_1d8),_1dD=E(_1dC[1]),_1dE=E(_1dw),_1dF=E(_1dE[1]),_1dG=E(_1dz),_1dH=E(_1dG[1]),_1dI=B(_E7(_1dF[1],_1dF[2],_1dF[3],_1dE[2],_1dH[1],_1dH[2],_1dH[3],_1dG[2])),_1dJ=E(_1dI[1]),_1dK=B(_E7(_1dD[1],_1dD[2],_1dD[3],_1dC[2],_1dJ[1],_1dJ[2],_1dJ[3],_1dI[2])),_1dL=E(_1dK[1]),_1dM=B(_E7(_1dB[1],_1dB[2],_1dB[3],_1dA[2],_1dL[1],_1dL[2],_1dL[3],_1dK[2]));return [0,E(_1dM[1]),_1dM[2]];})]);});},function(_1dN){return new F(function(){return _1d9(new T(function(){var _1dO=E(_1dw),_1dP=E(_1dO[1]),_1dQ=E(_1dN),_1dR=E(_1dQ[1]),_1dS=B(_E7(_1dP[1],_1dP[2],_1dP[3],_1dO[2],_1dR[1],_1dR[2],_1dR[3],_1dQ[2]));return [0,E(_1dS[1]),_1dS[2]];},1));});});});},_1d9);});});});});});},_16t,_1bY,_1bZ,_1c0,_1c1,_1c2);});};_16K=function(_1dT,_1dU,_1dV,_1dW,_1dX){return new F(function(){return _18g(_1dT,function(_1dY,_1dZ,_1e0){return new F(function(){return _1bW(_1dY,_1dZ,_1dU,_1dV,function(_1e1,_1e2,_1e3){return new F(function(){return A(_1dU,[_1e1,_1e2,new T(function(){return B(_ER(_1e0,_1e3));})]);});},function(_1e4){return new F(function(){return A(_1dV,[new T(function(){return B(_ER(_1e0,_1e4));})]);});});});},_1dV,function(_1e5,_1e6,_1e7){return new F(function(){return _1bW(_1e5,_1e6,_1dU,_1dV,function(_1e8,_1e9,_1ea){return new F(function(){return A(_1dW,[_1e8,_1e9,new T(function(){return B(_ER(_1e7,_1ea));})]);});},function(_1eb){return new F(function(){return A(_1dX,[new T(function(){return B(_ER(_1e7,_1eb));})]);});});});},_1dX);});};_16L=_16P[2];return null;}})(_16K,_16L);if(_16M!=null){return _16M;}}},_1ec=0,_1ed=[3,_],_1ee=function(_1ef,_1eg){return [5,_1ed,_1ef,_1eg];},_1eh=new T(function(){return B(unCStr("=>"));}),_1ei=function(_1ej){return E(E(_1ej)[1]);},_1ek=function(_1el,_1em,_1en,_1eo){while(1){var _1ep=E(_1eo);if(!_1ep[0]){return [0,_1el,_1em,_1en];}else{var _1eq=_1ep[2];switch(E(E(_1ep[1])[1])){case 9:var _1er=(_1en+8|0)-B(_Hk(_1en-1|0,8))|0;_1eo=_1eq;_1en=_1er;continue;case 10:var _1es=_1em+1|0;_1en=1;_1eo=_1eq;_1em=_1es;continue;default:var _1er=_1en+1|0;_1eo=_1eq;_1en=_1er;continue;}}}},_1et=function(_1eu){return E(E(_1eu)[1]);},_1ev=function(_1ew){return E(E(_1ew)[2]);},_1ex=function(_1ey){return [0,E(E(_1ey)[2]),_9];},_1ez=function(_1eA,_1eB,_1eC,_1eD,_1eE,_1eF,_1eG){var _1eH=E(_1eB);if(!_1eH[0]){return new F(function(){return A(_1eF,[_9,_1eC,new T(function(){return B(_1ex(_1eC));})]);});}else{var _1eI=E(_1eC),_1eJ=E(_1eI[2]),_1eK=new T(function(){return B(_1ei(_1eA));}),_1eL=[0,E(_1eJ),[1,[2,E([1,_Hg,new T(function(){return B(_IX(_1eH,_Hh));})])],_Hj]],_1eM=[2,E([1,_Hg,new T(function(){return B(_IX(_1eH,_Hh));})])],_1eN=new T(function(){var _1eO=B(_1ek(_1eJ[1],_1eJ[2],_1eJ[3],_1eH));return [0,_1eO[1],_1eO[2],_1eO[3]];}),_1eP=function(_1eQ,_1eR){var _1eS=E(_1eQ);if(!_1eS[0]){return new F(function(){return A(_1eD,[_1eH,new T(function(){return [0,_1eR,E(E(_1eN)),E(_1eI[3])];}),new T(function(){return [0,E(E(_1eN)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_1et(_1eK));}),[new T(function(){return B(A(new T(function(){return B(_1ev(_1eA));}),[_1eR]));}),function(_1eT){var _1eU=E(_1eT);if(!_1eU[0]){return E(new T(function(){return B(A(_1eE,[_1eL]));}));}else{var _1eV=E(_1eU[1]),_1eW=E(_1eV[1]);return E(_1eS[1])[1]!=_1eW[1]?B(A(_1eE,[[0,E(_1eJ),[1,_1eM,[1,[0,E([1,_Hg,new T(function(){return B(_IX([1,_1eW,_9],_Hh));})])],_9]]]])):B(_1eP(_1eS[2],_1eV[2]));}}]);});}};return new F(function(){return A(_1et,[_1eK,new T(function(){return B(A(_1ev,[_1eA,_1eI[1]]));}),function(_1eX){var _1eY=E(_1eX);if(!_1eY[0]){return E(new T(function(){return B(A(_1eG,[_1eL]));}));}else{var _1eZ=E(_1eY[1]),_1f0=E(_1eZ[1]);return E(_1eH[1])[1]!=_1f0[1]?B(A(_1eG,[[0,E(_1eJ),[1,_1eM,[1,[0,E([1,_Hg,new T(function(){return B(_IX([1,_1f0,_9],_Hh));})])],_9]]]])):B(_1eP(_1eH[2],_1eZ[2]));}}]);});}},_1f1=function(_1f2,_1f3,_1f4,_1f5,_1f6){return new F(function(){return _1ez(_La,_1eh,_1f2,function(_1f7,_1f8,_1f9){return new F(function(){return A(_1f3,[_1ee,_1f8,new T(function(){var _1fa=E(E(_1f8)[2]),_1fb=E(_1f9),_1fc=E(_1fb[1]),_1fd=B(_E7(_1fc[1],_1fc[2],_1fc[3],_1fb[2],_1fa[1],_1fa[2],_1fa[3],_9));return [0,E(_1fd[1]),_1fd[2]];})]);});},_1f4,function(_1fe,_1ff,_1fg){return new F(function(){return A(_1f5,[_1ee,_1ff,new T(function(){var _1fh=E(E(_1ff)[2]),_1fi=E(_1fg),_1fj=E(_1fi[1]),_1fk=B(_E7(_1fj[1],_1fj[2],_1fj[3],_1fi[2],_1fh[1],_1fh[2],_1fh[3],_9));return [0,E(_1fk[1]),_1fk[2]];})]);});},_1f6);});},_1fl=[0,_1f1,_1ec],_1fm=[1,_1fl,_9],_1fn=[1,_1fm,_9],_1fo=1,_1fp=[2,_],_1fq=function(_1ef,_1eg){return [5,_1fp,_1ef,_1eg];},_1fr=new T(function(){return B(unCStr("\\/"));}),_1fs=function(_1ft,_1fu,_1fv,_1fw,_1fx){return new F(function(){return _1ez(_La,_1fr,_1ft,function(_1fy,_1fz,_1fA){return new F(function(){return A(_1fu,[_1fq,_1fz,new T(function(){var _1fB=E(E(_1fz)[2]),_1fC=E(_1fA),_1fD=E(_1fC[1]),_1fE=B(_E7(_1fD[1],_1fD[2],_1fD[3],_1fC[2],_1fB[1],_1fB[2],_1fB[3],_9));return [0,E(_1fE[1]),_1fE[2]];})]);});},_1fv,function(_1fF,_1fG,_1fH){return new F(function(){return A(_1fw,[_1fq,_1fG,new T(function(){var _1fI=E(E(_1fG)[2]),_1fJ=E(_1fH),_1fK=E(_1fJ[1]),_1fL=B(_E7(_1fK[1],_1fK[2],_1fK[3],_1fJ[2],_1fI[1],_1fI[2],_1fI[3],_9));return [0,E(_1fL[1]),_1fL[2]];})]);});},_1fx);});},_1fM=[0,_1fs,_1fo],_1fN=[1,_],_1fO=function(_1ef,_1eg){return [5,_1fN,_1ef,_1eg];},_1fP=new T(function(){return B(unCStr("/\\"));}),_1fQ=function(_1fR,_1fS,_1fT,_1fU,_1fV){return new F(function(){return _1ez(_La,_1fP,_1fR,function(_1fW,_1fX,_1fY){return new F(function(){return A(_1fS,[_1fO,_1fX,new T(function(){var _1fZ=E(E(_1fX)[2]),_1g0=E(_1fY),_1g1=E(_1g0[1]),_1g2=B(_E7(_1g1[1],_1g1[2],_1g1[3],_1g0[2],_1fZ[1],_1fZ[2],_1fZ[3],_9));return [0,E(_1g2[1]),_1g2[2]];})]);});},_1fT,function(_1g3,_1g4,_1g5){return new F(function(){return A(_1fU,[_1fO,_1g4,new T(function(){var _1g6=E(E(_1g4)[2]),_1g7=E(_1g5),_1g8=E(_1g7[1]),_1g9=B(_E7(_1g8[1],_1g8[2],_1g8[3],_1g7[2],_1g6[1],_1g6[2],_1g6[3],_9));return [0,E(_1g9[1]),_1g9[2]];})]);});},_1fV);});},_1ga=[0,_1fQ,_1fo],_1gb=[1,_1ga,_9],_1gc=[1,_1fM,_1gb],_1gd=[1,_1gc,_1fn],_1ge=[0,_],_1gf=function(_1eg){return [4,_1ge,_1eg];},_1gg=[0,45],_1gh=[1,_1gg,_9],_1gi=function(_1gj,_1gk,_1gl,_1gm,_1gn){return new F(function(){return _1ez(_La,_1gh,_1gj,function(_1go,_1gp,_1gq){return new F(function(){return A(_1gk,[_1gf,_1gp,new T(function(){var _1gr=E(E(_1gp)[2]),_1gs=E(_1gq),_1gt=E(_1gs[1]),_1gu=B(_E7(_1gt[1],_1gt[2],_1gt[3],_1gs[2],_1gr[1],_1gr[2],_1gr[3],_9));return [0,E(_1gu[1]),_1gu[2]];})]);});},_1gl,function(_1gv,_1gw,_1gx){return new F(function(){return A(_1gm,[_1gf,_1gw,new T(function(){var _1gy=E(E(_1gw)[2]),_1gz=E(_1gx),_1gA=E(_1gz[1]),_1gB=B(_E7(_1gA[1],_1gA[2],_1gA[3],_1gz[2],_1gy[1],_1gy[2],_1gy[3],_9));return [0,E(_1gB[1]),_1gB[2]];})]);});},_1gn);});},_1gC=[1,_1gi],_1gD=[1,_1gC,_9],_1gE=[1,_1gD,_1gd],_1gF=new T(function(){return B(unCStr("number"));}),_1gG=[1,_1gF,_9],_1gH=new T(function(){return B(err(_Lw));}),_1gI=new T(function(){return B(err(_Lu));}),_1gJ=new T(function(){return B(_V7(_Vt,_UU,_Vz));}),_1gK=function(_1gL){return function(_1gM,_1gN,_1gO,_1gP,_1gQ){return new F(function(){return A(_1gP,[new T(function(){var _1gR=B(_VE(B(_Lz(_1gJ,_1gL))));return _1gR[0]==0?E(_1gI):E(_1gR[2])[0]==0?E(_1gR[1]):E(_1gH);}),_1gM,new T(function(){return [0,E(E(_1gM)[2]),_9];})]);});};},_1gS=function(_1gT,_1gU,_1gV,_1gW,_1gX){return new F(function(){return _EZ(_KW,_1gT,function(_1gY,_1gZ,_1h0){return new F(function(){return A(_1gK,[_1gY,_1gZ,_1gU,_1gV,function(_1h1,_1h2,_1h3){return new F(function(){return A(_1gU,[_1h1,_1h2,new T(function(){return B(_ER(_1h0,_1h3));})]);});},function(_1h4){return new F(function(){return A(_1gV,[new T(function(){return B(_ER(_1h0,_1h4));})]);});}]);});},_1gV,function(_1h5,_1h6,_1h7){return new F(function(){return A(_1gK,[_1h5,_1h6,_1gU,_1gV,function(_1h8,_1h9,_1ha){return new F(function(){return A(_1gW,[_1h8,_1h9,new T(function(){return B(_ER(_1h7,_1ha));})]);});},function(_1hb){return new F(function(){return A(_1gX,[new T(function(){return B(_ER(_1h7,_1hb));})]);});}]);});},_1gX);});},_1hc=function(_1hd,_1he,_1hf,_1hg,_1hh){return new F(function(){return _1gS(_1hd,function(_1hi,_1hj,_1hk){return new F(function(){return A(_1he,[[1,[0,_,_1hi]],_1hj,new T(function(){var _1hl=E(E(_1hj)[2]),_1hm=E(_1hk),_1hn=E(_1hm[1]),_1ho=B(_E7(_1hn[1],_1hn[2],_1hn[3],_1hm[2],_1hl[1],_1hl[2],_1hl[3],_9));return [0,E(_1ho[1]),_1ho[2]];})]);});},_1hf,function(_1hp,_1hq,_1hr){return new F(function(){return A(_1hg,[[1,[0,_,_1hp]],_1hq,new T(function(){var _1hs=E(E(_1hq)[2]),_1ht=_1hs[1],_1hu=_1hs[2],_1hv=_1hs[3],_1hw=E(_1hr),_1hx=E(_1hw[1]),_1hy=_1hx[2],_1hz=_1hx[3],_1hA=E(_1hw[2]);if(!_1hA[0]){switch(B(_DZ(_1hx[1],_1ht))){case 0:var _1hB=[0,E(_1hs),_9];break;case 1:if(_1hy>=_1hu){if(_1hy!=_1hu){var _1hC=[0,E(_1hx),_9];}else{if(_1hz>=_1hv){var _1hD=_1hz!=_1hv?[0,E(_1hx),_9]:[0,E(_1hx),_E6];}else{var _1hD=[0,E(_1hs),_9];}var _1hE=_1hD,_1hC=_1hE;}var _1hF=_1hC,_1hG=_1hF;}else{var _1hG=[0,E(_1hs),_9];}var _1hH=_1hG,_1hB=_1hH;break;default:var _1hB=[0,E(_1hx),_9];}var _1hI=_1hB;}else{var _1hJ=B(_K5(_1hx,_1hA,_1gG)),_1hK=E(_1hJ[1]),_1hL=B(_E7(_1hK[1],_1hK[2],_1hK[3],_1hJ[2],_1ht,_1hu,_1hv,_9)),_1hI=[0,E(_1hL[1]),_1hL[2]];}var _1hM=_1hI,_1hN=_1hM,_1hO=_1hN,_1hP=_1hO;return _1hP;})]);});},function(_1hQ){return new F(function(){return A(_1hh,[new T(function(){var _1hR=E(_1hQ),_1hS=B(_K5(_1hR[1],_1hR[2],_1gG));return [0,E(_1hS[1]),_1hS[2]];})]);});});});},_1hT=new T(function(){return B(unCStr("P_"));}),_1hU=function(_1hV,_1hW,_1hX,_1hY,_1hZ){return new F(function(){return _1ez(_La,_1hT,_1hV,function(_1i0,_1i1,_1i2){return new F(function(){return _1hc(_1i1,_1hW,_1hX,function(_1i3,_1i4,_1i5){return new F(function(){return A(_1hW,[_1i3,_1i4,new T(function(){return B(_ER(_1i2,_1i5));})]);});},function(_1i6){return new F(function(){return A(_1hX,[new T(function(){return B(_ER(_1i2,_1i6));})]);});});});},_1hX,function(_1i7,_1i8,_1i9){return new F(function(){return _1hc(_1i8,_1hW,_1hX,function(_1ia,_1ib,_1ic){return new F(function(){return A(_1hY,[_1ia,_1ib,new T(function(){return B(_ER(_1i9,_1ic));})]);});},function(_1id){return new F(function(){return A(_1hZ,[new T(function(){return B(_ER(_1i9,_1id));})]);});});});},_1hZ);});},_1ie=[0,41],_1if=new T(function(){return B(_Lb(_La,_1ie));}),_1ig=function(_1ih,_1ii,_1ij,_1ik,_1il,_1im){return new F(function(){return A(_1if,[_1ii,function(_1in,_1io,_1ip){return new F(function(){return A(_1ij,[_1ih,_1io,new T(function(){var _1iq=E(E(_1io)[2]),_1ir=E(_1ip),_1is=E(_1ir[1]),_1it=B(_E7(_1is[1],_1is[2],_1is[3],_1ir[2],_1iq[1],_1iq[2],_1iq[3],_9));return [0,E(_1it[1]),_1it[2]];})]);});},_1ik,function(_1iu,_1iv,_1iw){return new F(function(){return A(_1il,[_1ih,_1iv,new T(function(){var _1ix=E(E(_1iv)[2]),_1iy=E(_1iw),_1iz=E(_1iy[1]),_1iA=B(_E7(_1iz[1],_1iz[2],_1iz[3],_1iy[2],_1ix[1],_1ix[2],_1ix[3],_9));return [0,E(_1iA[1]),_1iA[2]];})]);});},_1im]);});},_1iB=function(_1iC,_1iD,_1iE,_1iF,_1iG){return new F(function(){return A(_1iH,[_1iC,function(_1iI,_1iJ,_1iK){return new F(function(){return _1ig(_1iI,_1iJ,_1iD,_1iE,function(_1iL,_1iM,_1iN){return new F(function(){return A(_1iD,[_1iL,_1iM,new T(function(){return B(_ER(_1iK,_1iN));})]);});},function(_1iO){return new F(function(){return A(_1iE,[new T(function(){return B(_ER(_1iK,_1iO));})]);});});});},_1iE,function(_1iP,_1iQ,_1iR){return new F(function(){return _1ig(_1iP,_1iQ,_1iD,_1iE,function(_1iS,_1iT,_1iU){return new F(function(){return A(_1iF,[_1iS,_1iT,new T(function(){return B(_ER(_1iR,_1iU));})]);});},function(_1iV){return new F(function(){return A(_1iG,[new T(function(){return B(_ER(_1iR,_1iV));})]);});});});},_1iG]);});},_1iW=[0,40],_1iX=new T(function(){return B(_Lb(_La,_1iW));}),_1iY=function(_1iZ,_1j0,_1j1,_1j2,_1j3){var _1j4=function(_1j5){return new F(function(){return _1hU(_1iZ,_1j0,_1j1,function(_1j6,_1j7,_1j8){return new F(function(){return A(_1j2,[_1j6,_1j7,new T(function(){return B(_ER(_1j5,_1j8));})]);});},function(_1j9){return new F(function(){return A(_1j3,[new T(function(){return B(_ER(_1j5,_1j9));})]);});});});};return new F(function(){return A(_1iX,[_1iZ,function(_1ja,_1jb,_1jc){return new F(function(){return _1iB(_1jb,_1j0,_1j1,function(_1jd,_1je,_1jf){return new F(function(){return A(_1j0,[_1jd,_1je,new T(function(){return B(_ER(_1jc,_1jf));})]);});},function(_1jg){return new F(function(){return A(_1j1,[new T(function(){return B(_ER(_1jc,_1jg));})]);});});});},_1j1,function(_1jh,_1ji,_1jj){return new F(function(){return _1iB(_1ji,_1j0,_1j1,function(_1jk,_1jl,_1jm){return new F(function(){return A(_1j2,[_1jk,_1jl,new T(function(){return B(_ER(_1jj,_1jm));})]);});},function(_1jn){return new F(function(){return _1j4(new T(function(){return B(_ER(_1jj,_1jn));}));});});});},_1j4]);});},_1iH=new T(function(){return B(_16J(_1iY,_1gE));}),_1jo=function(_1jp,_1jq,_1jr,_1js,_1jt){return new F(function(){return A(_1iH,[_1jp,function(_1ju,_1jv,_1jw){return new F(function(){return _14T(_1ju,_1jv,_1jq,_1jr,function(_1jx,_1jy,_1jz){return new F(function(){return A(_1jq,[_1jx,_1jy,new T(function(){return B(_ER(_1jw,_1jz));})]);});},function(_1jA){return new F(function(){return A(_1jr,[new T(function(){return B(_ER(_1jw,_1jA));})]);});});});},_1jr,function(_1jB,_1jC,_1jD){return new F(function(){return _14T(_1jB,_1jC,_1jq,_1jr,function(_1jE,_1jF,_1jG){return new F(function(){return A(_1js,[_1jE,_1jF,new T(function(){return B(_ER(_1jD,_1jG));})]);});},function(_1jH){return new F(function(){return A(_1jt,[new T(function(){return B(_ER(_1jD,_1jH));})]);});});});},_1jt]);});},_1jI=function(_1jJ,_1jK,_1jL,_1jM,_1jN){return new F(function(){return _FC(_JP,_1jJ,function(_1jO,_1jP,_1jQ){return new F(function(){return _1jo(_1jP,_1jK,_1jL,function(_1jR,_1jS,_1jT){return new F(function(){return A(_1jK,[_1jR,_1jS,new T(function(){return B(_ER(_1jQ,_1jT));})]);});},function(_1jU){return new F(function(){return A(_1jL,[new T(function(){return B(_ER(_1jQ,_1jU));})]);});});});},_1jL,function(_1jV,_1jW,_1jX){return new F(function(){return _1jo(_1jW,_1jK,_1jL,function(_1jY,_1jZ,_1k0){return new F(function(){return A(_1jM,[_1jY,_1jZ,new T(function(){return B(_ER(_1jX,_1k0));})]);});},function(_1k1){return new F(function(){return A(_1jN,[new T(function(){return B(_ER(_1jX,_1k1));})]);});});});});});},_1k2=function(_1k3,_1k4,_1k5,_1k6,_1k7,_1k8,_1k9,_1ka){var _1kb=E(_1k3);if(!_1kb[0]){return new F(function(){return A(_1ka,[[0,E([0,_1k4,_1k5,_1k6]),_Hj]]);});}else{var _1kc=_1kb[1];if(!B(_9r(_Jv,_1kc,_XD))){return new F(function(){return A(_1ka,[[0,E([0,_1k4,_1k5,_1k6]),[1,[0,E([1,_Hg,new T(function(){return B(_IX([1,_1kc,_9],_Hh));})])],_9]]]);});}else{var _1kd=function(_1ke,_1kf,_1kg,_1kh){var _1ki=[0,E([0,_1ke,_1kf,_1kg]),_9],_1kj=[0,E([0,_1ke,_1kf,_1kg]),_E6];return new F(function(){return _FC(_Yb,[0,_1kb[2],E(_1kh),E(_1k7)],function(_1kk,_1kl,_1km){return new F(function(){return _1jI(_1kl,_1k8,_1k9,function(_1kn,_1ko,_1kp){return new F(function(){return A(_1k8,[_1kn,_1ko,new T(function(){return B(_ER(_1km,_1kp));})]);});},function(_1kq){return new F(function(){return A(_1k9,[new T(function(){return B(_ER(_1km,_1kq));})]);});});});},_1k9,function(_1kr,_1ks,_1kt){return new F(function(){return _1jI(_1ks,_1k8,_1k9,function(_1ku,_1kv,_1kw){return new F(function(){return A(_1k8,[_1ku,_1kv,new T(function(){var _1kx=E(_1kt),_1ky=E(_1kx[1]),_1kz=E(_1kw),_1kA=E(_1kz[1]),_1kB=B(_E7(_1ky[1],_1ky[2],_1ky[3],_1kx[2],_1kA[1],_1kA[2],_1kA[3],_1kz[2])),_1kC=E(_1kB[1]),_1kD=_1kC[2],_1kE=_1kC[3],_1kF=E(_1kB[2]);if(!_1kF[0]){switch(B(_DZ(_1ke,_1kC[1]))){case 0:var _1kG=[0,E(_1kC),_9];break;case 1:if(_1kf>=_1kD){if(_1kf!=_1kD){var _1kH=E(_1ki);}else{if(_1kg>=_1kE){var _1kI=_1kg!=_1kE?E(_1ki):E(_1kj);}else{var _1kI=[0,E(_1kC),_9];}var _1kJ=_1kI,_1kH=_1kJ;}var _1kK=_1kH,_1kL=_1kK;}else{var _1kL=[0,E(_1kC),_9];}var _1kM=_1kL,_1kG=_1kM;break;default:var _1kG=E(_1ki);}var _1kN=_1kG;}else{var _1kN=[0,E(_1kC),_1kF];}var _1kO=_1kN,_1kP=_1kO,_1kQ=_1kP,_1kR=_1kQ,_1kS=_1kR,_1kT=_1kS;return _1kT;})]);});},function(_1kU){return new F(function(){return A(_1k9,[new T(function(){var _1kV=E(_1kt),_1kW=E(_1kV[1]),_1kX=E(_1kU),_1kY=E(_1kX[1]),_1kZ=B(_E7(_1kW[1],_1kW[2],_1kW[3],_1kV[2],_1kY[1],_1kY[2],_1kY[3],_1kX[2])),_1l0=E(_1kZ[1]),_1l1=_1l0[2],_1l2=_1l0[3],_1l3=E(_1kZ[2]);if(!_1l3[0]){switch(B(_DZ(_1ke,_1l0[1]))){case 0:var _1l4=[0,E(_1l0),_9];break;case 1:if(_1kf>=_1l1){if(_1kf!=_1l1){var _1l5=E(_1ki);}else{if(_1kg>=_1l2){var _1l6=_1kg!=_1l2?E(_1ki):E(_1kj);}else{var _1l6=[0,E(_1l0),_9];}var _1l7=_1l6,_1l5=_1l7;}var _1l8=_1l5,_1l9=_1l8;}else{var _1l9=[0,E(_1l0),_9];}var _1la=_1l9,_1l4=_1la;break;default:var _1l4=E(_1ki);}var _1lb=_1l4;}else{var _1lb=[0,E(_1l0),_1l3];}var _1lc=_1lb,_1ld=_1lc,_1le=_1ld,_1lf=_1le,_1lg=_1lf,_1lh=_1lg;return _1lh;})]);});});});});});};switch(E(E(_1kc)[1])){case 9:var _1li=(_1k6+8|0)-B(_Hk(_1k6-1|0,8))|0;return new F(function(){return _1kd(_1k4,_1k5,_1li,[0,_1k4,_1k5,_1li]);});break;case 10:var _1lj=_1k5+1|0;return new F(function(){return _1kd(_1k4,_1lj,1,[0,_1k4,_1lj,1]);});break;default:var _1lk=_1k6+1|0;return new F(function(){return _1kd(_1k4,_1k5,_1lk,[0,_1k4,_1k5,_1lk]);});}}}},_1ll=function(_1lm,_1ln){return E(_1);},_1lo=function(_1lp,_1lq,_1lr,_1ls){var _1lt=E(_1lr);switch(_1lt[0]){case 0:var _1lu=E(_1ls);return _1lu[0]==0?E(_1):E(_1lu[1]);case 1:return new F(function(){return A(_1lp,[_1lt[1],_9]);});break;case 2:return new F(function(){return A(_1lq,[_1lt[1],[1,new T(function(){return B(_1lo(_1lp,_1lq,_1lt[2],_1ls));}),_9]]);});break;default:return new F(function(){return A(_1lq,[_1lt[1],[1,new T(function(){return B(_1lo(_1lp,_1lq,_1lt[2],_1ls));}),[1,new T(function(){return B(_1lo(_1lp,_1lq,_1lt[3],_1ls));}),_9]]]);});}},_1lv=function(_1lw,_1lx,_1ly,_1lz,_1lA,_1lB,_1lC,_1lD){var _1lE=E(_1lC);switch(_1lE[0]){case 0:return [0];case 1:return new F(function(){return A(_1lz,[_1lE[1],_9]);});break;case 2:return new F(function(){return A(_1lw,[_1lE[1],[1,new T(function(){return B(_1lo(_1lz,_1lA,_1lE[2],_1lD));}),_9]]);});break;case 3:return new F(function(){return A(_1lw,[_1lE[1],[1,new T(function(){return B(_1lo(_1lz,_1lA,_1lE[2],_1lD));}),[1,new T(function(){return B(_1lo(_1lz,_1lA,_1lE[3],_1lD));}),_9]]]);});break;case 4:return new F(function(){return A(_1lx,[_1lE[1],[1,new T(function(){return B(_1lv(_1lw,_1lx,_1ly,_1lz,_1lA,_1lB,_1lE[2],_1lD));}),_9]]);});break;case 5:return new F(function(){return A(_1lx,[_1lE[1],[1,new T(function(){return B(_1lv(_1lw,_1lx,_1ly,_1lz,_1lA,_1lB,_1lE[2],_1lD));}),[1,new T(function(){return B(_1lv(_1lw,_1lx,_1ly,_1lz,_1lA,_1lB,_1lE[3],_1lD));}),_9]]]);});break;default:var _1lF=_1lE[1],_1lG=_1lE[2];return new F(function(){return A(_1ly,[_1lF,[1,new T(function(){return B(A(_1lB,[new T(function(){return B(A(_1lG,[_2V]));}),_1lF]));}),[1,new T(function(){return B(_1lv(_1lw,_1lx,_1ly,_1lz,_1lA,_1lB,B(A(_1lG,[_2V])),[1,new T(function(){return B(A(_1lB,[new T(function(){return B(A(_1lG,[_2V]));}),_1lF]));}),_9]));}),_9]]]);});}},_1lH=[0,95],_1lI=[1,_1lH,_9],_1lJ=[1,_1lI,_9],_1lK=function(_1lL){var _1lM=function(_1lN){var _1lO=E(new T(function(){var _1lP=B(_145(_131,_1iH,[0,_1lL,E(_12W),E(_6B)]));if(!_1lP[0]){var _1lQ=E(_1lP[1]),_1lR=_1lQ[0]==0?[1,_1lQ[1]]:[0,_1lQ[1]];}else{var _1lS=E(_1lP[1]),_1lR=_1lS[0]==0?[1,_1lS[1]]:[0,_1lS[1]];}return _1lR;}));return _1lO[0]==0?function(_1lT,_1lU,_1lV,_1lW,_1lX){return new F(function(){return A(_1lW,[[0,[0,new T(function(){var _1lY=E(_1lO[1]),_1lZ=E(_1lY[1]);return B(_bc(_1lZ[1],_1lZ[2],_1lZ[3],_1lY[2]));})],_9],_1lT,new T(function(){return [0,E(E(_1lT)[2]),_9];})]);});}:function(_1m0,_1m1,_1m2,_1m3,_1m4){return new F(function(){return A(_1m3,[[0,[0,new T(function(){return B(_1lv(_Q,_u,_Q,_N,_Q,_1ll,_1lO[1],_1lJ));})],_9],_1m0,new T(function(){return [0,E(E(_1m0)[2]),_9];})]);});};};return function(_1m5,_1m6,_1m7,_1m8,_1m9){return new F(function(){return A(_Yt,[_1m5,function(_1ma,_1mb,_1mc){return new F(function(){return A(_1lM,[_,_1mb,_1m6,_1m7,function(_1md,_1me,_1mf){return new F(function(){return A(_1m6,[_1md,_1me,new T(function(){return B(_ER(_1mc,_1mf));})]);});},function(_1mg){return new F(function(){return A(_1m7,[new T(function(){return B(_ER(_1mc,_1mg));})]);});}]);});},_1m7,function(_1mh,_1mi,_1mj){return new F(function(){return A(_1lM,[_,_1mi,_1m6,_1m7,function(_1mk,_1ml,_1mm){return new F(function(){return A(_1m8,[_1mk,_1ml,new T(function(){return B(_ER(_1mj,_1mm));})]);});},function(_1mn){return new F(function(){return A(_1m9,[new T(function(){return B(_ER(_1mj,_1mn));})]);});}]);});},_1m9]);});};},_1mo=function(_1mp,_1mq,_1mr,_1ms,_1mt,_1mu,_1mv,_1mw,_1mx,_1my){return new F(function(){return _J3(_1mp,_1mq,function(_1mz){return !B(_9r(_Jv,_1mz,_1mr))?true:false;},_1ms,_1mt,_1mu,_1mv,_1mw,_1mx,_1my);});},_1mA=[0,9],_1mB=[1,_1mA,_9],_1mC=[0,10],_1mD=[1,_1mC,_1mB],_1mE=function(_1mF,_1mG,_1mH,_1mI,_1mJ){var _1mK=E(_1mF),_1mL=E(_1mK[2]);return new F(function(){return _1mo(_Hd,_JN,_1mD,_1mK[1],_1mL[1],_1mL[2],_1mL[3],_1mK[3],_1mG,_1mJ);});},_1mM=function(_1mN,_1mO,_1mP,_1mQ,_1mR){return new F(function(){return _EZ(_1mE,_1mN,function(_1mS,_1mT,_1mU){return new F(function(){return A(_1lK,[_1mS,_1mT,_1mO,_1mP,function(_1mV,_1mW,_1mX){return new F(function(){return A(_1mO,[_1mV,_1mW,new T(function(){return B(_ER(_1mU,_1mX));})]);});},function(_1mY){return new F(function(){return A(_1mP,[new T(function(){return B(_ER(_1mU,_1mY));})]);});}]);});},_1mP,function(_1mZ,_1n0,_1n1){return new F(function(){return A(_1lK,[_1mZ,_1n0,_1mO,_1mP,function(_1n2,_1n3,_1n4){return new F(function(){return A(_1mQ,[_1n2,_1n3,new T(function(){return B(_ER(_1n1,_1n4));})]);});},function(_1n5){return new F(function(){return A(_1mR,[new T(function(){return B(_ER(_1n1,_1n5));})]);});}]);});},_1mR);});},_1n6=function(_1n7,_1n8,_1n9,_1na,_1nb,_1nc){var _1nd=function(_1ne,_1nf,_1ng,_1nh,_1ni,_1nj){var _1nk=function(_1nl){var _1nm=[0,[1,[0,_1n7,_1ne,new T(function(){return B(_3d(_VL,_1nl));})]],_9];return function(_1nn,_1no,_1np,_1nq,_1nr){return new F(function(){return A(_Yt,[_1nn,function(_1ns,_1nt,_1nu){return new F(function(){return A(_1no,[_1nm,_1nt,new T(function(){var _1nv=E(E(_1nt)[2]),_1nw=E(_1nu),_1nx=E(_1nw[1]),_1ny=B(_E7(_1nx[1],_1nx[2],_1nx[3],_1nw[2],_1nv[1],_1nv[2],_1nv[3],_9));return [0,E(_1ny[1]),_1ny[2]];})]);});},_1np,function(_1nz,_1nA,_1nB){return new F(function(){return A(_1nq,[_1nm,_1nA,new T(function(){var _1nC=E(E(_1nA)[2]),_1nD=E(_1nB),_1nE=E(_1nD[1]),_1nF=B(_E7(_1nE[1],_1nE[2],_1nE[3],_1nD[2],_1nC[1],_1nC[2],_1nC[3],_9));return [0,E(_1nF[1]),_1nF[2]];})]);});},_1nr]);});};},_1nG=function(_1nH,_1nI,_1nJ,_1nK,_1nL){var _1nM=function(_1nN,_1nO,_1nP){return new F(function(){return A(_1nk,[_1nN,_1nO,_1nI,_1nJ,function(_1nQ,_1nR,_1nS){return new F(function(){return A(_1nK,[_1nQ,_1nR,new T(function(){return B(_ER(_1nP,_1nS));})]);});},function(_1nT){return new F(function(){return A(_1nL,[new T(function(){return B(_ER(_1nP,_1nT));})]);});}]);});},_1nU=function(_1nV){return new F(function(){return _1nM(_9,_1nH,new T(function(){var _1nW=E(E(_1nH)[2]),_1nX=E(_1nV),_1nY=E(_1nX[1]),_1nZ=B(_E7(_1nY[1],_1nY[2],_1nY[3],_1nX[2],_1nW[1],_1nW[2],_1nW[3],_9));return [0,E(_1nZ[1]),_1nZ[2]];}));});};return new F(function(){return _G2(_L2,_Lt,_1nH,function(_1o0,_1o1,_1o2){return new F(function(){return A(_1nk,[_1o0,_1o1,_1nI,_1nJ,function(_1o3,_1o4,_1o5){return new F(function(){return A(_1nI,[_1o3,_1o4,new T(function(){return B(_ER(_1o2,_1o5));})]);});},function(_1o6){return new F(function(){return A(_1nJ,[new T(function(){return B(_ER(_1o2,_1o6));})]);});}]);});},_1nU,_1nM,_1nU);});};return new F(function(){return _FC(_JP,_1nf,function(_1o7,_1o8,_1o9){return new F(function(){return _1nG(_1o8,_1ng,_1nh,function(_1oa,_1ob,_1oc){return new F(function(){return A(_1ng,[_1oa,_1ob,new T(function(){return B(_ER(_1o9,_1oc));})]);});},function(_1od){return new F(function(){return A(_1nh,[new T(function(){return B(_ER(_1o9,_1od));})]);});});});},_1nh,function(_1oe,_1of,_1og){return new F(function(){return _1nG(_1of,_1ng,_1nh,function(_1oh,_1oi,_1oj){return new F(function(){return A(_1ni,[_1oh,_1oi,new T(function(){return B(_ER(_1og,_1oj));})]);});},function(_1ok){return new F(function(){return A(_1nj,[new T(function(){return B(_ER(_1og,_1ok));})]);});});});});});},_1ol=function(_1om,_1on,_1oo,_1op,_1oq){return new F(function(){return _EZ(_WJ,_1om,function(_1or,_1os,_1ot){return new F(function(){return _1nd(_1or,_1os,_1on,_1oo,function(_1ou,_1ov,_1ow){return new F(function(){return A(_1on,[_1ou,_1ov,new T(function(){return B(_ER(_1ot,_1ow));})]);});},function(_1ox){return new F(function(){return A(_1oo,[new T(function(){return B(_ER(_1ot,_1ox));})]);});});});},_1oq,function(_1oy,_1oz,_1oA){return new F(function(){return _1nd(_1oy,_1oz,_1on,_1oo,function(_1oB,_1oC,_1oD){return new F(function(){return A(_1op,[_1oB,_1oC,new T(function(){return B(_ER(_1oA,_1oD));})]);});},function(_1oE){return new F(function(){return A(_1oq,[new T(function(){return B(_ER(_1oA,_1oE));})]);});});});},_1oq);});};return new F(function(){return _FC(_JP,_1n8,function(_1oF,_1oG,_1oH){return new F(function(){return _1ol(_1oG,_1n9,_1na,function(_1oI,_1oJ,_1oK){return new F(function(){return A(_1n9,[_1oI,_1oJ,new T(function(){return B(_ER(_1oH,_1oK));})]);});},function(_1oL){return new F(function(){return A(_1na,[new T(function(){return B(_ER(_1oH,_1oL));})]);});});});},_1na,function(_1oM,_1oN,_1oO){return new F(function(){return _1ol(_1oN,_1n9,_1na,function(_1oP,_1oQ,_1oR){return new F(function(){return A(_1nb,[_1oP,_1oQ,new T(function(){return B(_ER(_1oO,_1oR));})]);});},function(_1oS){return new F(function(){return A(_1nc,[new T(function(){return B(_ER(_1oO,_1oS));})]);});});});});});},_1oT=function(_1oU,_1oV,_1oW,_1oX,_1oY){return new F(function(){return A(_1iH,[_1oU,function(_1oZ,_1p0,_1p1){return new F(function(){return _1n6(_1oZ,_1p0,_1oV,_1oW,function(_1p2,_1p3,_1p4){return new F(function(){return A(_1oV,[_1p2,_1p3,new T(function(){return B(_ER(_1p1,_1p4));})]);});},function(_1p5){return new F(function(){return A(_1oW,[new T(function(){return B(_ER(_1p1,_1p5));})]);});});});},_1oW,function(_1p6,_1p7,_1p8){return new F(function(){return _1n6(_1p6,_1p7,_1oV,_1oW,function(_1p9,_1pa,_1pb){return new F(function(){return A(_1oX,[_1p9,_1pa,new T(function(){return B(_ER(_1p8,_1pb));})]);});},function(_1pc){return new F(function(){return A(_1oY,[new T(function(){return B(_ER(_1p8,_1pc));})]);});});});},_1oY]);});},_1pd=function(_1pe,_1pf,_1pg,_1ph){var _1pi=function(_1pj){var _1pk=E(_1pe),_1pl=E(_1pk[2]),_1pm=function(_1pn){var _1po=function(_1pp){return new F(function(){return A(_1ph,[new T(function(){var _1pq=E(_1pj),_1pr=E(_1pq[1]),_1ps=E(_1pn),_1pt=E(_1ps[1]),_1pu=E(_1pp),_1pv=E(_1pu[1]),_1pw=B(_E7(_1pt[1],_1pt[2],_1pt[3],_1ps[2],_1pv[1],_1pv[2],_1pv[3],_1pu[2])),_1px=E(_1pw[1]),_1py=B(_E7(_1pr[1],_1pr[2],_1pr[3],_1pq[2],_1px[1],_1px[2],_1px[3],_1pw[2]));return [0,E(_1py[1]),_1py[2]];})]);});};return new F(function(){return _1mM(_1pk,_1pf,_1po,function(_1pz,_1pA,_1pB){return new F(function(){return A(_1pg,[_1pz,_1pA,new T(function(){var _1pC=E(_1pj),_1pD=E(_1pC[1]),_1pE=E(_1pn),_1pF=E(_1pE[1]),_1pG=E(_1pB),_1pH=E(_1pG[1]),_1pI=B(_E7(_1pF[1],_1pF[2],_1pF[3],_1pE[2],_1pH[1],_1pH[2],_1pH[3],_1pG[2])),_1pJ=E(_1pI[1]),_1pK=B(_E7(_1pD[1],_1pD[2],_1pD[3],_1pC[2],_1pJ[1],_1pJ[2],_1pJ[3],_1pI[2]));return [0,E(_1pK[1]),_1pK[2]];})]);});},_1po);});};return new F(function(){return _1k2(_1pk[1],_1pl[1],_1pl[2],_1pl[3],_1pk[3],_1pf,_1pm,_1pm);});};return new F(function(){return _1oT(_1pe,_1pf,_1pi,_1pg,_1pi);});},_1pL=function(_1pM,_1pN,_1pO,_1pP,_1pQ){return new F(function(){return _1pd(_1pM,_1pN,_1pP,_1pQ);});},_14r=function(_1pR,_1pS,_1pT,_1pU,_1pV){return new F(function(){return _EZ(_1pL,_1pR,function(_1pW,_1pX,_1pY){return new F(function(){return _X9(_1pW,_1pX,_1pS,function(_1pZ,_1q0,_1q1){return new F(function(){return A(_1pS,[_1pZ,_1q0,new T(function(){return B(_ER(_1pY,_1q1));})]);});});});},_1pT,function(_1q2,_1q3,_1q4){return new F(function(){return _X9(_1q2,_1q3,_1pS,function(_1q5,_1q6,_1q7){return new F(function(){return A(_1pU,[_1q5,_1q6,new T(function(){return B(_ER(_1q4,_1q7));})]);});});});},_1pV);});},_1q8=function(_1q9,_1qa){return new F(function(){return _F(0,E(_1q9)[1],_1qa);});},_1qb=function(_1qc){return function(_mb,_mc){return new F(function(){return _6v(new T(function(){return B(_23(_1q8,_1qc,_9));}),_mb,_mc);});};},_1qd=function(_1qe){return function(_mb,_mc){return new F(function(){return _6v(new T(function(){return B(_1lv(_Q,_u,_Q,_N,_Q,_1ll,_1qe,_1lJ));}),_mb,_mc);});};},_1qf=new T(function(){return B(unCStr("open"));}),_1qg=new T(function(){return B(unCStr("termination"));}),_1qh=new T(function(){return B(unCStr("closed"));}),_1qi=function(_1qj){var _1qk=E(_1qj);return _1qk[0]==0?E(_BP):function(_1ql,_){var _1qm=B(A(new T(function(){var _1qn=E(_1qk[1]);return B(_1qo(_1qn[1],_1qn[2]));}),[_1ql,_])),_1qp=_1qm,_1qq=B(A(new T(function(){return B(_1qi(_1qk[2]));}),[_1ql,_])),_1qr=_1qq;return _1ql;};},_1qs=function(_1qt){var _1qu=E(_1qt);return _1qu[0]==0?E(_BP):function(_1qv,_){var _1qw=B(A(new T(function(){var _1qx=E(_1qu[1]);return B(_1qo(_1qx[1],_1qx[2]));}),[_1qv,_])),_1qy=_1qw,_1qz=B(A(new T(function(){return B(_1qs(_1qu[2]));}),[_1qv,_])),_1qA=_1qz;return _1qv;};},_1qB=new T(function(){return B(unCStr("SHOW"));}),_1qo=function(_1qC,_1qD){var _1qE=E(_1qC);if(!_1qE[0]){return function(_mb,_mc){return new F(function(){return _Ag(_6v,_1qE[1],_mb,_mc);});};}else{var _1qF=E(_1qE[1]),_1qG=_1qF[1],_1qH=_1qF[2],_1qI=_1qF[3];if(!B(_3x(_1qH,_1qB))){var _1qJ=E(_1qD);return _1qJ[0]==0?function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_1qK,_){var _1qL=B(_7i(_1qd,_1qG,_1qK,_)),_1qM=_1qL,_1qN=B(_7i(_7s,function(_1qO,_){var _1qP=B(_7i(_6v,_1qH,_1qO,_)),_1qQ=_1qP,_1qR=B(_7i(_1qb,_1qI,_1qO,_)),_1qS=_1qR;return _1qO;},_1qK,_)),_1qT=_1qN;return _1qK;},_mb,_mc);});}:function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_1qU,_){var _1qV=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1lv(_Q,_u,_Q,_N,_Q,_1ll,_1qG,_1lJ));})));}),_1qU,_)),_1qW=_1qV,_1qX=B(_Ag(_7s,function(_1qY,_){var _1qZ=B(_7i(_7s,new T(function(){return B(_1qs(_1qJ));}),_1qY,_)),_1r0=_1qZ,_1r1=B(_Ag(_7s,function(_1r2,_){var _1r3=B(_7i(_6v,_9,_1r2,_)),_1r4=_1r3,_1r5=B(A(_6C,[_6P,_1r4,_A3,_1qg,_])),_1r6=_1r5,_1r7=B(_7i(_7s,function(_1r8,_){var _1r9=B(_7i(_6v,_1qH,_1r8,_)),_1ra=_1r9,_1rb=B(_7i(_1qb,_1qI,_1r8,_)),_1rc=_1rb;return _1r8;},_1r2,_)),_1rd=_1r7;return _1r2;},_1qY,_)),_1re=_1r1;return _1qY;},_1qU,_)),_1rf=_1qX,_1rg=B(A(_6C,[_6P,_1rf,_A3,_1qh,_])),_1rh=_1rg;return _1qU;},_mb,_mc);});};}else{var _1ri=E(_1qD);return _1ri[0]==0?function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_By,_){return new F(function(){return _7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1lv(_Q,_u,_Q,_N,_Q,_1ll,_1qG,_1lJ));})));}),_By,_);});},_mb,_mc);});}:function(_mb,_mc){return new F(function(){return _Ag(_7s,function(_1rj,_){var _1rk=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1lv(_Q,_u,_Q,_N,_Q,_1ll,_1qG,_1lJ));})));}),_1rj,_)),_1rl=_1rk,_1rm=B(_Ag(_7s,function(_By,_){return new F(function(){return _7i(_7s,new T(function(){return B(_1qi(_1ri));}),_By,_);});},_1rj,_)),_1rn=_1rm,_1ro=B(A(_6C,[_6P,_1rn,_A3,_1qf,_])),_1rp=_1ro;return _1rj;},_mb,_mc);});};}}},_1rq=function(_1rr){var _1rs=E(_1rr);return _1rs[0]==0?E(_BP):function(_1rt,_){var _1ru=B(A(new T(function(){var _1rv=E(_1rs[1]);return B(_1qo(_1rv[1],_1rv[2]));}),[_1rt,_])),_1rw=_1ru,_1rx=B(A(new T(function(){return B(_1rq(_1rs[2]));}),[_1rt,_])),_1ry=_1rx;return _1rt;};},_1rz=[0,10],_1rA=[1,_1rz,_9],_1rB=function(_1rC,_1rD,_){var _1rE=jsCreateElem(toJSStr(E(_1rC))),_1rF=_1rE,_1rG=jsAppendChild(_1rF,E(_1rD)[1]);return [0,_1rF];},_1rH=function(_1rI,_1rJ,_1rK,_){var _1rL=B(_1rB(_1rI,_1rK,_)),_1rM=_1rL,_1rN=B(A(_1rJ,[_1rM,_])),_1rO=_1rN;return _1rM;},_1rP=new T(function(){return B(unCStr("()"));}),_1rQ=new T(function(){return B(unCStr("GHC.Tuple"));}),_1rR=new T(function(){return B(unCStr("ghc-prim"));}),_1rS=new T(function(){var _1rT=hs_wordToWord64(2170319554),_1rU=_1rT,_1rV=hs_wordToWord64(26914641),_1rW=_1rV;return [0,_1rU,_1rW,[0,_1rU,_1rW,_1rR,_1rQ,_1rP],_9];}),_1rX=function(_1rY){return E(_1rS);},_1rZ=new T(function(){return B(unCStr("PerchM"));}),_1s0=new T(function(){return B(unCStr("Haste.Perch"));}),_1s1=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1s2=new T(function(){var _1s3=hs_wordToWord64(3005229400),_1s4=_1s3,_1s5=hs_wordToWord64(2682402736),_1s6=_1s5;return [0,_1s4,_1s6,[0,_1s4,_1s6,_1s1,_1s0,_1rZ],_9];}),_1s7=function(_1s8){return E(_1s2);},_1s9=function(_1sa){var _1sb=E(_1sa);if(!_1sb[0]){return [0];}else{var _1sc=E(_1sb[1]);return [1,[0,_1sc[1],_1sc[2]],new T(function(){return B(_1s9(_1sb[2]));})];}},_1sd=function(_1se,_1sf){var _1sg=E(_1se);if(!_1sg){return [0,_9,_1sf];}else{var _1sh=E(_1sf);if(!_1sh[0]){return [0,_9,_9];}else{var _1si=new T(function(){var _1sj=B(_1sd(_1sg-1|0,_1sh[2]));return [0,_1sj[1],_1sj[2]];});return [0,[1,_1sh[1],new T(function(){return E(E(_1si)[1]);})],new T(function(){return E(E(_1si)[2]);})];}}},_1sk=[0,120],_1sl=[0,48],_1sm=function(_1sn){var _1so=new T(function(){var _1sp=B(_1sd(8,new T(function(){var _1sq=md5(toJSStr(E(_1sn))),_1sr=_1sq;return fromJSStr(_1sr);})));return [0,_1sp[1],_1sp[2]];}),_1ss=parseInt([0,toJSStr([1,_1sl,[1,_1sk,new T(function(){return E(E(_1so)[1]);})]])]),_1st=_1ss,_1su=new T(function(){var _1sv=B(_1sd(8,new T(function(){return E(E(_1so)[2]);})));return [0,_1sv[1],_1sv[2]];}),_1sw=parseInt([0,toJSStr([1,_1sl,[1,_1sk,new T(function(){return E(E(_1su)[1]);})]])]),_1sx=_1sw,_1sy=hs_mkWord64(_1st,_1sx),_1sz=_1sy,_1sA=parseInt([0,toJSStr([1,_1sl,[1,_1sk,new T(function(){return E(B(_1sd(8,new T(function(){return E(E(_1su)[2]);})))[1]);})]])]),_1sB=_1sA,_1sC=hs_mkWord64(_1sB,_1sB),_1sD=_1sC;return [0,_1sz,_1sD];},_1sE=function(_1sF,_1sG){var _1sH=jsShowI(_1sF),_1sI=_1sH,_1sJ=md5(_1sI),_1sK=_1sJ;return new F(function(){return _e(fromJSStr(_1sK),new T(function(){var _1sL=jsShowI(_1sG),_1sM=_1sL,_1sN=md5(_1sM),_1sO=_1sN;return fromJSStr(_1sO);},1));});},_1sP=function(_1sQ){var _1sR=E(_1sQ);return new F(function(){return _1sE(_1sR[1],_1sR[2]);});},_1sS=function(_1sT,_1sU){return function(_1sV){return E(new T(function(){var _1sW=B(A(_1sT,[_])),_1sX=E(_1sW[3]),_1sY=_1sX[1],_1sZ=_1sX[2],_1t0=B(_e(_1sW[4],[1,new T(function(){return B(A(_1sU,[_]));}),_9]));if(!_1t0[0]){var _1t1=[0,_1sY,_1sZ,_1sX,_9];}else{var _1t2=B(_1sm(new T(function(){return B(_8Q(B(_3d(_1sP,[1,[0,_1sY,_1sZ],new T(function(){return B(_1s9(_1t0));})]))));},1))),_1t1=[0,_1t2[1],_1t2[2],_1sX,_1t0];}var _1t3=_1t1,_1t4=_1t3;return _1t4;}));};},_1t5=new T(function(){return B(_1sS(_1s7,_1rX));}),_1t6=function(_1t7,_1t8,_1t9,_){var _1ta=E(_1t8),_1tb=B(A(_1t7,[_1t9,_])),_1tc=_1tb,_1td=B(A(_6C,[_6P,_1tc,_1ta[1],_1ta[2],_])),_1te=_1td;return _1tc;},_1tf=function(_1tg,_1th){while(1){var _1ti=(function(_1tj,_1tk){var _1tl=E(_1tk);if(!_1tl[0]){return E(_1tj);}else{_1tg=function(_1tm,_){return new F(function(){return _1t6(_1tj,_1tl[1],_1tm,_);});};_1th=_1tl[2];return null;}})(_1tg,_1th);if(_1ti!=null){return _1ti;}}},_1tn=new T(function(){return B(unCStr("value"));}),_1to=new T(function(){return B(unCStr("id"));}),_1tp=new T(function(){return B(unCStr("onclick"));}),_1tq=new T(function(){return B(unCStr("checked"));}),_1tr=[0,_1tq,_9],_1ts=[1,_1tr,_9],_1tt=new T(function(){return B(unCStr("type"));}),_1tu=new T(function(){return B(unCStr("input"));}),_1tv=function(_1tw,_){return new F(function(){return _1rB(_1tu,_1tw,_);});},_1tx=function(_1ty,_1tz,_1tA,_1tB,_1tC){var _1tD=new T(function(){var _1tE=new T(function(){return B(_1tf(_1tv,[1,[0,_1tt,_1tz],[1,[0,_1to,_1ty],[1,[0,_1tn,_1tA],_9]]]));});return !E(_1tB)?E(_1tE):B(_1tf(_1tE,_1ts));}),_1tF=E(_1tC);return _1tF[0]==0?E(_1tD):B(_1tf(_1tD,[1,[0,_1tp,_1tF[1]],_9]));},_1tG=new T(function(){return B(unCStr("href"));}),_1tH=[0,97],_1tI=[1,_1tH,_9],_1tJ=function(_1tK,_){return new F(function(){return _1rB(_1tI,_1tK,_);});},_1tL=function(_1tM,_1tN){return function(_1tO,_){var _1tP=B(A(new T(function(){return B(_1tf(_1tJ,[1,[0,_1tG,_1tM],_9]));}),[_1tO,_])),_1tQ=_1tP,_1tR=B(A(_1tN,[_1tQ,_])),_1tS=_1tR;return _1tQ;};},_1tT=function(_1tU){return new F(function(){return _1tL(_1tU,function(_1tm,_){return new F(function(){return _6v(_1tU,_1tm,_);});});});},_1tV=new T(function(){return B(unCStr("option"));}),_1tW=function(_1tX,_){return new F(function(){return _1rB(_1tV,_1tX,_);});},_1tY=new T(function(){return B(unCStr("selected"));}),_1tZ=[0,_1tY,_9],_1u0=[1,_1tZ,_9],_1u1=function(_1u2,_1u3,_1u4){var _1u5=new T(function(){return B(_1tf(_1tW,[1,[0,_1tn,_1u2],_9]));});if(!E(_1u4)){return function(_1u6,_){var _1u7=B(A(_1u5,[_1u6,_])),_1u8=_1u7,_1u9=B(A(_1u3,[_1u8,_])),_1ua=_1u9;return _1u8;};}else{return new F(function(){return _1tf(function(_1ub,_){var _1uc=B(A(_1u5,[_1ub,_])),_1ud=_1uc,_1ue=B(A(_1u3,[_1ud,_])),_1uf=_1ue;return _1ud;},_1u0);});}},_1ug=function(_1uh,_1ui){return new F(function(){return _1u1(_1uh,function(_1tm,_){return new F(function(){return _6v(_1uh,_1tm,_);});},_1ui);});},_1uj=new T(function(){return B(unCStr("method"));}),_1uk=new T(function(){return B(unCStr("action"));}),_1ul=new T(function(){return B(unCStr("UTF-8"));}),_1um=new T(function(){return B(unCStr("acceptCharset"));}),_1un=[0,_1um,_1ul],_1uo=new T(function(){return B(unCStr("form"));}),_1up=function(_1uq,_){return new F(function(){return _1rB(_1uo,_1uq,_);});},_1ur=function(_1us,_1ut,_1uu){return function(_1uv,_){var _1uw=B(A(new T(function(){return B(_1tf(_1up,[1,_1un,[1,[0,_1uk,_1us],[1,[0,_1uj,_1ut],_9]]]));}),[_1uv,_])),_1ux=_1uw,_1uy=B(A(_1uu,[_1ux,_])),_1uz=_1uy;return _1ux;};},_1uA=new T(function(){return B(unCStr("select"));}),_1uB=function(_1uC,_){return new F(function(){return _1rB(_1uA,_1uC,_);});},_1uD=function(_1uE,_1uF){return function(_1uG,_){var _1uH=B(A(new T(function(){return B(_1tf(_1uB,[1,[0,_1to,_1uE],_9]));}),[_1uG,_])),_1uI=_1uH,_1uJ=B(A(_1uF,[_1uI,_])),_1uK=_1uJ;return _1uI;};},_1uL=new T(function(){return B(unCStr("textarea"));}),_1uM=function(_1uN,_){return new F(function(){return _1rB(_1uL,_1uN,_);});},_1uO=function(_1uP,_1uQ){return function(_1uR,_){var _1uS=B(A(new T(function(){return B(_1tf(_1uM,[1,[0,_1to,_1uP],_9]));}),[_1uR,_])),_1uT=_1uS,_1uU=B(_6v(_1uQ,_1uT,_)),_1uV=_1uU;return _1uT;};},_1uW=new T(function(){return B(unCStr("color:red"));}),_1uX=new T(function(){return B(unCStr("style"));}),_1uY=[0,_1uX,_1uW],_1uZ=[1,_1uY,_9],_1v0=[0,98],_1v1=[1,_1v0,_9],_1v2=function(_1v3){return new F(function(){return _1tf(function(_1v4,_){var _1v5=B(_1rB(_1v1,_1v4,_)),_1v6=_1v5,_1v7=B(A(_1v3,[_1v6,_])),_1v8=_1v7;return _1v6;},_1uZ);});},_1v9=function(_1va,_1vb,_){return new F(function(){return _zP(_1va,_1vb,_);});},_1vc=function(_1vd,_1ve,_1vf,_){var _1vg=B(A(_1vd,[_1vf,_])),_1vh=_1vg,_1vi=B(A(_1ve,[_1vf,_])),_1vj=_1vi;return _1vf;},_1vk=[0,_6S,_1vc,_1v9],_1vl=[0,_1vk,_1t5,_6v,_6v,_1rH,_1v2,_1tL,_1tT,_1tx,_1uO,_1uD,_1u1,_1ug,_1ur,_1tf],_1vm=function(_1vn,_1vo,_){var _1vp=B(A(_1vo,[_])),_1vq=_1vp;return _1vn;},_1vr=function(_1vs,_1vt,_){var _1vu=B(A(_1vt,[_])),_1vv=_1vu;return new T(function(){return B(A(_1vs,[_1vv]));});},_1vw=[0,_1vr,_1vm],_1vx=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1vy=new T(function(){return B(unCStr("base"));}),_1vz=new T(function(){return B(unCStr("IOException"));}),_1vA=new T(function(){var _1vB=hs_wordToWord64(4053623282),_1vC=_1vB,_1vD=hs_wordToWord64(3693590983),_1vE=_1vD;return [0,_1vC,_1vE,[0,_1vC,_1vE,_1vy,_1vx,_1vz],_9];}),_1vF=function(_1vG){return E(_1vA);},_1vH=function(_1vI){var _1vJ=E(_1vI);return new F(function(){return _1I(B(_1G(_1vJ[1])),_1vF,_1vJ[2]);});},_1vK=new T(function(){return B(unCStr(": "));}),_1vL=[0,41],_1vM=new T(function(){return B(unCStr(" ("));}),_1vN=new T(function(){return B(unCStr("already exists"));}),_1vO=new T(function(){return B(unCStr("does not exist"));}),_1vP=new T(function(){return B(unCStr("protocol error"));}),_1vQ=new T(function(){return B(unCStr("failed"));}),_1vR=new T(function(){return B(unCStr("invalid argument"));}),_1vS=new T(function(){return B(unCStr("inappropriate type"));}),_1vT=new T(function(){return B(unCStr("hardware fault"));}),_1vU=new T(function(){return B(unCStr("unsupported operation"));}),_1vV=new T(function(){return B(unCStr("timeout"));}),_1vW=new T(function(){return B(unCStr("resource vanished"));}),_1vX=new T(function(){return B(unCStr("interrupted"));}),_1vY=new T(function(){return B(unCStr("resource busy"));}),_1vZ=new T(function(){return B(unCStr("resource exhausted"));}),_1w0=new T(function(){return B(unCStr("end of file"));}),_1w1=new T(function(){return B(unCStr("illegal operation"));}),_1w2=new T(function(){return B(unCStr("permission denied"));}),_1w3=new T(function(){return B(unCStr("user error"));}),_1w4=new T(function(){return B(unCStr("unsatisified constraints"));}),_1w5=new T(function(){return B(unCStr("system error"));}),_1w6=function(_1w7,_1w8){switch(E(_1w7)){case 0:return new F(function(){return _e(_1vN,_1w8);});break;case 1:return new F(function(){return _e(_1vO,_1w8);});break;case 2:return new F(function(){return _e(_1vY,_1w8);});break;case 3:return new F(function(){return _e(_1vZ,_1w8);});break;case 4:return new F(function(){return _e(_1w0,_1w8);});break;case 5:return new F(function(){return _e(_1w1,_1w8);});break;case 6:return new F(function(){return _e(_1w2,_1w8);});break;case 7:return new F(function(){return _e(_1w3,_1w8);});break;case 8:return new F(function(){return _e(_1w4,_1w8);});break;case 9:return new F(function(){return _e(_1w5,_1w8);});break;case 10:return new F(function(){return _e(_1vP,_1w8);});break;case 11:return new F(function(){return _e(_1vQ,_1w8);});break;case 12:return new F(function(){return _e(_1vR,_1w8);});break;case 13:return new F(function(){return _e(_1vS,_1w8);});break;case 14:return new F(function(){return _e(_1vT,_1w8);});break;case 15:return new F(function(){return _e(_1vU,_1w8);});break;case 16:return new F(function(){return _e(_1vV,_1w8);});break;case 17:return new F(function(){return _e(_1vW,_1w8);});break;default:return new F(function(){return _e(_1vX,_1w8);});}},_1w9=[0,125],_1wa=new T(function(){return B(unCStr("{handle: "));}),_1wb=function(_1wc,_1wd,_1we,_1wf,_1wg,_1wh){var _1wi=new T(function(){var _1wj=new T(function(){return B(_1w6(_1wd,new T(function(){var _1wk=E(_1wf);return _1wk[0]==0?E(_1wh):B(_e(_1vM,new T(function(){return B(_e(_1wk,[1,_1vL,_1wh]));},1)));},1)));},1),_1wl=E(_1we);return _1wl[0]==0?E(_1wj):B(_e(_1wl,new T(function(){return B(_e(_1vK,_1wj));},1)));},1),_1wm=E(_1wg);if(!_1wm[0]){var _1wn=E(_1wc);if(!_1wn[0]){return E(_1wi);}else{var _1wo=E(_1wn[1]);return _1wo[0]==0?B(_e(_1wa,new T(function(){return B(_e(_1wo[1],[1,_1w9,new T(function(){return B(_e(_1vK,_1wi));})]));},1))):B(_e(_1wa,new T(function(){return B(_e(_1wo[1],[1,_1w9,new T(function(){return B(_e(_1vK,_1wi));})]));},1)));}}else{return new F(function(){return _e(_1wm[1],new T(function(){return B(_e(_1vK,_1wi));},1));});}},_1wp=function(_1wq){var _1wr=E(_1wq);return new F(function(){return _1wb(_1wr[1],_1wr[2],_1wr[3],_1wr[4],_1wr[6],_9);});},_1ws=function(_1wt,_1wu){var _1wv=E(_1wt);return new F(function(){return _1wb(_1wv[1],_1wv[2],_1wv[3],_1wv[4],_1wv[6],_1wu);});},_1ww=function(_1wx,_1wy){return new F(function(){return _23(_1ws,_1wx,_1wy);});},_1wz=function(_1wA,_1wB,_1wC){var _1wD=E(_1wB);return new F(function(){return _1wb(_1wD[1],_1wD[2],_1wD[3],_1wD[4],_1wD[6],_1wC);});},_1wE=[0,_1wz,_1wp,_1ww],_1wF=new T(function(){return [0,_1vF,_1wE,_1wG,_1vH];}),_1wG=function(_1wH){return [0,_1wF,_1wH];},_1wI=7,_1wJ=function(_1wK){return [0,_4O,_1wI,_9,_1wK,_4O,_4O];},_1wL=function(_1wM,_){return new F(function(){return die(new T(function(){return B(_1wG(new T(function(){return B(_1wJ(_1wM));})));}));});},_1wN=function(_1wO,_){return new F(function(){return _1wL(_1wO,_);});},_1wP=function(_1wQ,_){return new F(function(){return _1wN(_1wQ,_);});},_1wR=function(_1wS,_){return new F(function(){return _1wP(_1wS,_);});},_1wT=function(_1wU,_1wV,_){var _1wW=B(A(_1wU,[_])),_1wX=_1wW;return new F(function(){return A(_1wV,[_1wX,_]);});},_1wY=function(_1wZ,_1x0,_){var _1x1=B(A(_1wZ,[_])),_1x2=_1x1;return new F(function(){return A(_1x0,[_]);});},_1x3=[0,_1wT,_1wY,_6S,_1wR],_1x4=[0,_1x3,_6P],_1x5=function(_1x6){return E(E(_1x6)[1]);},_1x7=function(_1x8){return E(E(_1x8)[2]);},_1x9=function(_1xa,_1xb){var _1xc=new T(function(){return B(_1x5(_1xa));});return function(_1xd){return new F(function(){return A(new T(function(){return B(_1et(_1xc));}),[new T(function(){return B(A(_1x7,[_1xa,_1xb]));}),function(_1xe){return new F(function(){return A(new T(function(){return B(_JH(_1xc));}),[[0,_1xe,_1xd]]);});}]);});};},_1xf=function(_1xg,_1xh){return [0,_1xg,function(_1xi){return new F(function(){return _1x9(_1xh,_1xi);});}];},_1xj=function(_1xk,_1xl,_1xm,_1xn){return new F(function(){return A(_1et,[_1xk,new T(function(){return B(A(_1xl,[_1xn]));}),function(_1xo){return new F(function(){return A(_1xm,[new T(function(){return E(E(_1xo)[1]);}),new T(function(){return E(E(_1xo)[2]);})]);});}]);});},_1xp=function(_1xq,_1xr,_1xs,_1xt){return new F(function(){return A(_1et,[_1xq,new T(function(){return B(A(_1xr,[_1xt]));}),function(_1xu){return new F(function(){return A(_1xs,[new T(function(){return E(E(_1xu)[2]);})]);});}]);});},_1xv=function(_1xw,_1xx,_1xy,_1xz){return new F(function(){return _1xp(_1xw,_1xx,_1xy,_1xz);});},_1xA=function(_1xB){return E(E(_1xB)[4]);},_1xC=function(_1xD,_1xE){return function(_1xF){return E(new T(function(){return B(A(_1xA,[_1xD,_1xE]));}));};},_1xG=function(_1xH){return [0,function(_1xx,_1xy,_1xz){return new F(function(){return _1xj(_1xH,_1xx,_1xy,_1xz);});},function(_1xx,_1xy,_1xz){return new F(function(){return _1xv(_1xH,_1xx,_1xy,_1xz);});},function(_1xI,_1xJ){return new F(function(){return A(new T(function(){return B(_JH(_1xH));}),[[0,_1xI,_1xJ]]);});},function(_1xz){return new F(function(){return _1xC(_1xH,_1xz);});}];},_1xK=function(_1xL,_1xM,_1xN){return new F(function(){return A(_JH,[_1xL,[0,_1xM,_1xN]]);});},_1xO=[0,10],_1xP=function(_1xQ,_1xR){var _1xS=E(_1xR);if(!_1xS[0]){return E(_6P);}else{var _1xT=_1xS[1],_1xU=E(_1xS[2]);if(!_1xU[0]){var _1xV=E(_1xT);return new F(function(){return _1xW(_1xO,_1xV[3],_1xV[4]);});}else{return function(_1xX){return new F(function(){return A(new T(function(){var _1xY=E(_1xT);return B(_1xW(_1xO,_1xY[3],_1xY[4]));}),[new T(function(){return B(A(_1xQ,[new T(function(){return B(A(new T(function(){return B(_1xP(_1xQ,_1xU));}),[_1xX]));})]));})]);});};}}},_1xZ=new T(function(){return B(unCStr("(->)"));}),_1y0=new T(function(){return B(unCStr("GHC.Prim"));}),_1y1=new T(function(){var _1y2=hs_wordToWord64(4173248105),_1y3=_1y2,_1y4=hs_wordToWord64(4270398258),_1y5=_1y4;return [0,_1y3,_1y5,[0,_1y3,_1y5,_1rR,_1y0,_1xZ],_9];}),_1y6=new T(function(){return E(E(_1y1)[3]);}),_1y7=new T(function(){return B(unCStr("GHC.Types"));}),_1y8=new T(function(){return B(unCStr("[]"));}),_1y9=new T(function(){var _1ya=hs_wordToWord64(4033920485),_1yb=_1ya,_1yc=hs_wordToWord64(786266835),_1yd=_1yc;return [0,_1yb,_1yd,[0,_1yb,_1yd,_1rR,_1y7,_1y8],_9];}),_1ye=[1,_1rS,_9],_1yf=function(_1yg){var _1yh=E(_1yg);if(!_1yh[0]){return [0];}else{var _1yi=E(_1yh[1]);return [1,[0,_1yi[1],_1yi[2]],new T(function(){return B(_1yf(_1yh[2]));})];}},_1yj=new T(function(){var _1yk=E(_1y9),_1yl=E(_1yk[3]),_1ym=B(_e(_1yk[4],_1ye));if(!_1ym[0]){var _1yn=E(_1yl);}else{var _1yo=B(_1sm(new T(function(){return B(_8Q(B(_3d(_1sP,[1,[0,_1yl[1],_1yl[2]],new T(function(){return B(_1yf(_1ym));})]))));},1))),_1yn=E(_1yl);}var _1yp=_1yn,_1yq=_1yp;return _1yq;}),_1yr=[0,8],_1ys=[0,32],_1yt=function(_1yu){return [1,_1ys,_1yu];},_1yv=new T(function(){return B(unCStr(" -> "));}),_1yw=[0,9],_1yx=[0,93],_1yy=[0,91],_1yz=[0,41],_1yA=[0,44],_1yB=function(_1yu){return [1,_1yA,_1yu];},_1yC=[0,40],_1yD=[0,0],_1xW=function(_1yE,_1yF,_1yG){var _1yH=E(_1yG);if(!_1yH[0]){return function(_1yI){return new F(function(){return _e(E(_1yF)[5],_1yI);});};}else{var _1yJ=_1yH[1],_1yK=function(_1yL){var _1yM=E(_1yF)[5],_1yN=function(_1yO){var _1yP=new T(function(){return B(_1xP(_1yt,_1yH));});return E(_1yE)[1]<=9?function(_1yQ){return new F(function(){return _e(_1yM,[1,_1ys,new T(function(){return B(A(_1yP,[_1yQ]));})]);});}:function(_1yR){return [1,_E,new T(function(){return B(_e(_1yM,[1,_1ys,new T(function(){return B(A(_1yP,[[1,_D,_1yR]]));})]));})];};},_1yS=E(_1yM);if(!_1yS[0]){return new F(function(){return _1yN(_);});}else{if(E(E(_1yS[1])[1])==40){var _1yT=E(_1yS[2]);if(!_1yT[0]){return new F(function(){return _1yN(_);});}else{if(E(E(_1yT[1])[1])==44){return function(_1yU){return [1,_1yC,new T(function(){return B(A(new T(function(){return B(_1xP(_1yB,_1yH));}),[[1,_1yz,_1yU]]));})];};}else{return new F(function(){return _1yN(_);});}}}else{return new F(function(){return _1yN(_);});}}},_1yV=E(_1yH[2]);if(!_1yV[0]){var _1yW=E(_1yF),_1yX=E(_1yj),_1yY=hs_eqWord64(_1yW[1],_1yX[1]),_1yZ=_1yY;if(!E(_1yZ)){return new F(function(){return _1yK(_);});}else{var _1z0=hs_eqWord64(_1yW[2],_1yX[2]),_1z1=_1z0;if(!E(_1z1)){return new F(function(){return _1yK(_);});}else{return function(_1z2){return [1,_1yy,new T(function(){return B(A(new T(function(){var _1z3=E(_1yJ);return B(_1xW(_1yD,_1z3[3],_1z3[4]));}),[[1,_1yx,_1z2]]));})];};}}}else{if(!E(_1yV[2])[0]){var _1z4=E(_1yF),_1z5=E(_1y6),_1z6=hs_eqWord64(_1z4[1],_1z5[1]),_1z7=_1z6;if(!E(_1z7)){return new F(function(){return _1yK(_);});}else{var _1z8=hs_eqWord64(_1z4[2],_1z5[2]),_1z9=_1z8;if(!E(_1z9)){return new F(function(){return _1yK(_);});}else{var _1za=new T(function(){var _1zb=E(_1yV[1]);return B(_1xW(_1yr,_1zb[3],_1zb[4]));}),_1zc=new T(function(){var _1zd=E(_1yJ);return B(_1xW(_1yw,_1zd[3],_1zd[4]));});return E(_1yE)[1]<=8?function(_1ze){return new F(function(){return A(_1zc,[new T(function(){return B(_e(_1yv,new T(function(){return B(A(_1za,[_1ze]));},1)));})]);});}:function(_1zf){return [1,_E,new T(function(){return B(A(_1zc,[new T(function(){return B(_e(_1yv,new T(function(){return B(A(_1za,[[1,_D,_1zf]]));},1)));})]));})];};}}}else{return new F(function(){return _1yK(_);});}}}},_1zg=function(_1zh,_1zi){return new F(function(){return A(_1zh,[function(_){return new F(function(){return jsFind(toJSStr(E(_1zi)));});}]);});},_1zj=[0],_1zk=function(_1zl){return E(E(_1zl)[3]);},_1zm=new T(function(){return [0,"value"];}),_1zn=function(_1zo){return E(E(_1zo)[6]);},_1zp=function(_1zq){return E(E(_1zq)[1]);},_1zr=new T(function(){return B(unCStr("Char"));}),_1zs=new T(function(){var _1zt=hs_wordToWord64(3763641161),_1zu=_1zt,_1zv=hs_wordToWord64(1343745632),_1zw=_1zv;return [0,_1zu,_1zw,[0,_1zu,_1zw,_1rR,_1y7,_1zr],_9];}),_1zx=function(_1zy){return E(_1zs);},_1zz=function(_1zA){return E(_1y9);},_1zB=new T(function(){return B(_1sS(_1zz,_1zx));}),_1zC=new T(function(){return B(A(_1zB,[_]));}),_1zD=function(_1zE,_1zF,_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM){var _1zN=new T(function(){return B(A(_1zH,[_1zj]));});return new F(function(){return A(_1zF,[new T(function(){return B(_1zg(E(_1zE)[2],_1zM));}),function(_1zO){var _1zP=E(_1zO);return _1zP[0]==0?E(_1zN):B(A(_1zF,[new T(function(){return B(A(E(_1zE)[2],[function(_){var _1zQ=jsGet(E(_1zP[1])[1],E(_1zm)[1]),_1zR=_1zQ;return [1,new T(function(){return fromJSStr(_1zR);})];}]));}),function(_1zS){var _1zT=E(_1zS);if(!_1zT[0]){return E(_1zN);}else{var _1zU=_1zT[1];if(!E(new T(function(){var _1zV=B(A(_1zJ,[_])),_1zW=E(_1zC),_1zX=hs_eqWord64(_1zV[1],_1zW[1]),_1zY=_1zX;if(!E(_1zY)){var _1zZ=false;}else{var _1A0=hs_eqWord64(_1zV[2],_1zW[2]),_1A1=_1A0,_1zZ=E(_1A1)==0?false:true;}var _1A2=_1zZ,_1A3=_1A2;return _1A3;}))){var _1A4=function(_1A5){return new F(function(){return A(_1zH,[[1,_1zU,new T(function(){return B(A(new T(function(){return B(_1zn(_1zL));}),[new T(function(){return B(A(new T(function(){return B(_1zk(_1zL));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1zU,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1A6=B(A(_1zJ,[_]));return B(A(_1xW,[_1yD,_1A6[3],_1A6[4],_9]));})));})));})));})]));})]));})]]);});},_1A7=B(A(new T(function(){return B(A(_1zp,[_1zK,_4x]));}),[_1zU]));if(!_1A7[0]){return new F(function(){return _1A4(_);});}else{var _1A8=E(_1A7[1]);return E(_1A8[2])[0]==0?E(_1A7[2])[0]==0?B(A(_1zH,[[2,_1A8[1]]])):B(_1A4(_)):B(_1A4(_));}}else{return new F(function(){return A(_1zH,[[2,_1zU]]);});}}}]));}]);});},_1A9=function(_1Aa){return E(E(_1Aa)[10]);},_1Ab=function(_1Ac){return new F(function(){return _LJ([1,function(_1Ad){return new F(function(){return A(_Tj,[_1Ad,function(_1Ae){return E(new T(function(){return B(_Uz(function(_1Af){var _1Ag=E(_1Af);return _1Ag[0]==0?B(A(_1Ac,[_1Ag[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_UV(_1Ah,_1Ac))];}));});},_1Ah=function(_1Ai,_1Aj){return new F(function(){return _1Ab(_1Aj);});},_1Ak=[0,91],_1Al=[1,_1Ak,_9],_1Am=function(_1An,_1Ao){var _1Ap=function(_1Aq,_1Ar){return [1,function(_1As){return new F(function(){return A(_Tj,[_1As,function(_1At){return E(new T(function(){return B(_Uz(function(_1Au){var _1Av=E(_1Au);if(_1Av[0]==2){var _1Aw=E(_1Av[1]);if(!_1Aw[0]){return [2];}else{var _1Ax=_1Aw[2];switch(E(E(_1Aw[1])[1])){case 44:return E(_1Ax)[0]==0?!E(_1Aq)?[2]:E(new T(function(){return B(A(_1An,[_UU,function(_1Ay){return new F(function(){return _1Ap(_OQ,function(_1Az){return new F(function(){return A(_1Ar,[[1,_1Ay,_1Az]]);});});});}]));})):[2];case 93:return E(_1Ax)[0]==0?E(new T(function(){return B(A(_1Ar,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1AA=function(_1AB){return new F(function(){return _LJ([1,function(_1AC){return new F(function(){return A(_Tj,[_1AC,function(_1AD){return E(new T(function(){return B(_Uz(function(_1AE){var _1AF=E(_1AE);return _1AF[0]==2?!B(_3x(_1AF[1],_1Al))?[2]:E(new T(function(){return B(_LJ(B(_1Ap(_4y,_1AB)),new T(function(){return B(A(_1An,[_UU,function(_1AG){return new F(function(){return _1Ap(_OQ,function(_1AH){return new F(function(){return A(_1AB,[[1,_1AG,_1AH]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_UV(function(_1AI,_1AJ){return new F(function(){return _1AA(_1AJ);});},_1AB))];}));});};return new F(function(){return _1AA(_1Ao);});},_1AK=function(_1AL){return new F(function(){return _LJ(B(_LJ([1,function(_1AM){return new F(function(){return A(_Tj,[_1AM,function(_1AN){return E(new T(function(){return B(_Uz(function(_1AO){var _1AP=E(_1AO);return _1AP[0]==1?B(A(_1AL,[_1AP[1]])):[2];}));}));}]);});}],new T(function(){return B(_1Am(_1Ah,_1AL));}))),new T(function(){return [1,B(_UV(_1AQ,_1AL))];}));});},_1AQ=function(_1AR,_1AS){return new F(function(){return _1AK(_1AS);});},_1AT=new T(function(){return B(_1AK(_Ms));}),_1AU=function(_1AV){return new F(function(){return _Lz(_1AT,_1AV);});},_1AW=new T(function(){return B(_1Ab(_Ms));}),_1AX=function(_1AV){return new F(function(){return _Lz(_1AW,_1AV);});},_1AY=function(_1AZ){return E(_1AX);},_1B0=[0,_1AY,_1AU,_1Ah,_1AQ],_1B1=function(_1B2){return E(E(_1B2)[4]);},_1B3=function(_1B4,_1B5,_1B6){return new F(function(){return _1Am(new T(function(){return B(_1B1(_1B4));}),_1B6);});},_1B7=function(_1B8){return function(_mb){return new F(function(){return _Lz(new T(function(){return B(_1Am(new T(function(){return B(_1B1(_1B8));}),_Ms));}),_mb);});};},_1B9=function(_1Ba,_1Bb){return function(_mb){return new F(function(){return _Lz(new T(function(){return B(A(_1B1,[_1Ba,_1Bb,_Ms]));}),_mb);});};},_1Bc=function(_1Bd){return [0,function(_1AV){return new F(function(){return _1B9(_1Bd,_1AV);});},new T(function(){return B(_1B7(_1Bd));}),new T(function(){return B(_1B1(_1Bd));}),function(_1Be,_1AV){return new F(function(){return _1B3(_1Bd,_1Be,_1AV);});}];},_1Bf=new T(function(){return B(_1Bc(_1B0));}),_1Bg=function(_1Bh,_1Bi,_1Bj){var _1Bk=new T(function(){return B(_1A9(_1Bh));}),_1Bl=new T(function(){return B(_1x5(_1Bj));}),_1Bm=new T(function(){return B(_JH(_1Bl));});return function(_1Bn,_1Bo){return new F(function(){return A(new T(function(){return B(_1et(_1Bl));}),[new T(function(){return B(A(new T(function(){return B(_1et(_1Bl));}),[new T(function(){return B(A(new T(function(){return B(_JH(_1Bl));}),[[0,_1Bo,_1Bo]]));}),function(_1Bp){var _1Bq=new T(function(){return E(E(_1Bp)[1]);}),_1Br=new T(function(){return E(E(_1Bq)[2]);});return new F(function(){return A(new T(function(){return B(_1et(_1Bl));}),[new T(function(){return B(A(new T(function(){return B(_JH(_1Bl));}),[[0,_6B,new T(function(){var _1Bs=E(_1Bq);return [0,_1Bs[1],new T(function(){return [0,E(_1Br)[1]+1|0];}),_1Bs[3],_1Bs[4],_1Bs[5],_1Bs[6],_1Bs[7]];})]]));}),function(_1Bt){return new F(function(){return A(new T(function(){return B(_JH(_1Bl));}),[[0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_1Br)[1],_9)),new T(function(){return E(E(_1Bq)[1]);},1)));})],new T(function(){return E(E(_1Bt)[2]);})]]);});}]);});}]));}),function(_1Bu){var _1Bv=new T(function(){return E(E(_1Bu)[1]);});return new F(function(){return A(new T(function(){return B(_1et(_1Bl));}),[new T(function(){return B(A(_1zD,[new T(function(){return B(_1xf(new T(function(){return B(_1xG(_1Bl));}),_1Bj));}),function(_1Bw,_1tm,_1Bx){return new F(function(){return _1xj(_1Bl,_1Bw,_1tm,_1Bx);});},function(_1Bw,_1tm,_1Bx){return new F(function(){return _1xv(_1Bl,_1Bw,_1tm,_1Bx);});},function(_1tm,_1Bx){return new F(function(){return _1xK(_1Bl,_1tm,_1Bx);});},function(_1Bx){return new F(function(){return _1xC(_1Bl,_1Bx);});},_1zB,_1Bf,_1Bh,_1Bv,new T(function(){return E(E(_1Bu)[2]);})]));}),function(_1By){var _1Bz=E(_1By),_1BA=_1Bz[2],_1BB=E(_1Bz[1]);switch(_1BB[0]){case 0:return new F(function(){return A(_1Bm,[[0,[0,new T(function(){return B(A(_1Bk,[_1Bv,_1Bn]));}),_4O],_1BA]]);});break;case 1:return new F(function(){return A(_1Bm,[[0,[0,new T(function(){return B(A(_1Bk,[_1Bv,_1BB[1]]));}),_4O],_1BA]]);});break;default:var _1BC=_1BB[1];return new F(function(){return A(_1Bm,[[0,[0,new T(function(){return B(A(_1Bk,[_1Bv,_1BC]));}),[1,_1BC]],_1BA]]);});}}]);});}]);});};},_1BD=new T(function(){return B(_1Bg(_1vl,_1vw,_1x4));}),_1BE=function(_1BF){return E(E(_1BF)[2]);},_1BG=function(_1BH){return E(E(_1BH)[1]);},_1BI=function(_1BJ,_1BK,_1BL){return function(_1BM,_){var _1BN=B(A(_1BK,[_1BM,_])),_1BO=_1BN,_1BP=E(_1BO),_1BQ=E(_1BP[1]),_1BR=new T(function(){return B(A(new T(function(){return B(_1BE(_1BJ));}),[_1BL,function(_){var _1BS=E(E(_1BM)[4]),_1BT=B(A(_1BS[1],[_])),_1BU=_1BT,_1BV=E(_1BU);if(!_1BV[0]){return _6B;}else{var _1BW=B(A(_1BS[2],[_1BV[1],_])),_1BX=_1BW;return _6B;}}]));});return [0,[0,function(_1BY,_){var _1BZ=B(A(_1BQ[1],[_1BY,_])),_1C0=_1BZ,_1C1=E(_1C0),_1C2=E(_1BR),_1C3=jsSetCB(_1C1[1],toJSStr(E(new T(function(){return B(A(_1BG,[_1BJ,_1BL]));}))),_1BR),_1C4=_1C3;return _1C1;},_1BQ[2]],_1BP[2]];};},_1C5=function(_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_1Cf,_1Cg){return function(_1Ch,_1Ci){return function(_mb,_mc){return new F(function(){return _7u(function(_1Cj,_){var _1Ck=B(A(new T(function(){return B(_1BI(_6u,new T(function(){return B(_1BI(_6u,new T(function(){return B(A(_1BD,[_1Ci]));}),_1p));}),_1o));}),[_1Cj,_])),_1Cl=_1Ck,_1Cm=E(_1Cl),_1Cn=E(_1Cm[1]);return [0,[0,function(_1Co,_){var _1Cp=B(A(_1Cn[1],[_1Co,_])),_1Cq=_1Cp,_1Cr=B(A(_6C,[_6P,_1Cq,_A3,_D0,_])),_1Cs=_1Cr;return _1Cq;},_1Cn[2]],_1Cm[2]];},function(_1Ct){var _1Cu=new T(function(){var _1Cv=B(_145(_131,_14r,[0,new T(function(){return B(_e(_1Ct,_1rA));}),E(_12W),E(_6B)]));if(!_1Cv[0]){var _1Cw=E(_1Cv[1]);if(!_1Cw[0]){var _1Cx=E(E(_1Cw[1])[1]);}else{var _1Cx=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1Cw[1]));})));})],_9],_9];}var _1Cy=_1Cx;}else{var _1Cz=E(_1Cv[1]);if(!_1Cz[0]){var _1CA=E(E(_1Cz[1])[1]);}else{var _1CA=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1Cz[1]));})));})],_9],_9];}var _1Cy=_1CA;}return _1Cy;});return function(_mb,_mc){return new F(function(){return _7u(_D7,function(_1CB,_1CC,_){return new F(function(){return _7u(_Dc,function(_1CD,_1CE,_){return new F(function(){return _7u(_Dh,function(_1CF,_1CG,_){return new F(function(){return _7u(function(_1CH,_){return [0,[0,function(_1CI,_){var _1CJ=B(_Ag(_6v,_9,_1CI,_)),_1CK=_1CJ,_1CL=B(A(_6C,[_6P,_1CK,_6O,_1CB,_])),_1CM=_1CL,_1CN=B(A(_6C,[_6P,_1CK,_A3,_Di,_])),_1CO=_1CN;return _1CK;},_Dn],_1CH];},function(_1CP,_1CQ,_){return new F(function(){return _7u(function(_1CR,_){return [0,[0,function(_1CS,_){var _1CT=B(_7i(_7s,new T(function(){return B(_1rq(_1Cu));}),_1CS,_)),_1CU=_1CT,_1CV=B(A(_6C,[_6P,_1CU,_6O,_1CD,_])),_1CW=_1CV,_1CX=B(A(_6C,[_6P,_1CU,_A3,_Dj,_])),_1CY=_1CX;return _1CU;},_Dn],_1CR];},function(_1CZ){return E(new T(function(){var _1D0=E(new T(function(){return B(_zy(_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_1Cf,_1Cg,_1Cu,new T(function(){return E(E(_1Ch)[1]);}),new T(function(){return E(E(_1Ch)[2]);})));}));if(!_1D0[0]){var _1D1=function(_1D2,_){return [0,[0,function(_1D3,_){var _1D4=B(A(new T(function(){return B(A(new T(function(){return B(_C1(_1C6,_1C7,_1C8,_1C9,_1Ca,_1Cb,_1Cc,_1Cd,_1Ce,_1Cf,_1Cg));}),[_1Ch,new T(function(){return B(_we(_1D0[1]));})]));}),[_1D3,_])),_1D5=_1D4,_1D6=B(A(_6C,[_6P,_1D5,_6O,_1CF,_])),_1D7=_1D6,_1D8=B(A(_6C,[_6P,_1D5,_A3,_Dk,_])),_1D9=_1D8;return _1D5;},_Dn],_1D2];};}else{var _1Da=E(_1D0[1]);if(!_1Da[0]){var _1Db=function(_By,_){return new F(function(){return _Ds(_1CB,_CZ,_Dp,_By,_);});};}else{var _1Db=function(_mb,_mc){return new F(function(){return _Ds(_1CB,_CZ,function(_1Dc,_){return [0,[0,function(_By,_){return new F(function(){return _7i(_6v,new T(function(){var _1Dd=E(_1Da[1]);return B(_bV(new T(function(){return B(_bI(_1Cc,_1Cb,_1Ca,_1C9,_1C8,_1C6,_1C7));}),new T(function(){return B(_3W(_1Cc,_1Cb,_1Ca,_1C9,_1C8,_1C6,_1C7));}),_1Dd[1],_1Dd[2]));}),_By,_);});},_Dn],_1Dc];},_mb,_mc);});};}var _1D1=_1Db;}return _1D1;}));},_1CQ,_);});},_1CG,_);});},_1CE,_);});},_1CC,_);});},_mb,_mc);});};},_mb,_mc);});};};},_1De=function(_1Df,_1Dg,_1Dh,_1Di){return new F(function(){return A(_1Df,[function(_){var _1Dj=jsSet(E(_1Dg)[1],toJSStr(E(_1Dh)),toJSStr(E(_1Di)));return _6B;}]);});},_1Dk=new T(function(){return B(unCStr("innerHTML"));}),_1Dl=new T(function(){return B(unCStr("textContent"));}),_1Dm=function(_1Dn,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz,_){var _1DA=B(_1j(_1Dz,_1Dl,_)),_1DB=_1DA,_1DC=[0,_1Dz],_1DD=B(A(_1De,[_6P,_1DC,_1Dk,_9,_])),_1DE=_1DD,_1DF=E(_51)[1],_1DG=takeMVar(_1DF),_1DH=_1DG,_1DI=B(A(_1C5,[_1Dn,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw,_1Dx,_1Dy,_1DB,_1DH,_])),_1DJ=_1DI,_1DK=E(_1DJ),_1DL=E(_1DK[1]),_=putMVar(_1DF,_1DK[2]),_1DM=B(A(_1DL[1],[_1DC,_])),_1DN=_1DM;return _1DL[2];},_1DO=function(_){var _1DP=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1DQ=_1DP;return _6B;},_1DR=new T(function(){return B(unCStr("embedding complete"));}),_1DS=new T(function(){return B(unCStr("proofbox"));}),_1DT=function(_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_1E2,_1E3,_1E4,_1E5,_){var _1E6=jsElemsByClassName(toJSStr(E(_1DS))),_1E7=_1E6,_1E8=B((function(_1E9,_){while(1){var _1Ea=E(_1E9);if(!_1Ea[0]){return _6B;}else{var _1Eb=B(_1Dm(_1DU,_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_1E2,_1E3,_1E4,_1E5,E(_1Ea[1])[1],_)),_1Ec=_1Eb;_1E9=_1Ea[2];continue;}}})(_1E7,_)),_1Ed=_1E8,_1Ee=jsLog(toJSStr(E(_1DR))),_1Ef=jsSetTimeout(60,_1DO);return _6B;},_1Eg=new T(function(){return B(unCStr("ADD"));}),_1Eh=new T(function(){return B(unCStr("ADJ"));}),_1Ei=[0,1],_1Ej=[1,_1Ei],_1Ek=[1,_1Ej],_1El=[0,_1Ei],_1Em=[1,_1El],_1En=new T(function(){return B(unCStr("DN"));}),_1Eo=new T(function(){return B(_3x(_9,_1En));}),_1Ep=new T(function(){return B(unCStr("MTP"));}),_1Eq=new T(function(){return B(unCStr("MT"));}),_1Er=new T(function(){return B(unCStr("MP"));}),_1Es=new T(function(){return B(unCStr("ID"));}),_1Et=new T(function(){return B(unCStr("DD"));}),_1Eu=new T(function(){return B(unCStr("CD"));}),_1Ev=[0,2],_1Ew=[1,_1Ev],_1Ex=[1,_1Ew],_1Ey=[0,_1Ev],_1Ez=[1,_1Ey],_1EA=function(_1EB){if(!B(_3x(_1EB,_1Eg))){if(!B(_3x(_1EB,_1Eh))){if(!B(_3x(_1EB,_1Eu))){if(!B(_3x(_1EB,_1Et))){if(!B(_3x(_1EB,_1Es))){if(!B(_3x(_1EB,_1Er))){if(!B(_3x(_1EB,_1Eq))){if(!B(_3x(_1EB,_1Ep))){var _1EC=E(_1EB);return _1EC[0]==0?!E(_1Eo)?[0]:E(_1Em):E(E(_1EC[1])[1])==83?E(_1EC[2])[0]==0?E(_1Em):!B(_3x(_1EC,_1En))?[0]:E(_1Em):!B(_3x(_1EC,_1En))?[0]:E(_1Em);}else{return E(_1Ez);}}else{return E(_1Ez);}}else{return E(_1Ez);}}else{return E(_1Ex);}}else{return E(_1Ek);}}else{return E(_1Ek);}}else{return E(_1Ez);}}else{return E(_1Em);}},_1ED=function(_1EE){return E(E(_1EE)[2]);},_1EF=function(_1EG,_1EH,_1EI){while(1){var _1EJ=E(_1EH);if(!_1EJ[0]){return E(_1EI)[0]==0?1:0;}else{var _1EK=E(_1EI);if(!_1EK[0]){return 2;}else{var _1EL=B(A(_1ED,[_1EG,_1EJ[1],_1EK[1]]));if(_1EL==1){_1EH=_1EJ[2];_1EI=_1EK[2];continue;}else{return E(_1EL);}}}}},_1EM=function(_1EN){return E(E(_1EN)[3]);},_1EO=function(_1EP,_1EQ,_1ER,_1ES,_1ET){switch(B(_1EF(_1EP,_1EQ,_1ES))){case 0:return true;case 1:return new F(function(){return A(_1EM,[_1EP,_1ER,_1ET]);});break;default:return false;}},_1EU=function(_1EV,_1EW,_1EX,_1EY){var _1EZ=E(_1EX),_1F0=E(_1EY);return new F(function(){return _1EO(_1EW,_1EZ[1],_1EZ[2],_1F0[1],_1F0[2]);});},_1F1=function(_1F2){return E(E(_1F2)[6]);},_1F3=function(_1F4,_1F5,_1F6,_1F7,_1F8){switch(B(_1EF(_1F4,_1F5,_1F7))){case 0:return true;case 1:return new F(function(){return A(_1F1,[_1F4,_1F6,_1F8]);});break;default:return false;}},_1F9=function(_1Fa,_1Fb,_1Fc,_1Fd){var _1Fe=E(_1Fc),_1Ff=E(_1Fd);return new F(function(){return _1F3(_1Fb,_1Fe[1],_1Fe[2],_1Ff[1],_1Ff[2]);});},_1Fg=function(_1Fh){return E(E(_1Fh)[5]);},_1Fi=function(_1Fj,_1Fk,_1Fl,_1Fm,_1Fn){switch(B(_1EF(_1Fj,_1Fk,_1Fm))){case 0:return false;case 1:return new F(function(){return A(_1Fg,[_1Fj,_1Fl,_1Fn]);});break;default:return true;}},_1Fo=function(_1Fp,_1Fq,_1Fr,_1Fs){var _1Ft=E(_1Fr),_1Fu=E(_1Fs);return new F(function(){return _1Fi(_1Fq,_1Ft[1],_1Ft[2],_1Fu[1],_1Fu[2]);});},_1Fv=function(_1Fw){return E(E(_1Fw)[4]);},_1Fx=function(_1Fy,_1Fz,_1FA,_1FB,_1FC){switch(B(_1EF(_1Fy,_1Fz,_1FB))){case 0:return false;case 1:return new F(function(){return A(_1Fv,[_1Fy,_1FA,_1FC]);});break;default:return true;}},_1FD=function(_1FE,_1FF,_1FG,_1FH){var _1FI=E(_1FG),_1FJ=E(_1FH);return new F(function(){return _1Fx(_1FF,_1FI[1],_1FI[2],_1FJ[1],_1FJ[2]);});},_1FK=function(_1FL,_1FM,_1FN,_1FO,_1FP){switch(B(_1EF(_1FL,_1FM,_1FO))){case 0:return 0;case 1:return new F(function(){return A(_1ED,[_1FL,_1FN,_1FP]);});break;default:return 2;}},_1FQ=function(_1FR,_1FS,_1FT,_1FU){var _1FV=E(_1FT),_1FW=E(_1FU);return new F(function(){return _1FK(_1FS,_1FV[1],_1FV[2],_1FW[1],_1FW[2]);});},_1FX=function(_1FY,_1FZ,_1G0,_1G1){var _1G2=E(_1G0),_1G3=_1G2[1],_1G4=_1G2[2],_1G5=E(_1G1),_1G6=_1G5[1],_1G7=_1G5[2];switch(B(_1EF(_1FZ,_1G3,_1G6))){case 0:return [0,_1G6,_1G7];case 1:return !B(A(_1F1,[_1FZ,_1G4,_1G7]))?[0,_1G3,_1G4]:[0,_1G6,_1G7];default:return [0,_1G3,_1G4];}},_1G8=function(_1G9,_1Ga,_1Gb,_1Gc){var _1Gd=E(_1Gb),_1Ge=_1Gd[1],_1Gf=_1Gd[2],_1Gg=E(_1Gc),_1Gh=_1Gg[1],_1Gi=_1Gg[2];switch(B(_1EF(_1Ga,_1Ge,_1Gh))){case 0:return [0,_1Ge,_1Gf];case 1:return !B(A(_1F1,[_1Ga,_1Gf,_1Gi]))?[0,_1Gh,_1Gi]:[0,_1Ge,_1Gf];default:return [0,_1Gh,_1Gi];}},_1Gj=function(_1Gk,_1Gl){return [0,_1Gk,function(_cr,_cs){return new F(function(){return _1FQ(_1Gk,_1Gl,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1EU(_1Gk,_1Gl,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1FD(_1Gk,_1Gl,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Fo(_1Gk,_1Gl,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1F9(_1Gk,_1Gl,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1FX(_1Gk,_1Gl,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1G8(_1Gk,_1Gl,_cr,_cs);});}];},_1Gm=function(_1Gn,_1Go,_1Gp,_1Gq){return !B(A(_1Gn,[_1Gp,_1Gq]))?B(_DZ(B(A(_1Go,[_1Gp,_jf])),B(A(_1Go,[_1Gq,_jf]))))==2?false:true:false;},_1Gr=function(_1Gs,_1Gt,_1Gu,_1Gv){return new F(function(){return _1Gm(E(_1Gs)[1],_1Gt,_1Gu,_1Gv);});},_1Gw=function(_1Gx,_1Gy,_1Gz,_1GA){return B(_DZ(B(A(_1Gy,[_1Gz,_jf])),B(A(_1Gy,[_1GA,_jf]))))==2?false:true;},_1GB=function(_1GC,_1GD,_1GE,_1GF){return !B(A(_1GC,[_1GE,_1GF]))?B(_DZ(B(A(_1GD,[_1GE,_jf])),B(A(_1GD,[_1GF,_jf]))))==2?true:false:false;},_1GG=function(_1GH,_1GI,_1GJ,_1GK){return new F(function(){return _1GB(E(_1GH)[1],_1GI,_1GJ,_1GK);});},_1GL=function(_1GM,_1GN,_1GO,_1GP){return !B(A(_1GM,[_1GO,_1GP]))?B(_DZ(B(A(_1GN,[_1GO,_jf])),B(A(_1GN,[_1GP,_jf]))))==2?true:false:true;},_1GQ=function(_1GR,_1GS,_1GT,_1GU){return new F(function(){return _1GL(E(_1GR)[1],_1GS,_1GT,_1GU);});},_1GV=function(_1GW,_1GX,_1GY,_1GZ){return !B(A(_1GW,[_1GY,_1GZ]))?B(_DZ(B(A(_1GX,[_1GY,_jf])),B(A(_1GX,[_1GZ,_jf]))))==2?2:0:1;},_1H0=function(_1H1,_1H2,_1H3,_1H4){return new F(function(){return _1GV(E(_1H1)[1],_1H2,_1H3,_1H4);});},_1H5=function(_1H6,_1H7,_1H8,_1H9){return B(_DZ(B(A(_1H7,[_1H8,_jf])),B(A(_1H7,[_1H9,_jf]))))==2?E(_1H8):E(_1H9);},_1Ha=function(_1Hb,_1Hc,_1Hd,_1He){return B(_DZ(B(A(_1Hc,[_1Hd,_jf])),B(A(_1Hc,[_1He,_jf]))))==2?E(_1He):E(_1Hd);},_1Hf=function(_1Hg,_1Hh){return [0,_1Hg,function(_44,_45){return new F(function(){return _1H0(_1Hg,_1Hh,_44,_45);});},function(_44,_45){return new F(function(){return _1Gr(_1Hg,_1Hh,_44,_45);});},function(_44,_45){return new F(function(){return _1GQ(_1Hg,_1Hh,_44,_45);});},function(_44,_45){return new F(function(){return _1GG(_1Hg,_1Hh,_44,_45);});},function(_44,_45){return new F(function(){return _1Gw(_1Hg,_1Hh,_44,_45);});},function(_44,_45){return new F(function(){return _1H5(_1Hg,_1Hh,_44,_45);});},function(_44,_45){return new F(function(){return _1Ha(_1Hg,_1Hh,_44,_45);});}];},_1Hi=function(_1Hj,_1Hk,_1Hl,_1Hm,_1Hn,_1Ho,_1Hp){var _1Hq=function(_1Hr,_1Hs){return new F(function(){return _2W(_1Hj,_1Hk,_1Hl,_1Hn,_1Hm,_1Hp,_1Ho,_1Hr);});};return function(_1Ht,_1Hu){var _1Hv=E(_1Ht);if(!_1Hv[0]){var _1Hw=E(_1Hu);return _1Hw[0]==0?B(_DZ(B(_1r(_1Hv[1])),B(_1r(_1Hw[1]))))==2?false:true:true;}else{var _1Hx=E(_1Hu);return _1Hx[0]==0?false:B(_1EF(new T(function(){return B(_1Hf(new T(function(){return B(_jk(_1Hq));}),_1Hq));}),_1Hv[1],_1Hx[1]))==2?false:true;}};},_1Hy=function(_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HH,_1HI){return !B(A(_1Hi,[_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_1HG,_1HH,_1HI]))?E(_1HH):E(_1HI);},_1HJ=function(_1HK,_1HL,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1HS,_1HT){return !B(A(_1Hi,[_1HL,_1HM,_1HN,_1HO,_1HP,_1HQ,_1HR,_1HS,_1HT]))?E(_1HT):E(_1HS);},_1HU=function(_1HV,_1HW,_1HX,_1HY,_1HZ,_1I0,_1I1){var _1I2=function(_1I3,_1I4){return new F(function(){return _2W(_1HV,_1HW,_1HX,_1HZ,_1HY,_1I1,_1I0,_1I3);});};return function(_1I5,_1I6){var _1I7=E(_1I5);if(!_1I7[0]){var _1I8=_1I7[1],_1I9=E(_1I6);if(!_1I9[0]){var _1Ia=_1I9[1];return B(_cH(_1I8,_1Ia,_1))[0]==0?B(_DZ(B(_1r(_1I8)),B(_1r(_1Ia))))==2?false:true:false;}else{return true;}}else{var _1Ib=E(_1I6);return _1Ib[0]==0?false:B(_1EF(new T(function(){return B(_1Hf(new T(function(){return B(_jk(_1I2));}),_1I2));}),_1I7[1],_1Ib[1]))==0?true:false;}};},_1Ic=function(_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij){var _1Ik=function(_1Il,_1Im){return new F(function(){return _2W(_1Id,_1Ie,_1If,_1Ih,_1Ig,_1Ij,_1Ii,_1Il);});};return function(_1In,_1Io){var _1Ip=E(_1In);if(!_1Ip[0]){var _1Iq=_1Ip[1],_1Ir=E(_1Io);if(!_1Ir[0]){var _1Is=_1Ir[1];return B(_cH(_1Iq,_1Is,_1))[0]==0?B(_DZ(B(_1r(_1Iq)),B(_1r(_1Is))))==2?true:false:false;}else{return false;}}else{var _1It=E(_1Io);return _1It[0]==0?true:B(_1EF(new T(function(){return B(_1Hf(new T(function(){return B(_jk(_1Ik));}),_1Ik));}),_1Ip[1],_1It[1]))==2?true:false;}};},_1Iu=function(_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB){var _1IC=function(_1ID,_1IE){return new F(function(){return _2W(_1Iv,_1Iw,_1Ix,_1Iz,_1Iy,_1IB,_1IA,_1ID);});};return function(_1IF,_1IG){var _1IH=E(_1IF);if(!_1IH[0]){var _1II=_1IH[1],_1IJ=E(_1IG);if(!_1IJ[0]){var _1IK=_1IJ[1];return B(_cH(_1II,_1IK,_1))[0]==0?B(_DZ(B(_1r(_1II)),B(_1r(_1IK))))==2?true:false:true;}else{return false;}}else{var _1IL=E(_1IG);return _1IL[0]==0?true:B(_1EF(new T(function(){return B(_1Hf(new T(function(){return B(_jk(_1IC));}),_1IC));}),_1IH[1],_1IL[1]))==0?false:true;}};},_1IM=function(_1IN,_1IO,_1IP,_1IQ,_1IR,_1IS,_1IT){var _1IU=function(_1IV,_1IW){return new F(function(){return _2W(_1IN,_1IO,_1IP,_1IR,_1IQ,_1IT,_1IS,_1IV);});};return function(_1IX,_1IY){var _1IZ=E(_1IX);if(!_1IZ[0]){var _1J0=_1IZ[1],_1J1=E(_1IY);if(!_1J1[0]){var _1J2=_1J1[1];return B(_cH(_1J0,_1J2,_1))[0]==0?B(_DZ(B(_1r(_1J0)),B(_1r(_1J2))))==2?2:0:1;}else{return 0;}}else{var _1J3=E(_1IY);return _1J3[0]==0?2:B(_1EF(new T(function(){return B(_1Hf(new T(function(){return B(_jk(_1IU));}),_1IU));}),_1IZ[1],_1J3[1]));}};},_1J4=function(_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc){return [0,_1J5,new T(function(){return B(_1IM(_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc));}),new T(function(){return B(_1HU(_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc));}),new T(function(){return B(_1Iu(_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc));}),new T(function(){return B(_1Ic(_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc));}),new T(function(){return B(_1Hi(_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc));}),function(_44,_45){return new F(function(){return _1Hy(_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_44,_45);});},function(_44,_45){return new F(function(){return _1HJ(_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_44,_45);});}];},_1Jd=new T(function(){return B(_3W(_Q,_u,_Q,_Q,_N,_2,_15));}),_1Je=new T(function(){return B(_1J4(_1Jd,_Q,_u,_Q,_Q,_N,_15,_2));}),_1Jf=new T(function(){return B(_cF(_1Jd));}),_1Jg=new T(function(){return B(_1Gj(_1Jf,_1Je));}),_1Jh=function(_1Ji,_1Jj,_1Jk,_1Jl){var _1Jm=E(_1Jk),_1Jn=E(_1Jl);return new F(function(){return _1EO(_1Jj,_1Jm[1],_1Jm[2],_1Jn[1],_1Jn[2]);});},_1Jo=function(_1Jp,_1Jq,_1Jr,_1Js){var _1Jt=E(_1Jr),_1Ju=E(_1Js);return new F(function(){return _1F3(_1Jq,_1Jt[1],_1Jt[2],_1Ju[1],_1Ju[2]);});},_1Jv=function(_1Jw,_1Jx,_1Jy,_1Jz){var _1JA=E(_1Jy),_1JB=E(_1Jz);return new F(function(){return _1Fi(_1Jx,_1JA[1],_1JA[2],_1JB[1],_1JB[2]);});},_1JC=function(_1JD,_1JE,_1JF,_1JG){var _1JH=E(_1JF),_1JI=E(_1JG);return new F(function(){return _1Fx(_1JE,_1JH[1],_1JH[2],_1JI[1],_1JI[2]);});},_1JJ=function(_1JK,_1JL,_1JM,_1JN){var _1JO=E(_1JM),_1JP=E(_1JN);return new F(function(){return _1FK(_1JL,_1JO[1],_1JO[2],_1JP[1],_1JP[2]);});},_1JQ=function(_1JR,_1JS,_1JT,_1JU){var _1JV=E(_1JT),_1JW=_1JV[1],_1JX=_1JV[2],_1JY=E(_1JU),_1JZ=_1JY[1],_1K0=_1JY[2];switch(B(_1EF(_1JS,_1JW,_1JZ))){case 0:return [0,_1JZ,_1K0];case 1:return !B(A(_1F1,[_1JS,_1JX,_1K0]))?[0,_1JW,_1JX]:[0,_1JZ,_1K0];default:return [0,_1JW,_1JX];}},_1K1=function(_1K2,_1K3,_1K4,_1K5){var _1K6=E(_1K4),_1K7=_1K6[1],_1K8=_1K6[2],_1K9=E(_1K5),_1Ka=_1K9[1],_1Kb=_1K9[2];switch(B(_1EF(_1K3,_1K7,_1Ka))){case 0:return [0,_1K7,_1K8];case 1:return !B(A(_1F1,[_1K3,_1K8,_1Kb]))?[0,_1Ka,_1Kb]:[0,_1K7,_1K8];default:return [0,_1Ka,_1Kb];}},_1Kc=function(_1Kd,_1Ke){return [0,_1Kd,function(_cr,_cs){return new F(function(){return _1JJ(_1Kd,_1Ke,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Jh(_1Kd,_1Ke,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1JC(_1Kd,_1Ke,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Jv(_1Kd,_1Ke,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Jo(_1Kd,_1Ke,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1JQ(_1Kd,_1Ke,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1K1(_1Kd,_1Ke,_cr,_cs);});}];},_1Kf=function(_1Kg,_1Kh){return B(_DZ(_1Kg,_1Kh))==0?false:true;},_1Ki=function(_1Kj){return E(E(_1Kj)[1]);},_1Kk=function(_1Kl){return function(_1Km,_1Kn){var _1Ko=E(_1Km),_1Kp=E(_1Kn);switch(B(_1EF(new T(function(){return B(_1Kc(new T(function(){return B(_cp(new T(function(){return B(_1Ki(_1Kl));})));}),_1Kl));}),_1Ko[1],_1Kp[1]))){case 0:return false;case 1:return new F(function(){return _1Kf(_1Ko[2],_1Kp[2]);});break;default:return true;}};},_1Kq=new T(function(){return B(_1Kk(_1Jg));}),_1Kr=function(_1Ks,_1Kt){return B(_DZ(_1Ks,_1Kt))==2?false:true;},_1Ku=function(_1Kv){return function(_1Kw,_1Kx){var _1Ky=E(_1Kw),_1Kz=E(_1Kx);switch(B(_1EF(new T(function(){return B(_1Kc(new T(function(){return B(_cp(new T(function(){return B(_1Ki(_1Kv));})));}),_1Kv));}),_1Ky[1],_1Kz[1]))){case 0:return true;case 1:return new F(function(){return _1Kr(_1Ky[2],_1Kz[2]);});break;default:return false;}};},_1KA=function(_1KB,_1KC,_1KD,_1KE){return !B(A(_1Ku,[_1KC,_1KD,_1KE]))?E(_1KD):E(_1KE);},_1KF=function(_1KG,_1KH,_1KI,_1KJ){return !B(A(_1Ku,[_1KH,_1KI,_1KJ]))?E(_1KJ):E(_1KI);},_1KK=function(_1KL,_1KM){return B(_DZ(_1KL,_1KM))==0?true:false;},_1KN=function(_1KO){return function(_1KP,_1KQ){var _1KR=E(_1KP),_1KS=E(_1KQ);switch(B(_1EF(new T(function(){return B(_1Kc(new T(function(){return B(_cp(new T(function(){return B(_1Ki(_1KO));})));}),_1KO));}),_1KR[1],_1KS[1]))){case 0:return true;case 1:return new F(function(){return _1KK(_1KR[2],_1KS[2]);});break;default:return false;}};},_1KT=function(_1KU,_1KV){return B(_DZ(_1KU,_1KV))==2?true:false;},_1KW=function(_1KX){return function(_1KY,_1KZ){var _1L0=E(_1KY),_1L1=E(_1KZ);switch(B(_1EF(new T(function(){return B(_1Kc(new T(function(){return B(_cp(new T(function(){return B(_1Ki(_1KX));})));}),_1KX));}),_1L0[1],_1L1[1]))){case 0:return false;case 1:return new F(function(){return _1KT(_1L0[2],_1L1[2]);});break;default:return true;}};},_1L2=function(_1L3){return function(_1L4,_1L5){var _1L6=E(_1L4),_1L7=E(_1L5);switch(B(_1EF(new T(function(){return B(_1Kc(new T(function(){return B(_cp(new T(function(){return B(_1Ki(_1L3));})));}),_1L3));}),_1L6[1],_1L7[1]))){case 0:return 0;case 1:return new F(function(){return _DZ(_1L6[2],_1L7[2]);});break;default:return 2;}};},_1L8=function(_1L9,_1La){return [0,_1L9,new T(function(){return B(_1L2(_1La));}),new T(function(){return B(_1KN(_1La));}),new T(function(){return B(_1Kk(_1La));}),new T(function(){return B(_1KW(_1La));}),new T(function(){return B(_1Ku(_1La));}),function(_cr,_cs){return new F(function(){return _1KA(_1L9,_1La,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1KF(_1L9,_1La,_cr,_cs);});}];},_1Lb=function(_1Lc,_1Ld,_1Le,_1Lf,_1Lg){return !B(_c1(new T(function(){return B(_cp(_1Lc));}),_1Ld,_1Lf))?true:!B(_3x(_1Le,_1Lg))?true:false;},_1Lh=function(_1Li,_1Lj,_1Lk){var _1Ll=E(_1Lj),_1Lm=E(_1Lk);return new F(function(){return _1Lb(_1Li,_1Ll[1],_1Ll[2],_1Lm[1],_1Lm[2]);});},_1Ln=function(_1Lo){return function(_1Lp,_1Lq){var _1Lr=E(_1Lp),_1Ls=E(_1Lq);return !B(_c1(new T(function(){return B(_cp(_1Lo));}),_1Lr[1],_1Ls[1]))?false:B(_3x(_1Lr[2],_1Ls[2]));};},_1Lt=function(_1Lu){return [0,new T(function(){return B(_1Ln(_1Lu));}),function(_cr,_cs){return new F(function(){return _1Lh(_1Lu,_cr,_cs);});}];},_1Lv=new T(function(){return B(_1Lt(_1Jf));}),_1Lw=new T(function(){return B(_1L8(_1Lv,_1Jg));}),_1Lx=function(_1Ly,_1Lz,_1LA){var _1LB=E(_1Lz),_1LC=E(_1LA);if(!_1LC[0]){var _1LD=_1LC[2],_1LE=_1LC[3],_1LF=_1LC[4];switch(B(A(_1ED,[_1Ly,_1LB,_1LD]))){case 0:return new F(function(){return _ri(_1LD,B(_1Lx(_1Ly,_1LB,_1LE)),_1LF);});break;case 1:return [0,_1LC[1],E(_1LB),E(_1LE),E(_1LF)];default:return new F(function(){return _rU(_1LD,_1LE,B(_1Lx(_1Ly,_1LB,_1LF)));});}}else{return [0,1,E(_1LB),E(_rd),E(_rd)];}},_1LG=function(_1LH,_1LI){while(1){var _1LJ=E(_1LI);if(!_1LJ[0]){return E(_1LH);}else{var _1LK=B(_1Lx(_1Lw,_1LJ[1],_1LH));_1LI=_1LJ[2];_1LH=_1LK;continue;}}},_1LL=function(_1LM,_1LN){var _1LO=E(_1LN);if(!_1LO[0]){return [0,_rd,_9,_9];}else{var _1LP=_1LO[1],_1LQ=E(_1LM);if(_1LQ==1){var _1LR=E(_1LO[2]);return _1LR[0]==0?[0,new T(function(){return [0,1,E(E(_1LP)),E(_rd),E(_rd)];}),_9,_9]:!B(A(_1Kq,[_1LP,_1LR[1]]))?[0,new T(function(){return [0,1,E(E(_1LP)),E(_rd),E(_rd)];}),_1LR,_9]:[0,new T(function(){return [0,1,E(E(_1LP)),E(_rd),E(_rd)];}),_9,_1LR];}else{var _1LS=B(_1LL(_1LQ>>1,_1LO)),_1LT=_1LS[1],_1LU=_1LS[3],_1LV=E(_1LS[2]);if(!_1LV[0]){return [0,_1LT,_9,_1LU];}else{var _1LW=_1LV[1],_1LX=E(_1LV[2]);if(!_1LX[0]){return [0,new T(function(){return B(_sA(_1LW,_1LT));}),_9,_1LU];}else{if(!B(A(_1Kq,[_1LW,_1LX[1]]))){var _1LY=B(_1LL(_1LQ>>1,_1LX));return [0,new T(function(){return B(_te(_1LW,_1LT,_1LY[1]));}),_1LY[2],_1LY[3]];}else{return [0,_1LT,_9,_1LV];}}}}}},_1LZ=function(_1M0,_1M1,_1M2){while(1){var _1M3=E(_1M2);if(!_1M3[0]){return E(_1M1);}else{var _1M4=_1M3[1],_1M5=E(_1M3[2]);if(!_1M5[0]){return new F(function(){return _sA(_1M4,_1M1);});}else{if(!B(A(_1Kq,[_1M4,_1M5[1]]))){var _1M6=B(_1LL(_1M0,_1M5)),_1M7=_1M6[1],_1M8=E(_1M6[3]);if(!_1M8[0]){var _1M9=_1M0<<1,_1Ma=B(_te(_1M4,_1M1,_1M7));_1M2=_1M6[2];_1M0=_1M9;_1M1=_1Ma;continue;}else{return new F(function(){return _1LG(B(_te(_1M4,_1M1,_1M7)),_1M8);});}}else{return new F(function(){return _1LG(_1M1,_1M3);});}}}}},_1Mb=function(_1Mc){var _1Md=E(_1Mc);if(!_1Md[0]){return [1];}else{var _1Me=_1Md[1],_1Mf=E(_1Md[2]);if(!_1Mf[0]){return [0,1,E(E(_1Me)),E(_rd),E(_rd)];}else{if(!B(A(_1Kq,[_1Me,_1Mf[1]]))){return new F(function(){return _1LZ(1,[0,1,E(E(_1Me)),E(_rd),E(_rd)],_1Mf);});}else{return new F(function(){return _1LG([0,1,E(E(_1Me)),E(_rd),E(_rd)],_1Mf);});}}}},_1Mg=new T(function(){return B(_F(0,1,_9));}),_1Mh=new T(function(){return B(unCStr("\u0394_"));}),_1Mi=new T(function(){return B(_e(_1Mh,_1Mg));}),_1Mj=[9,_,_,_1Mi],_1Mk=[0,_1Mj],_1Ml=[1,_1Mk,_9],_1Mm=new T(function(){return B(unCStr("\u03c6_"));}),_1Mn=new T(function(){return B(_e(_1Mm,_1Mg));}),_1Mo=[3,_,_,_1Mn],_1Mp=[2,_,_1Mo],_1Mq=[1,_1Mp,_9],_1Mr=[1,_1Mq],_1Ms=[0,_1Ml,_1Mr],_1Mt=new T(function(){return B(_F(0,2,_9));}),_1Mu=new T(function(){return B(_e(_1Mm,_1Mt));}),_1Mv=[3,_,_,_1Mu],_1Mw=[2,_,_1Mv],_1Mx=[1,_1Mw,_9],_1My=[1,_1Mx],_1Mz=new T(function(){return B(_e(_1Mh,_1Mt));}),_1MA=[9,_,_,_1Mz],_1MB=[0,_1MA],_1MC=[1,_1MB,_9],_1MD=[0,_1MC,_1My],_1ME=[1,_1MD,_9],_1MF=[1,_1Ms,_1ME],_1MG=function(_1MH,_1MI){var _1MJ=E(_1MH);if(!_1MJ[0]){return [0];}else{var _1MK=_1MJ[1],_1ML=_1MJ[2],_1MM=function(_1MN,_1MO,_1MP){var _1MQ=E(_1MO);if(!_1MQ[0]){return [0,_1ML,_1MP];}else{var _1MR=_1MQ[1],_1MS=new T(function(){var _1MT=B(_1MM(function(_1MU){return new F(function(){return A(_1MN,[[1,_1MR,_1MU]]);});},_1MQ[2],_1MP));return [0,_1MT[1],_1MT[2]];}),_1MV=new T(function(){return E(E(_1MS)[1]);});return [0,[1,_1MR,_1MV],[1,new T(function(){return B(A(_1MN,[[1,_1MK,[1,_1MR,_1MV]]]));}),new T(function(){return E(E(_1MS)[2]);})]];}},_1MW=function(_1MX){var _1MY=E(_1MX);return _1MY[0]==0?E(new T(function(){return B(_1MG(_1ML,[1,_1MK,_1MI]));})):E(B(_1MM(_6P,_1MY[1],new T(function(){return B(_1MW(_1MY[2]));})))[2]);};return new F(function(){return _1MW([1,_1MI,new T(function(){return B(_1MG(_1MI,_9));})]);});}},_1MZ=new T(function(){return B(_1MG(_1MF,_9));}),_1N0=[1,_1MF,_1MZ],_1N1=[9,_,_1fN,_1Mp,_1Mw],_1N2=[1,_1N1,_9],_1N3=[1,_1N2],_1N4=[1,_1Mk,_1MC],_1N5=[0,_1N4,_1N3],_1N6=function(_1N7){return [0,_1N7,_1N5];},_1N8=new T(function(){return B(_3d(_1N6,_1N0));}),_1N9=[0,_1N8,_1Eh],_1Na=[1,_1Ms,_9],_1Nb=[9,_,_1fp,_1Mp,_1Mw],_1Nc=[1,_1Nb,_9],_1Nd=[1,_1Nc],_1Ne=[0,_1Ml,_1Nd],_1Nf=[0,_1Na,_1Ne],_1Ng=[9,_,_1fp,_1Mw,_1Mp],_1Nh=[1,_1Ng,_9],_1Ni=[1,_1Nh],_1Nj=[0,_1Ml,_1Ni],_1Nk=[0,_1Na,_1Nj],_1Nl=[1,_1Nk,_9],_1Nm=[1,_1Nf,_1Nl],_1Nn=[0,_1Nm,_1Eg],_1No=[0,_1Na,_1Ms],_1Np=[1,_1No,_9],_1Nq=[0,_1Np,_1Et],_1Nr=[1,_1Nq,_9],_1Ns=[1,_1Mr,_1Ml],_1Nt=[0,_1Ns,_1My],_1Nu=[1,_1Mr,_1MC],_1Nv=[7,_,_1ge,_1Mw],_1Nw=[1,_1Nv,_9],_1Nx=[1,_1Nw],_1Ny=[0,_1Nu,_1Nx],_1Nz=[1,_1Ny,_9],_1NA=[1,_1Nt,_1Nz],_1NB=new T(function(){return B(_1MG(_1NA,_9));}),_1NC=[1,_1NA,_1NB],_1ND=[7,_,_1ge,_1Mp],_1NE=[1,_1ND,_9],_1NF=[1,_1NE],_1NG=[0,_1N4,_1NF],_1NH=[0,_1N4,_1Mr],_1NI=function(_1NJ){return [0,_1NJ,_1NH];},_1NK=[0,_1Ml,_1My],_1NL=[1,_1NK,_9],_1NM=[0,_1MC,_1Nx],_1NN=[1,_1NM,_1NL],_1NO=new T(function(){return B(_1MG(_1NN,_9));}),_1NP=[1,_1NN,_1NO],_1NQ=new T(function(){return B(_3d(_1NI,_1NP));}),_1NR=function(_1NS){var _1NT=E(_1NS);return _1NT[0]==0?E(_1NQ):[1,[0,_1NT[1],_1NH],new T(function(){return B(_1NR(_1NT[2]));})];},_1NU=[1,_1NF,_1MC],_1NV=[0,_1NU,_1Nx],_1NW=[1,_1NV,_1NL],_1NX=new T(function(){return B(_1MG(_1NW,_9));}),_1NY=[1,_1NW,_1NX],_1NZ=new T(function(){return B(_1NR(_1NY));}),_1O0=function(_1O1){var _1O2=E(_1O1);return _1O2[0]==0?E(_1NZ):[1,[0,_1O2[1],_1NH],new T(function(){return B(_1O0(_1O2[2]));})];},_1O3=[1,_1NF,_1Ml],_1O4=[0,_1O3,_1My],_1O5=[1,_1O4,_9],_1O6=[1,_1NM,_1O5],_1O7=new T(function(){return B(_1MG(_1O6,_9));}),_1O8=[1,_1O6,_1O7],_1O9=new T(function(){return B(_1O0(_1O8));}),_1Oa=function(_1Ob){var _1Oc=E(_1Ob);return _1Oc[0]==0?E(_1O9):[1,[0,_1Oc[1],_1NH],new T(function(){return B(_1Oa(_1Oc[2]));})];},_1Od=[1,_1NV,_1O5],_1Oe=new T(function(){return B(_1MG(_1Od,_9));}),_1Of=[1,_1Od,_1Oe],_1Og=new T(function(){return B(_1Oa(_1Of));}),_1Oh=function(_1Oi){var _1Oj=E(_1Oi);return _1Oj[0]==0?E(_1Og):[1,[0,_1Oj[1],_1NG],new T(function(){return B(_1Oh(_1Oj[2]));})];},_1Ok=[1,_1NM,_9],_1Ol=[1,_1NK,_1Ok],_1Om=new T(function(){return B(_1MG(_1Ol,_9));}),_1On=[1,_1Ol,_1Om],_1Oo=new T(function(){return B(_1Oh(_1On));}),_1Op=function(_1Oq){var _1Or=E(_1Oq);return _1Or[0]==0?E(_1Oo):[1,[0,_1Or[1],_1NG],new T(function(){return B(_1Op(_1Or[2]));})];},_1Os=[1,_1Nt,_1Ok],_1Ot=new T(function(){return B(_1MG(_1Os,_9));}),_1Ou=[1,_1Os,_1Ot],_1Ov=new T(function(){return B(_1Op(_1Ou));}),_1Ow=function(_1Ox){var _1Oy=E(_1Ox);return _1Oy[0]==0?E(_1Ov):[1,[0,_1Oy[1],_1NG],new T(function(){return B(_1Ow(_1Oy[2]));})];},_1Oz=[1,_1NK,_1Nz],_1OA=new T(function(){return B(_1MG(_1Oz,_9));}),_1OB=[1,_1Oz,_1OA],_1OC=new T(function(){return B(_1Ow(_1OB));}),_1OD=function(_1OE){var _1OF=E(_1OE);return _1OF[0]==0?E(_1OC):[1,[0,_1OF[1],_1NG],new T(function(){return B(_1OD(_1OF[2]));})];},_1OG=new T(function(){return B(_1OD(_1NC));}),_1OH=[0,_1OG,_1Es],_1OI=[1,_1OH,_1Nr],_1OJ=[1,_1Nn,_1OI],_1OK=[0,83],_1OL=[1,_1OK,_9],_1OM=[0,_1Ml,_1N3],_1ON=[1,_1OM,_9],_1OO=[0,_1ON,_1Ms],_1OP=[0,_1ON,_1NK],_1OQ=[1,_1OP,_9],_1OR=[1,_1OO,_1OQ],_1OS=[0,_1OR,_1OL],_1OT=[1,_1OS,_1OJ],_1OU=[1,_1Nj,_1Ok],_1OV=new T(function(){return B(_1MG(_1OU,_9));}),_1OW=[1,_1OU,_1OV],_1OX=[0,_1MC,_1NF],_1OY=[1,_1OX,_9],_1OZ=[1,_1Nj,_1OY],_1P0=new T(function(){return B(_1MG(_1OZ,_9));}),_1P1=[1,_1OZ,_1P0],_1P2=[0,_1N4,_1My],_1P3=function(_1P4){return [0,_1P4,_1P2];},_1P5=new T(function(){return B(_3d(_1P3,_1P1));}),_1P6=function(_1P7){var _1P8=E(_1P7);return _1P8[0]==0?E(_1P5):[1,[0,_1P8[1],_1NH],new T(function(){return B(_1P6(_1P8[2]));})];},_1P9=new T(function(){return B(_1P6(_1OW));}),_1Pa=[0,_1P9,_1Ep],_1Pb=[1,_1Pa,_1OT],_1Pc=function(_1Pd){return [0,_1Pd,_1NG];},_1Pe=[0,_1Ml,_1Nx],_1Pf=[9,_,_1ed,_1Mp,_1Mw],_1Pg=[1,_1Pf,_9],_1Ph=[1,_1Pg],_1Pi=[0,_1MC,_1Ph],_1Pj=[1,_1Pi,_9],_1Pk=[1,_1Pe,_1Pj],_1Pl=new T(function(){return B(_1MG(_1Pk,_9));}),_1Pm=[1,_1Pk,_1Pl],_1Pn=new T(function(){return B(_3d(_1Pc,_1Pm));}),_1Po=[0,_1Pn,_1Eq],_1Pp=[1,_1Po,_1Pb],_1Pq=[1,_1Ms,_1Pj],_1Pr=new T(function(){return B(_1MG(_1Pq,_9));}),_1Ps=[1,_1Pq,_1Pr],_1Pt=new T(function(){return B(_3d(_1P3,_1Ps));}),_1Pu=[0,_1Pt,_1Er],_1Pv=[1,_1Pu,_1Pp],_1Pw=[0,_1Ml,_1Ph],_1Px=[1,_1Nt,_9],_1Py=[0,_1Px,_1Pw],_1Pz=[0,_1NL,_1Pw],_1PA=[1,_1Pz,_9],_1PB=[1,_1Py,_1PA],_1PC=[0,_1PB,_1Eu],_1PD=[1,_1PC,_1Pv],_1PE=[1,_1N9,_1PD],_1PF=new T(function(){return B(_1Mb(_1PE));}),_1PG=[0,_1EA,_1PF],_1PH=function(_){return new F(function(){return _1DT(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1PG,_);});},_1PI=function(_){return new F(function(){return _1PH(_);});};
var hasteMain = function() {B(A(_1PI, [0]));};window.onload = hasteMain;