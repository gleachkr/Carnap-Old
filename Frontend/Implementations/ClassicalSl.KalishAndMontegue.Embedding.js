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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr("wheel"));}),_1r=new T(function(){return B(unCStr("mouseout"));}),_1s=new T(function(){return B(unCStr("mouseover"));}),_1t=new T(function(){return B(unCStr("mousemove"));}),_1u=new T(function(){return B(unCStr("blur"));}),_1v=new T(function(){return B(unCStr("focus"));}),_1w=new T(function(){return B(unCStr("change"));}),_1x=new T(function(){return B(unCStr("unload"));}),_1y=new T(function(){return B(unCStr("load"));}),_1z=new T(function(){return B(unCStr("submit"));}),_1A=new T(function(){return B(unCStr("keydown"));}),_1B=new T(function(){return B(unCStr("keyup"));}),_1C=new T(function(){return B(unCStr("keypress"));}),_1D=new T(function(){return B(unCStr("mouseup"));}),_1E=new T(function(){return B(unCStr("mousedown"));}),_1F=new T(function(){return B(unCStr("dblclick"));}),_1G=new T(function(){return B(unCStr("click"));}),_1H=function(_1I){switch(E(_1I)[0]){case 0:return E(_1y);case 1:return E(_1x);case 2:return E(_1w);case 3:return E(_1v);case 4:return E(_1u);case 5:return E(_1t);case 6:return E(_1s);case 7:return E(_1r);case 8:return E(_1G);case 9:return E(_1F);case 10:return E(_1E);case 11:return E(_1D);case 12:return E(_1C);case 13:return E(_1B);case 14:return E(_1A);case 15:return E(_1z);default:return E(_1q);}},_1J=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_1K=new T(function(){return B(unCStr("main"));}),_1L=new T(function(){return B(unCStr("EventData"));}),_1M=new T(function(){var _1N=hs_wordToWord64(3703396926),_1O=_1N,_1P=hs_wordToWord64(1660403598),_1Q=_1P;return [0,_1O,_1Q,[0,_1O,_1Q,_1K,_1J,_1L],_9];}),_1R=[0,0],_1S=false,_1T=2,_1U=[1],_1V=new T(function(){return B(unCStr("Dynamic"));}),_1W=new T(function(){return B(unCStr("Data.Dynamic"));}),_1X=new T(function(){return B(unCStr("base"));}),_1Y=new T(function(){var _1Z=hs_wordToWord64(628307645),_20=_1Z,_21=hs_wordToWord64(949574464),_22=_21;return [0,_20,_22,[0,_20,_22,_1X,_1W,_1V],_9];}),_23=[0],_24=new T(function(){return B(unCStr("OnLoad"));}),_25=[0,_24,_23],_26=[0,_1M,_25],_27=[0,_1Y,_26],_28=[0],_29=function(_){return _28;},_2a=function(_2b,_){return _28;},_2c=[0,_29,_2a],_2d=[0,_9,_1R,_1T,_2c,_1S,_27,_1U],_2e=function(_){var _=0,_2f=newMVar(),_2g=_2f,_=putMVar(_2g,_2d);return [0,_2g];},_2h=function(_2i){var _2j=B(A(_2i,[_])),_2k=_2j;return E(_2k);},_2l=new T(function(){return B(_2h(_2e));}),_2m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2n=new T(function(){return B(unCStr("base"));}),_2o=new T(function(){return B(unCStr("PatternMatchFail"));}),_2p=new T(function(){var _2q=hs_wordToWord64(18445595),_2r=_2q,_2s=hs_wordToWord64(52003073),_2t=_2s;return [0,_2r,_2t,[0,_2r,_2t,_2n,_2m,_2o],_9];}),_2u=function(_2v){return E(_2p);},_2w=function(_2x){return E(E(_2x)[1]);},_2y=function(_2z,_2A,_2B){var _2C=B(A(_2z,[_])),_2D=B(A(_2A,[_])),_2E=hs_eqWord64(_2C[1],_2D[1]),_2F=_2E;if(!E(_2F)){return [0];}else{var _2G=hs_eqWord64(_2C[2],_2D[2]),_2H=_2G;return E(_2H)==0?[0]:[1,_2B];}},_2I=function(_2J){var _2K=E(_2J);return new F(function(){return _2y(B(_2w(_2K[1])),_2u,_2K[2]);});},_2L=function(_2M){return E(E(_2M)[1]);},_2N=function(_2O,_2P){return new F(function(){return _e(E(_2O)[1],_2P);});},_2Q=[0,44],_2R=[0,93],_2S=[0,91],_2T=function(_2U,_2V,_2W){var _2X=E(_2V);return _2X[0]==0?B(unAppCStr("[]",_2W)):[1,_2S,new T(function(){return B(A(_2U,[_2X[1],new T(function(){var _2Y=function(_2Z){var _30=E(_2Z);return _30[0]==0?E([1,_2R,_2W]):[1,_2Q,new T(function(){return B(A(_2U,[_30[1],new T(function(){return B(_2Y(_30[2]));})]));})];};return B(_2Y(_2X[2]));})]));})];},_31=function(_32,_33){return new F(function(){return _2T(_2N,_32,_33);});},_34=function(_35,_36,_37){return new F(function(){return _e(E(_36)[1],_37);});},_38=[0,_34,_2L,_31],_39=new T(function(){return [0,_2u,_38,_3a,_2I];}),_3a=function(_3b){return [0,_39,_3b];},_3c=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3d=function(_3e,_3f){return new F(function(){return die(new T(function(){return B(A(_3f,[_3e]));}));});},_3g=function(_3h,_3i){var _3j=E(_3i);if(!_3j[0]){return [0,_9,_9];}else{var _3k=_3j[1];if(!B(A(_3h,[_3k]))){return [0,_9,_3j];}else{var _3l=new T(function(){var _3m=B(_3g(_3h,_3j[2]));return [0,_3m[1],_3m[2]];});return [0,[1,_3k,new T(function(){return E(E(_3l)[1]);})],new T(function(){return E(E(_3l)[2]);})];}}},_3n=[0,32],_3o=[0,10],_3p=[1,_3o,_9],_3q=function(_3r){return E(E(_3r)[1])==124?false:true;},_3s=function(_3t,_3u){var _3v=B(_3g(_3q,B(unCStr(_3t)))),_3w=_3v[1],_3x=function(_3y,_3z){return new F(function(){return _e(_3y,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_3u,new T(function(){return B(_e(_3z,_3p));},1)));})));},1));});},_3A=E(_3v[2]);if(!_3A[0]){return new F(function(){return _3x(_3w,_9);});}else{return E(E(_3A[1])[1])==124?B(_3x(_3w,[1,_3n,_3A[2]])):B(_3x(_3w,_9));}},_3B=function(_3C){return new F(function(){return _3d([0,new T(function(){return B(_3s(_3C,_3c));})],_3a);});},_3D=new T(function(){return B(_3B("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_3E=[0,_1y,_23],_3F=[0,_1M,_3E],_3G=[0,_1x,_23],_3H=[0,_1M,_3G],_3I=[0,_1w,_23],_3J=[0,_1M,_3I],_3K=[0,_1v,_23],_3L=[0,_1M,_3K],_3M=[0,_1u,_23],_3N=[0,_1M,_3M],_3O=[3],_3P=[0,_1r,_3O],_3Q=[0,_1M,_3P],_3R=function(_3S,_3T){switch(E(_3S)[0]){case 0:return function(_){var _3U=E(_2l)[1],_3V=takeMVar(_3U),_3W=_3V,_=putMVar(_3U,new T(function(){var _3X=E(_3W);return [0,_3X[1],_3X[2],_3X[3],_3X[4],_3X[5],_3F,_3X[7]];}));return new F(function(){return A(_3T,[_]);});};case 1:return function(_){var _3Y=E(_2l)[1],_3Z=takeMVar(_3Y),_40=_3Z,_=putMVar(_3Y,new T(function(){var _41=E(_40);return [0,_41[1],_41[2],_41[3],_41[4],_41[5],_3H,_41[7]];}));return new F(function(){return A(_3T,[_]);});};case 2:return function(_){var _42=E(_2l)[1],_43=takeMVar(_42),_44=_43,_=putMVar(_42,new T(function(){var _45=E(_44);return [0,_45[1],_45[2],_45[3],_45[4],_45[5],_3J,_45[7]];}));return new F(function(){return A(_3T,[_]);});};case 3:return function(_){var _46=E(_2l)[1],_47=takeMVar(_46),_48=_47,_=putMVar(_46,new T(function(){var _49=E(_48);return [0,_49[1],_49[2],_49[3],_49[4],_49[5],_3L,_49[7]];}));return new F(function(){return A(_3T,[_]);});};case 4:return function(_){var _4a=E(_2l)[1],_4b=takeMVar(_4a),_4c=_4b,_=putMVar(_4a,new T(function(){var _4d=E(_4c);return [0,_4d[1],_4d[2],_4d[3],_4d[4],_4d[5],_3N,_4d[7]];}));return new F(function(){return A(_3T,[_]);});};case 5:return function(_4e){return function(_){var _4f=E(_2l)[1],_4g=takeMVar(_4f),_4h=_4g,_=putMVar(_4f,new T(function(){var _4i=E(_4h);return [0,_4i[1],_4i[2],_4i[3],_4i[4],_4i[5],[0,_1M,[0,_1t,[2,E(_4e)]]],_4i[7]];}));return new F(function(){return A(_3T,[_]);});};};case 6:return function(_4j){return function(_){var _4k=E(_2l)[1],_4l=takeMVar(_4k),_4m=_4l,_=putMVar(_4k,new T(function(){var _4n=E(_4m);return [0,_4n[1],_4n[2],_4n[3],_4n[4],_4n[5],[0,_1M,[0,_1s,[2,E(_4j)]]],_4n[7]];}));return new F(function(){return A(_3T,[_]);});};};case 7:return function(_){var _4o=E(_2l)[1],_4p=takeMVar(_4o),_4q=_4p,_=putMVar(_4o,new T(function(){var _4r=E(_4q);return [0,_4r[1],_4r[2],_4r[3],_4r[4],_4r[5],_3Q,_4r[7]];}));return new F(function(){return A(_3T,[_]);});};case 8:return function(_4s,_4t){return function(_){var _4u=E(_2l)[1],_4v=takeMVar(_4u),_4w=_4v,_=putMVar(_4u,new T(function(){var _4x=E(_4w);return [0,_4x[1],_4x[2],_4x[3],_4x[4],_4x[5],[0,_1M,[0,_1G,[1,_4s,E(_4t)]]],_4x[7]];}));return new F(function(){return A(_3T,[_]);});};};case 9:return function(_4y,_4z){return function(_){var _4A=E(_2l)[1],_4B=takeMVar(_4A),_4C=_4B,_=putMVar(_4A,new T(function(){var _4D=E(_4C);return [0,_4D[1],_4D[2],_4D[3],_4D[4],_4D[5],[0,_1M,[0,_1F,[1,_4y,E(_4z)]]],_4D[7]];}));return new F(function(){return A(_3T,[_]);});};};case 10:return function(_4E,_4F){return function(_){var _4G=E(_2l)[1],_4H=takeMVar(_4G),_4I=_4H,_=putMVar(_4G,new T(function(){var _4J=E(_4I);return [0,_4J[1],_4J[2],_4J[3],_4J[4],_4J[5],[0,_1M,[0,_1E,[1,_4E,E(_4F)]]],_4J[7]];}));return new F(function(){return A(_3T,[_]);});};};case 11:return function(_4K,_4L){return function(_){var _4M=E(_2l)[1],_4N=takeMVar(_4M),_4O=_4N,_=putMVar(_4M,new T(function(){var _4P=E(_4O);return [0,_4P[1],_4P[2],_4P[3],_4P[4],_4P[5],[0,_1M,[0,_1D,[1,_4K,E(_4L)]]],_4P[7]];}));return new F(function(){return A(_3T,[_]);});};};case 12:return function(_4Q,_){var _4R=E(_2l)[1],_4S=takeMVar(_4R),_4T=_4S,_=putMVar(_4R,new T(function(){var _4U=E(_4T);return [0,_4U[1],_4U[2],_4U[3],_4U[4],_4U[5],[0,_1M,[0,_1C,[4,_4Q]]],_4U[7]];}));return new F(function(){return A(_3T,[_]);});};case 13:return function(_4V,_){var _4W=E(_2l)[1],_4X=takeMVar(_4W),_4Y=_4X,_=putMVar(_4W,new T(function(){var _4Z=E(_4Y);return [0,_4Z[1],_4Z[2],_4Z[3],_4Z[4],_4Z[5],[0,_1M,[0,_1B,[4,_4V]]],_4Z[7]];}));return new F(function(){return A(_3T,[_]);});};case 14:return function(_50,_){var _51=E(_2l)[1],_52=takeMVar(_51),_53=_52,_=putMVar(_51,new T(function(){var _54=E(_53);return [0,_54[1],_54[2],_54[3],_54[4],_54[5],[0,_1M,[0,_1A,[4,_50]]],_54[7]];}));return new F(function(){return A(_3T,[_]);});};default:return E(_3D);}},_55=[0,_1H,_3R],_56=function(_57,_58,_){var _59=jsCreateTextNode(toJSStr(E(_57))),_5a=_59,_5b=jsAppendChild(_5a,E(_58)[1]);return [0,_5a];},_5c=0,_5d=function(_5e,_5f,_5g,_5h){return new F(function(){return A(_5e,[function(_){var _5i=jsSetAttr(E(_5f)[1],toJSStr(E(_5g)),toJSStr(E(_5h)));return _5c;}]);});},_5j=[0,112],_5k=function(_5l){var _5m=new T(function(){return E(E(_5l)[2]);});return function(_5n,_){return [0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_5m)[1],_9)),new T(function(){return E(E(_5l)[1]);},1)));})],new T(function(){var _5o=E(_5l);return [0,_5o[1],new T(function(){return [0,E(_5m)[1]+1|0];}),_5o[3],_5o[4],_5o[5],_5o[6],_5o[7]];})];};},_5p=new T(function(){return B(unCStr("id"));}),_5q=function(_5r){return E(_5r);},_5s=new T(function(){return B(unCStr("noid"));}),_5t=function(_5u,_){return _5u;},_5v=function(_5w,_5x,_){var _5y=jsFind(toJSStr(E(_5x))),_5z=_5y,_5A=E(_5z);if(!_5A[0]){var _5B=E(_2l)[1],_5C=takeMVar(_5B),_5D=_5C,_5E=B(A(_5w,[_5D,_])),_5F=_5E,_5G=E(_5F),_=putMVar(_5B,_5G[2]);return E(_5G[1])[2];}else{var _5H=E(_5A[1]),_5I=jsClearChildren(_5H[1]),_5J=E(_2l)[1],_5K=takeMVar(_5J),_5L=_5K,_5M=B(A(_5w,[_5L,_])),_5N=_5M,_5O=E(_5N),_5P=E(_5O[1]),_=putMVar(_5J,_5O[2]),_5Q=B(A(_5P[1],[_5H,_])),_5R=_5Q;return _5P[2];}},_5S=new T(function(){return B(unCStr("span"));}),_5T=function(_5U,_5V,_5W,_){var _5X=jsCreateElem(toJSStr(E(_5S))),_5Y=_5X,_5Z=jsAppendChild(_5Y,E(_5W)[1]),_60=[0,_5Y],_61=B(A(_5U,[_5V,_60,_])),_62=_61;return _60;},_63=function(_64){return E(_64);},_65=function(_66,_67,_68,_){var _69=B(A(_5k,[_68,_68,_])),_6a=_69,_6b=E(_6a),_6c=_6b[1],_6d=E(_6b[2]),_6e=_6d[2],_6f=E(_6d[4]),_6g=B(A(_66,[[0,_6d[1],_6e,_6d[3],[0,function(_){return new F(function(){return _5v(function(_6h,_){var _6i=B(A(_66,[new T(function(){var _6j=E(_6h);return [0,_6j[1],_6e,_6j[3],_6j[4],_6j[5],_6j[6],_6j[7]];}),_])),_6k=_6i;return [0,[0,_5t,E(E(_6k)[1])[2]],_6h];},_5s,_);});},function(_6l,_){var _6m=B(_5v(new T(function(){return B(A(_67,[_6l]));},1),_6c,_)),_6n=_6m,_6o=E(_6n);return _6o[0]==0?_28:B(A(_6f[2],[_6o[1],_]));}],_6d[5],_6d[6],_6d[7]],_])),_6p=_6g,_6q=E(_6p),_6r=_6q[2],_6s=E(_6q[1]),_6t=_6s[1],_6u=E(_6s[2]);if(!_6u[0]){return [0,[0,function(_6v,_){var _6w=B(A(_6t,[_6v,_])),_6x=_6w;if(!E(E(_68)[5])){var _6y=B(_5T(_63,_5t,_6v,_)),_6z=_6y,_6A=B(A(_5d,[_5q,_6z,_5p,_6c,_])),_6B=_6A;return _6v;}else{return _6v;}},_28],new T(function(){var _6C=E(_6r);return [0,_6C[1],_6C[2],_6C[3],_6f,_6C[5],_6C[6],_6C[7]];})];}else{var _6D=B(A(_67,[_6u[1],new T(function(){var _6E=E(_6r);return [0,_6E[1],_6E[2],_6E[3],_6f,_6E[5],_6E[6],_6E[7]];}),_])),_6F=_6D,_6G=E(_6F),_6H=E(_6G[1]),_6I=_6H[1];return [0,[0,function(_6J,_){var _6K=B(A(_6t,[_6J,_])),_6L=_6K;if(!E(E(_68)[5])){var _6M=B(_5T(_63,_6I,_6J,_)),_6N=_6M,_6O=B(A(_5d,[_5q,_6N,_5p,_6c,_])),_6P=_6O;return _6J;}else{var _6Q=B(A(_6I,[_6J,_])),_6R=_6Q;return _6J;}},_6H[2]],_6G[2]];}},_6S=function(_6T,_6U){switch(E(_6T)[0]){case 0:switch(E(_6U)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_6U)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_6U)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_6U)[0]==3?1:2;}},_6V=new T(function(){return B(unCStr("end of input"));}),_6W=new T(function(){return B(unCStr("unexpected"));}),_6X=new T(function(){return B(unCStr("expecting"));}),_6Y=new T(function(){return B(unCStr("unknown parse error"));}),_6Z=new T(function(){return B(unCStr("or"));}),_70=[0,58],_71=[0,34],_72=[0,41],_73=[1,_72,_9],_74=function(_75,_76,_77){var _78=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_76,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_77,_9)),_73));})));},1)));})));}),_79=E(_75);return _79[0]==0?E(_78):[1,_71,new T(function(){return B(_e(_79,new T(function(){return B(unAppCStr("\" ",_78));},1)));})];},_7a=function(_7b,_7c){while(1){var _7d=E(_7b);if(!_7d[0]){return E(_7c)[0]==0?true:false;}else{var _7e=E(_7c);if(!_7e[0]){return false;}else{if(E(_7d[1])[1]!=E(_7e[1])[1]){return false;}else{_7b=_7d[2];_7c=_7e[2];continue;}}}}},_7f=function(_7g,_7h){return !B(_7a(_7g,_7h))?true:false;},_7i=[0,_7a,_7f],_7j=function(_7k,_7l,_7m){var _7n=E(_7m);if(!_7n[0]){return E(_7l);}else{return new F(function(){return _e(_7l,new T(function(){return B(_e(_7k,new T(function(){return B(_7j(_7k,_7n[1],_7n[2]));},1)));},1));});}},_7o=function(_7p){return E(_7p)[0]==0?false:true;},_7q=new T(function(){return B(unCStr(", "));}),_7r=function(_7s){var _7t=E(_7s);if(!_7t[0]){return [0];}else{return new F(function(){return _e(_7t[1],new T(function(){return B(_7r(_7t[2]));},1));});}},_7u=function(_7v,_7w){while(1){var _7x=(function(_7y,_7z){var _7A=E(_7z);if(!_7A[0]){return [0];}else{var _7B=_7A[1],_7C=_7A[2];if(!B(A(_7y,[_7B]))){var _7D=_7y;_7w=_7C;_7v=_7D;return null;}else{return [1,_7B,new T(function(){return B(_7u(_7y,_7C));})];}}})(_7v,_7w);if(_7x!=null){return _7x;}}},_7E=function(_7F,_7G){var _7H=E(_7G);return _7H[0]==0?[0]:[1,_7F,new T(function(){return B(_7E(_7H[1],_7H[2]));})];},_7I=function(_7J,_7K){while(1){var _7L=E(_7K);if(!_7L[0]){return E(_7J);}else{_7J=_7L[1];_7K=_7L[2];continue;}}},_7M=function(_7N){switch(E(_7N)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_7O=function(_7P){return E(_7P)[0]==1?true:false;},_7Q=function(_7R){return E(_7R)[0]==2?true:false;},_7S=[0,10],_7T=[1,_7S,_9],_7U=function(_7V){return new F(function(){return _e(_7T,_7V);});},_7W=[0,32],_7X=function(_7Y,_7Z){var _80=E(_7Z);return _80[0]==0?[0]:[1,new T(function(){return B(A(_7Y,[_80[1]]));}),new T(function(){return B(_7X(_7Y,_80[2]));})];},_81=function(_82){var _83=E(_82);switch(_83[0]){case 0:return E(_83[1]);case 1:return E(_83[1]);case 2:return E(_83[1]);default:return E(_83[1]);}},_84=function(_85){return E(E(_85)[1]);},_86=function(_87,_88,_89){while(1){var _8a=E(_89);if(!_8a[0]){return false;}else{if(!B(A(_84,[_87,_88,_8a[1]]))){_89=_8a[2];continue;}else{return true;}}}},_8b=function(_8c,_8d){var _8e=function(_8f,_8g){while(1){var _8h=(function(_8i,_8j){var _8k=E(_8i);if(!_8k[0]){return [0];}else{var _8l=_8k[1],_8m=_8k[2];if(!B(_86(_8c,_8l,_8j))){return [1,_8l,new T(function(){return B(_8e(_8m,[1,_8l,_8j]));})];}else{_8f=_8m;var _8n=_8j;_8g=_8n;return null;}}})(_8f,_8g);if(_8h!=null){return _8h;}}};return new F(function(){return _8e(_8d,_9);});},_8o=function(_8p,_8q,_8r,_8s,_8t,_8u){var _8v=E(_8u);if(!_8v[0]){return E(_8q);}else{var _8w=new T(function(){var _8x=B(_3g(_7M,_8v));return [0,_8x[1],_8x[2]];}),_8y=new T(function(){var _8z=B(_3g(_7O,E(_8w)[2]));return [0,_8z[1],_8z[2]];}),_8A=new T(function(){return E(E(_8y)[1]);}),_8B=function(_8C,_8D){var _8E=E(_8D);if(!_8E[0]){return E(_8C);}else{var _8F=new T(function(){return B(_e(_8p,[1,_7W,new T(function(){return B(_7I(_8C,_8E));})]));}),_8G=B(_8b(_7i,B(_7u(_7o,B(_7E(_8C,_8E))))));if(!_8G[0]){return new F(function(){return _e(_9,[1,_7W,_8F]);});}else{var _8H=_8G[1],_8I=E(_8G[2]);if(!_8I[0]){return new F(function(){return _e(_8H,[1,_7W,_8F]);});}else{return new F(function(){return _e(B(_e(_8H,new T(function(){return B(_e(_7q,new T(function(){return B(_7j(_7q,_8I[1],_8I[2]));},1)));},1))),[1,_7W,_8F]);});}}}},_8J=function(_8K,_8L){var _8M=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_8L))))));if(!_8M[0]){return [0];}else{var _8N=_8M[1],_8O=_8M[2],_8P=E(_8K);return _8P[0]==0?B(_8B(_8N,_8O)):B(_e(_8P,[1,_7W,new T(function(){return B(_8B(_8N,_8O));})]));}},_8Q=new T(function(){var _8R=B(_3g(_7Q,E(_8y)[2]));return [0,_8R[1],_8R[2]];});return new F(function(){return _7r(B(_7X(_7U,B(_8b(_7i,B(_7u(_7o,[1,new T(function(){if(!E(_8A)[0]){var _8S=E(E(_8w)[1]);if(!_8S[0]){var _8T=[0];}else{var _8U=E(_8S[1]);switch(_8U[0]){case 0:var _8V=E(_8U[1]),_8W=_8V[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8V]));break;case 1:var _8X=E(_8U[1]),_8W=_8X[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8X]));break;case 2:var _8Y=E(_8U[1]),_8W=_8Y[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Y]));break;default:var _8Z=E(_8U[1]),_8W=_8Z[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Z]));}var _8T=_8W;}var _90=_8T,_91=_90;}else{var _91=[0];}return _91;}),[1,new T(function(){return B(_8J(_8s,_8A));}),[1,new T(function(){return B(_8J(_8r,E(_8Q)[1]));}),[1,new T(function(){return B((function(_92){var _93=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_92))))));return _93[0]==0?[0]:B(_8B(_93[1],_93[2]));})(E(_8Q)[2]));}),_9]]]])))))));});}},_94=[1,_9,_9],_95=function(_96,_97){var _98=function(_99,_9a){var _9b=E(_99);if(!_9b[0]){return E(_9a);}else{var _9c=_9b[1],_9d=E(_9a);if(!_9d[0]){return E(_9b);}else{var _9e=_9d[1];return B(A(_96,[_9c,_9e]))==2?[1,_9e,new T(function(){return B(_98(_9b,_9d[2]));})]:[1,_9c,new T(function(){return B(_98(_9b[2],_9d));})];}}},_9f=function(_9g){var _9h=E(_9g);if(!_9h[0]){return [0];}else{var _9i=E(_9h[2]);return _9i[0]==0?E(_9h):[1,new T(function(){return B(_98(_9h[1],_9i[1]));}),new T(function(){return B(_9f(_9i[2]));})];}},_9j=function(_9k){while(1){var _9l=E(_9k);if(!_9l[0]){return E(new T(function(){return B(_9j(B(_9f(_9))));}));}else{if(!E(_9l[2])[0]){return E(_9l[1]);}else{_9k=B(_9f(_9l));continue;}}}},_9m=new T(function(){return B(_9n(_9));}),_9n=function(_9o){var _9p=E(_9o);if(!_9p[0]){return E(_94);}else{var _9q=_9p[1],_9r=E(_9p[2]);if(!_9r[0]){return [1,_9p,_9];}else{var _9s=_9r[1],_9t=_9r[2];if(B(A(_96,[_9q,_9s]))==2){return new F(function(){return (function(_9u,_9v,_9w){while(1){var _9x=(function(_9y,_9z,_9A){var _9B=E(_9A);if(!_9B[0]){return [1,[1,_9y,_9z],_9m];}else{var _9C=_9B[1];if(B(A(_96,[_9y,_9C]))==2){_9u=_9C;var _9D=[1,_9y,_9z];_9w=_9B[2];_9v=_9D;return null;}else{return [1,[1,_9y,_9z],new T(function(){return B(_9n(_9B));})];}}})(_9u,_9v,_9w);if(_9x!=null){return _9x;}}})(_9s,[1,_9q,_9],_9t);});}else{return new F(function(){return (function(_9E,_9F,_9G){while(1){var _9H=(function(_9I,_9J,_9K){var _9L=E(_9K);if(!_9L[0]){return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),_9m];}else{var _9M=_9L[1],_9N=_9L[2];switch(B(A(_96,[_9I,_9M]))){case 0:_9E=_9M;_9F=function(_9O){return new F(function(){return A(_9J,[[1,_9I,_9O]]);});};_9G=_9N;return null;case 1:_9E=_9M;_9F=function(_9P){return new F(function(){return A(_9J,[[1,_9I,_9P]]);});};_9G=_9N;return null;default:return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),new T(function(){return B(_9n(_9L));})];}}})(_9E,_9F,_9G);if(_9H!=null){return _9H;}}})(_9s,function(_9Q){return [1,_9q,_9Q];},_9t);});}}}};return new F(function(){return _9j(B(_9n(_97)));});},_9R=function(_9S,_9T,_9U,_9V){return new F(function(){return _e(B(_74(_9S,_9T,_9U)),[1,_70,new T(function(){return B(_8o(_6Z,_6Y,_6X,_6W,_6V,B(_95(_6S,_9V))));})]);});},_9W=function(_9X){var _9Y=E(_9X),_9Z=E(_9Y[1]);return new F(function(){return _9R(_9Z[1],_9Z[2],_9Z[3],_9Y[2]);});},_a0=new T(function(){return B(unCStr(" . "));}),_a1=function(_a2){var _a3=E(_a2);switch(_a3[0]){case 0:return E(_a3[3]);case 1:return E(_a3[3]);case 2:return E(_a3[3]);case 3:return E(_a3[3]);case 4:return E(_a3[3]);case 5:return E(_a3[3]);case 6:return E(_a3[3]);case 7:return E(_a3[3]);case 8:return E(_a3[3]);default:return E(_a3[3]);}},_a4=[0,41],_a5=[1,_a4,_9],_a6=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_a7=[0,44],_a8=[0,40],_a9=function(_aa,_ab,_ac){var _ad=E(_ac);switch(_ad[0]){case 0:return E(_a6);case 1:return new F(function(){return A(_aa,[_ad[2],_9]);});break;case 2:return new F(function(){return _a1(_ad[2]);});break;case 3:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),[1,new T(function(){return B(_a9(_aa,_ab,_ad[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[4])),_a5));})]));})]);});}},_ae=[0],_af=function(_ag,_ah,_ai,_aj,_ak,_al,_am,_an){var _ao=E(_an);switch(_ao[0]){case 0:return [0];case 1:return new F(function(){return A(_aj,[_ao[2],_9]);});break;case 2:return new F(function(){return _a1(_ao[2]);});break;case 3:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),[1,new T(function(){return B(_a9(_aj,_ak,_ao[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[4])),_a5));})]));})]);});break;case 7:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_a1(_ao[2])),new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));},1));});break;case 9:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4]));}),_9]]]);});break;case 10:return [1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3])),new T(function(){return B(_e(B(_a1(_ao[2])),new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4])),_a5));},1)));},1)));})];case 11:var _ap=_ao[2],_aq=_ao[3];return new F(function(){return A(_ai,[_ap,[1,new T(function(){return B(A(_al,[new T(function(){return B(A(_aq,[_ae]));}),_ap]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_aq,[_ae]))));}),_9]]]);});break;default:var _ar=_ao[2],_as=_ao[3];return new F(function(){return _e(B(_a1(_ar)),new T(function(){return B(_e(B(A(_am,[new T(function(){return B(A(_as,[_ae]));}),_ar])),[1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_as,[_ae])))),_a5));})]));},1));});}},_at=function(_au){var _av=E(_au);if(!_av[0]){return [0];}else{return new F(function(){return _e(_av[1],new T(function(){return B(_at(_av[2]));},1));});}},_aw=function(_ax,_ay){var _az=E(_ay);return _az[0]==0?[0]:[1,_ax,[1,_az[1],new T(function(){return B(_aw(_ax,_az[2]));})]];},_aA=function(_aB,_aC,_aD,_aE,_aF,_aG,_aH,_aI){var _aJ=E(_aI);if(!_aJ[0]){return new F(function(){return _a1(_aJ[1]);});}else{var _aK=B(_7X(function(_aL){return new F(function(){return _af(_aB,_aC,_aD,_aF,_aE,_aG,_aH,_aL);});},_aJ[1]));return _aK[0]==0?[0]:B(_at([1,_aK[1],new T(function(){return B(_aw(_a0,_aK[2]));})]));}},_aM=function(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aU,_aV){return new F(function(){return _2T(function(_aW,_aX){return new F(function(){return _e(B(_aA(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aW)),_aX);});},_aU,_aV);});},_aY=function(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,_b8){return new F(function(){return _e(B(_aA(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b7)),_b8);});},_b9=function(_ba,_bb,_bc,_bd,_be,_bf,_bg){return [0,function(_bh,_bi,_bj){return new F(function(){return _aY(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bh,_bi,_bj);});},function(_bj){return new F(function(){return _aA(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bj);});},function(_bi,_bj){return new F(function(){return _aM(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bi,_bj);});}];},_bk=new T(function(){return B(unCStr(" . "));}),_bl=new T(function(){return B(unCStr(" \u2234 "));}),_bm=function(_bn){return E(E(_bn)[2]);},_bo=function(_bp,_bq,_br){var _bs=B(_7X(new T(function(){return B(_bm(_bp));}),_bq));if(!_bs[0]){return new F(function(){return _e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1));});}else{return new F(function(){return _e(B(_at([1,_bs[1],new T(function(){return B(_aw(_bk,_bs[2]));})])),new T(function(){return B(_e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1)));},1));});}},_bt=2,_bu=function(_bv,_){return [0,[0,_5t,[1,_bv]],_bv];},_bw=function(_bx){return function(_by,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bz=E(_bx);return B(_e(B(_F(0,E(_bz[2])[1],_9)),_bz[1]));})]]],_by];};},_bA=function(_bB,_){return new F(function(){return _65(_bu,_bw,_bB,_);});},_bC=function(_bD){return function(_bE,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bF=E(_bD);return B(_e(B(_F(0,E(_bF[2])[1],_9)),_bF[1]));})]]],_bE];};},_bG=function(_bB,_){return new F(function(){return _65(_bu,_bC,_bB,_);});},_bH=function(_bI){return function(_bJ,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bK=E(_bI);return B(_e(B(_F(0,E(_bK[2])[1],_9)),_bK[1]));})]]],_bJ];};},_bL=function(_bB,_){return new F(function(){return _65(_bu,_bH,_bB,_);});},_bM=new T(function(){return B(unCStr("rslt"));}),_bN=new T(function(){return B(unCStr("root"));}),_bO=new T(function(){return B(unCStr("analysis"));}),_bP=new T(function(){return B(unCStr("class"));}),_bQ=new T(function(){return B(unCStr("invalid"));}),_bR=function(_bB,_){return new F(function(){return _5T(_56,_bQ,_bB,_);});},_bS=[1,_5c],_bT=[0,_bR,_bS],_bU=function(_bV,_){return [0,_bT,_bV];},_bW=new T(function(){return B(unCStr("div"));}),_bX=function(_bY,_bZ,_c0,_){var _c1=jsCreateElem(toJSStr(E(_bW))),_c2=_c1,_c3=jsAppendChild(_c2,E(_c0)[1]),_c4=[0,_c2],_c5=B(A(_bY,[_bZ,_c4,_])),_c6=_c5;return _c4;},_c7=function(_c8,_c9,_){var _ca=E(_c8);if(!_ca[0]){return _c9;}else{var _cb=B(_bX(_56,_ca[1],_c9,_)),_cc=_cb,_cd=B(_c7(_ca[2],_c9,_)),_ce=_cd;return _c9;}},_cf=new T(function(){return B(unCStr("lined"));}),_cg=new T(function(){return B(unCStr("span"));}),_ch=function(_ci,_cj,_ck,_cl,_){var _cm=B(A(_ck,[_cl,_])),_cn=_cm,_co=E(_cn),_cp=E(_co[1]),_cq=_cp[1];return [0,[0,function(_cr,_){var _cs=jsFind(toJSStr(E(_ci))),_ct=_cs,_cu=E(_ct);if(!_cu[0]){return _cr;}else{var _cv=_cu[1];switch(E(_cj)){case 0:var _cw=B(A(_cq,[_cv,_])),_cx=_cw;return _cr;case 1:var _cy=E(_cv),_cz=_cy[1],_cA=jsGetChildren(_cz),_cB=_cA,_cC=E(_cB);if(!_cC[0]){var _cD=B(A(_cq,[_cy,_])),_cE=_cD;return _cr;}else{var _cF=jsCreateElem(toJSStr(E(_cg))),_cG=_cF,_cH=jsAddChildBefore(_cG,_cz,E(_cC[1])[1]),_cI=B(A(_cq,[[0,_cG],_])),_cJ=_cI;return _cr;}break;default:var _cK=E(_cv),_cL=jsClearChildren(_cK[1]),_cM=B(A(_cq,[_cK,_])),_cN=_cM;return _cr;}}},_cp[2]],_co[2]];},_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR[0]){return E(_cQ)[0]==0?1:0;}else{var _cS=E(_cQ);if(!_cS[0]){return 2;}else{var _cT=E(_cR[1])[1],_cU=E(_cS[1])[1];if(_cT!=_cU){return _cT>_cU?2:0;}else{_cP=_cR[2];_cQ=_cS[2];continue;}}}}},_cV=new T(function(){return B(_e(_9,_9));}),_cW=function(_cX,_cY,_cZ,_d0,_d1,_d2,_d3,_d4){var _d5=[0,_cX,_cY,_cZ],_d6=function(_d7){var _d8=E(_d0);if(!_d8[0]){var _d9=E(_d4);if(!_d9[0]){switch(B(_cO(_cX,_d1))){case 0:return [0,[0,_d1,_d2,_d3],_9];case 1:return _cY>=_d2?_cY!=_d2?[0,_d5,_9]:_cZ>=_d3?_cZ!=_d3?[0,_d5,_9]:[0,_d5,_cV]:[0,[0,_d1,_d2,_d3],_9]:[0,[0,_d1,_d2,_d3],_9];default:return [0,_d5,_9];}}else{return [0,[0,_d1,_d2,_d3],_d9];}}else{switch(B(_cO(_cX,_d1))){case 0:return [0,[0,_d1,_d2,_d3],_d4];case 1:return _cY>=_d2?_cY!=_d2?[0,_d5,_d8]:_cZ>=_d3?_cZ!=_d3?[0,_d5,_d8]:[0,_d5,new T(function(){return B(_e(_d8,_d4));})]:[0,[0,_d1,_d2,_d3],_d4]:[0,[0,_d1,_d2,_d3],_d4];default:return [0,_d5,_d8];}}};if(!E(_d4)[0]){var _da=E(_d0);return _da[0]==0?B(_d6(_)):[0,_d5,_da];}else{return new F(function(){return _d6(_);});}},_db=function(_dc,_dd){while(1){var _de=E(_dc);if(!_de[0]){return E(_dd);}else{_dc=_de[2];var _df=[1,_de[1],_dd];_dd=_df;continue;}}},_dg=new T(function(){return B(_db(_9,_9));}),_dh=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_di=new T(function(){return B(err(_dh));}),_dj=function(_dk,_dl,_dm,_dn,_do){var _dp=function(_dq,_dr,_ds){var _dt=[1,_dr,_dq];return new F(function(){return A(_dk,[_ds,new T(function(){var _du=E(_dq);return function(_dv,_dw,_dx){return new F(function(){return _dp(_dt,_dv,_dw);});};}),_dn,_di,function(_dy){return new F(function(){return A(_dm,[new T(function(){return B(_db(_dt,_9));}),_ds,new T(function(){var _dz=E(E(_ds)[2]),_dA=E(_dy),_dB=E(_dA[1]),_dC=B(_cW(_dB[1],_dB[2],_dB[3],_dA[2],_dz[1],_dz[2],_dz[3],_9));return [0,E(_dC[1]),_dC[2]];})]);});}]);});};return new F(function(){return A(_dk,[_dl,function(_dD,_dE,_dF){return new F(function(){return _dp(_9,_dD,_dE);});},_dn,_di,function(_dG){return new F(function(){return A(_do,[_dg,_dl,new T(function(){var _dH=E(E(_dl)[2]),_dI=E(_dG),_dJ=E(_dI[1]),_dK=B(_cW(_dJ[1],_dJ[2],_dJ[3],_dI[2],_dH[1],_dH[2],_dH[3],_9));return [0,E(_dK[1]),_dK[2]];})]);});}]);});},_dL=function(_dM,_dN){var _dO=E(_dM),_dP=E(_dO[1]),_dQ=E(_dN),_dR=E(_dQ[1]),_dS=B(_cW(_dP[1],_dP[2],_dP[3],_dO[2],_dR[1],_dR[2],_dR[3],_dQ[2]));return [0,E(_dS[1]),_dS[2]];},_dT=function(_dU,_dV,_dW,_dX,_dY,_dZ){var _e0=function(_e1,_e2,_e3,_e4,_e5){return new F(function(){return _dj(_dU,_e2,function(_e6,_e7,_e8){return new F(function(){return A(_e3,[[1,_e1,_e6],_e7,new T(function(){var _e9=E(E(_e7)[2]),_ea=E(_e8),_eb=E(_ea[1]),_ec=B(_cW(_eb[1],_eb[2],_eb[3],_ea[2],_e9[1],_e9[2],_e9[3],_9));return [0,E(_ec[1]),_ec[2]];})]);});},_e4,function(_ed,_ee,_ef){return new F(function(){return A(_e5,[[1,_e1,_ed],_ee,new T(function(){var _eg=E(E(_ee)[2]),_eh=E(_ef),_ei=E(_eh[1]),_ej=B(_cW(_ei[1],_ei[2],_ei[3],_eh[2],_eg[1],_eg[2],_eg[3],_9));return [0,E(_ej[1]),_ej[2]];})]);});});});};return new F(function(){return A(_dU,[_dV,function(_ek,_el,_em){return new F(function(){return _e0(_ek,_el,_dW,_dX,function(_en,_eo,_ep){return new F(function(){return A(_dW,[_en,_eo,new T(function(){return B(_dL(_em,_ep));})]);});});});},_dX,function(_eq,_er,_es){return new F(function(){return _e0(_eq,_er,_dW,_dX,function(_et,_eu,_ev){return new F(function(){return A(_dY,[_et,_eu,new T(function(){return B(_dL(_es,_ev));})]);});});});},_dZ]);});},_ew=function(_ex,_ey,_ez,_eA,_eB){var _eC=function(_eD,_eE){return new F(function(){return A(_ex,[_eE,new T(function(){var _eF=E(_eD);return function(_eG,_eH,_eI){return new F(function(){return _eC(_9,_eH);});};}),_eA,_di,function(_eJ){return new F(function(){return A(_ez,[_5c,_eE,new T(function(){var _eK=E(E(_eE)[2]),_eL=E(_eJ),_eM=E(_eL[1]),_eN=B(_cW(_eM[1],_eM[2],_eM[3],_eL[2],_eK[1],_eK[2],_eK[3],_9));return [0,E(_eN[1]),_eN[2]];})]);});}]);});};return new F(function(){return A(_ex,[_ey,function(_eO,_eP,_eQ){return new F(function(){return _eC(_9,_eP);});},_eA,_di,function(_eR){return new F(function(){return A(_eB,[_5c,_ey,new T(function(){var _eS=E(E(_ey)[2]),_eT=E(_eR),_eU=E(_eT[1]),_eV=B(_cW(_eU[1],_eU[2],_eU[3],_eT[2],_eS[1],_eS[2],_eS[3],_9));return [0,E(_eV[1]),_eV[2]];})]);});}]);});},_eW=function(_eX,_eY,_eZ,_f0,_f1,_f2,_f3){var _f4=function(_f5,_f6,_f7,_f8,_f9){var _fa=[1,_f5,_9],_fb=function(_fc,_fd,_fe,_ff){return new F(function(){return _eW(_eX,_eY,_fc,function(_fg,_fh,_fi){return new F(function(){return A(_fd,[[1,_f5,_fg],_fh,new T(function(){var _fj=E(E(_fh)[2]),_fk=E(_fi),_fl=E(_fk[1]),_fm=B(_cW(_fl[1],_fl[2],_fl[3],_fk[2],_fj[1],_fj[2],_fj[3],_9));return [0,E(_fm[1]),_fm[2]];})]);});},_fe,function(_fn,_fo,_fp){return new F(function(){return A(_ff,[[1,_f5,_fn],_fo,new T(function(){var _fq=E(E(_fo)[2]),_fr=E(_fp),_fs=E(_fr[1]),_ft=B(_cW(_fs[1],_fs[2],_fs[3],_fr[2],_fq[1],_fq[2],_fq[3],_9));return [0,E(_ft[1]),_ft[2]];})]);});},function(_fu){return new F(function(){return A(_ff,[_fa,_fc,new T(function(){var _fv=E(E(_fc)[2]),_fw=_fv[1],_fx=_fv[2],_fy=_fv[3],_fz=E(_fu),_fA=E(_fz[1]),_fB=B(_cW(_fA[1],_fA[2],_fA[3],_fz[2],_fw,_fx,_fy,_9)),_fC=E(_fB[1]),_fD=B(_cW(_fC[1],_fC[2],_fC[3],_fB[2],_fw,_fx,_fy,_9));return [0,E(_fD[1]),_fD[2]];})]);});});});};return new F(function(){return A(_eY,[_f6,function(_fE,_fF,_fG){return new F(function(){return _fb(_fF,_f7,_f8,function(_fH,_fI,_fJ){return new F(function(){return A(_f7,[_fH,_fI,new T(function(){return B(_dL(_fG,_fJ));})]);});});});},_f8,function(_fK,_fL,_fM){return new F(function(){return _fb(_fL,_f7,_f8,function(_fN,_fO,_fP){return new F(function(){return A(_f9,[_fN,_fO,new T(function(){return B(_dL(_fM,_fP));})]);});});});},function(_fQ){return new F(function(){return A(_f9,[_fa,_f6,new T(function(){var _fR=E(E(_f6)[2]),_fS=E(_fQ),_fT=E(_fS[1]),_fU=B(_cW(_fT[1],_fT[2],_fT[3],_fS[2],_fR[1],_fR[2],_fR[3],_9));return [0,E(_fU[1]),_fU[2]];})]);});}]);});};return new F(function(){return A(_eX,[_eZ,function(_fV,_fW,_fX){return new F(function(){return _f4(_fV,_fW,_f0,_f1,function(_fY,_fZ,_g0){return new F(function(){return A(_f0,[_fY,_fZ,new T(function(){return B(_dL(_fX,_g0));})]);});});});},_f1,function(_g1,_g2,_g3){return new F(function(){return _f4(_g1,_g2,_f0,_f1,function(_g4,_g5,_g6){return new F(function(){return A(_f2,[_g4,_g5,new T(function(){return B(_dL(_g3,_g6));})]);});});});},_f3]);});},_g7=function(_g8,_g9){return new F(function(){return A(_g9,[_g8]);});},_ga=[0,34],_gb=[1,_ga,_9],_gc=[0,E(_9)],_gd=[1,_gc,_9],_ge=function(_gf,_gg){var _gh=_gf%_gg;if(_gf<=0){if(_gf>=0){return E(_gh);}else{if(_gg<=0){return E(_gh);}else{var _gi=E(_gh);return _gi==0?0:_gi+_gg|0;}}}else{if(_gg>=0){if(_gf>=0){return E(_gh);}else{if(_gg<=0){return E(_gh);}else{var _gj=E(_gh);return _gj==0?0:_gj+_gg|0;}}}else{var _gk=E(_gh);return _gk==0?0:_gk+_gg|0;}}},_gl=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_gm=new T(function(){return B(err(_gl));}),_gn=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_go=new T(function(){return B(err(_gn));}),_gp=function(_gq,_gr){while(1){var _gs=E(_gq);if(!_gs[0]){return E(_go);}else{var _gt=E(_gr);if(!_gt){return E(_gs[1]);}else{_gq=_gs[2];_gr=_gt-1|0;continue;}}}},_gu=new T(function(){return B(unCStr("ACK"));}),_gv=new T(function(){return B(unCStr("BEL"));}),_gw=new T(function(){return B(unCStr("BS"));}),_gx=new T(function(){return B(unCStr("SP"));}),_gy=[1,_gx,_9],_gz=new T(function(){return B(unCStr("US"));}),_gA=[1,_gz,_gy],_gB=new T(function(){return B(unCStr("RS"));}),_gC=[1,_gB,_gA],_gD=new T(function(){return B(unCStr("GS"));}),_gE=[1,_gD,_gC],_gF=new T(function(){return B(unCStr("FS"));}),_gG=[1,_gF,_gE],_gH=new T(function(){return B(unCStr("ESC"));}),_gI=[1,_gH,_gG],_gJ=new T(function(){return B(unCStr("SUB"));}),_gK=[1,_gJ,_gI],_gL=new T(function(){return B(unCStr("EM"));}),_gM=[1,_gL,_gK],_gN=new T(function(){return B(unCStr("CAN"));}),_gO=[1,_gN,_gM],_gP=new T(function(){return B(unCStr("ETB"));}),_gQ=[1,_gP,_gO],_gR=new T(function(){return B(unCStr("SYN"));}),_gS=[1,_gR,_gQ],_gT=new T(function(){return B(unCStr("NAK"));}),_gU=[1,_gT,_gS],_gV=new T(function(){return B(unCStr("DC4"));}),_gW=[1,_gV,_gU],_gX=new T(function(){return B(unCStr("DC3"));}),_gY=[1,_gX,_gW],_gZ=new T(function(){return B(unCStr("DC2"));}),_h0=[1,_gZ,_gY],_h1=new T(function(){return B(unCStr("DC1"));}),_h2=[1,_h1,_h0],_h3=new T(function(){return B(unCStr("DLE"));}),_h4=[1,_h3,_h2],_h5=new T(function(){return B(unCStr("SI"));}),_h6=[1,_h5,_h4],_h7=new T(function(){return B(unCStr("SO"));}),_h8=[1,_h7,_h6],_h9=new T(function(){return B(unCStr("CR"));}),_ha=[1,_h9,_h8],_hb=new T(function(){return B(unCStr("FF"));}),_hc=[1,_hb,_ha],_hd=new T(function(){return B(unCStr("VT"));}),_he=[1,_hd,_hc],_hf=new T(function(){return B(unCStr("LF"));}),_hg=[1,_hf,_he],_hh=new T(function(){return B(unCStr("HT"));}),_hi=[1,_hh,_hg],_hj=[1,_gw,_hi],_hk=[1,_gv,_hj],_hl=[1,_gu,_hk],_hm=new T(function(){return B(unCStr("ENQ"));}),_hn=[1,_hm,_hl],_ho=new T(function(){return B(unCStr("EOT"));}),_hp=[1,_ho,_hn],_hq=new T(function(){return B(unCStr("ETX"));}),_hr=[1,_hq,_hp],_hs=new T(function(){return B(unCStr("STX"));}),_ht=[1,_hs,_hr],_hu=new T(function(){return B(unCStr("SOH"));}),_hv=[1,_hu,_ht],_hw=new T(function(){return B(unCStr("NUL"));}),_hx=[1,_hw,_hv],_hy=[0,92],_hz=new T(function(){return B(unCStr("\\DEL"));}),_hA=new T(function(){return B(unCStr("\\a"));}),_hB=new T(function(){return B(unCStr("\\\\"));}),_hC=new T(function(){return B(unCStr("\\SO"));}),_hD=new T(function(){return B(unCStr("\\r"));}),_hE=new T(function(){return B(unCStr("\\f"));}),_hF=new T(function(){return B(unCStr("\\v"));}),_hG=new T(function(){return B(unCStr("\\n"));}),_hH=new T(function(){return B(unCStr("\\t"));}),_hI=new T(function(){return B(unCStr("\\b"));}),_hJ=function(_hK,_hL){if(_hK<=127){var _hM=E(_hK);switch(_hM){case 92:return new F(function(){return _e(_hB,_hL);});break;case 127:return new F(function(){return _e(_hz,_hL);});break;default:if(_hM<32){var _hN=E(_hM);switch(_hN){case 7:return new F(function(){return _e(_hA,_hL);});break;case 8:return new F(function(){return _e(_hI,_hL);});break;case 9:return new F(function(){return _e(_hH,_hL);});break;case 10:return new F(function(){return _e(_hG,_hL);});break;case 11:return new F(function(){return _e(_hF,_hL);});break;case 12:return new F(function(){return _e(_hE,_hL);});break;case 13:return new F(function(){return _e(_hD,_hL);});break;case 14:return new F(function(){return _e(_hC,new T(function(){var _hO=E(_hL);if(!_hO[0]){var _hP=[0];}else{var _hP=E(E(_hO[1])[1])==72?B(unAppCStr("\\&",_hO)):E(_hO);}return _hP;},1));});break;default:return new F(function(){return _e([1,_hy,new T(function(){var _hQ=_hN;return _hQ>=0?B(_gp(_hx,_hQ)):E(_gm);})],_hL);});}}else{return [1,[0,_hM],_hL];}}}else{return [1,_hy,new T(function(){var _hR=jsShowI(_hK),_hS=_hR;return B(_e(fromJSStr(_hS),new T(function(){var _hT=E(_hL);if(!_hT[0]){var _hU=[0];}else{var _hV=E(_hT[1])[1];if(_hV<48){var _hW=E(_hT);}else{var _hW=_hV>57?E(_hT):B(unAppCStr("\\&",_hT));}var _hX=_hW,_hY=_hX,_hU=_hY;}return _hU;},1)));})];}},_hZ=new T(function(){return B(unCStr("\\\""));}),_i0=function(_i1,_i2){var _i3=E(_i1);if(!_i3[0]){return E(_i2);}else{var _i4=_i3[2],_i5=E(E(_i3[1])[1]);if(_i5==34){return new F(function(){return _e(_hZ,new T(function(){return B(_i0(_i4,_i2));},1));});}else{return new F(function(){return _hJ(_i5,new T(function(){return B(_i0(_i4,_i2));}));});}}},_i6=function(_i7,_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig){var _ih=[0,_ib,_ic,_id];return new F(function(){return A(_i7,[new T(function(){return B(A(_i8,[_ia]));}),function(_ii){var _ij=E(_ii);if(!_ij[0]){return E(new T(function(){return B(A(_ig,[[0,E(_ih),_gd]]));}));}else{var _ik=E(_ij[1]),_il=_ik[1],_im=_ik[2];if(!B(A(_i9,[_il]))){return new F(function(){return A(_ig,[[0,E(_ih),[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_il,_9],_gb));})])],_9]]]);});}else{var _in=E(_il);switch(E(_in[1])){case 9:var _io=[0,_ib,_ic,(_id+8|0)-B(_ge(_id-1|0,8))|0];break;case 10:var _io=E([0,_ib,_ic+1|0,1]);break;default:var _io=E([0,_ib,_ic,_id+1|0]);}var _ip=_io,_iq=[0,E(_ip),_9],_ir=[0,_im,E(_ip),E(_ie)];return new F(function(){return A(_if,[_in,_ir,_iq]);});}}}]);});},_is=function(_it,_iu){return E(_it)[1]!=E(_iu)[1];},_iv=function(_iw,_ix){return E(_iw)[1]==E(_ix)[1];},_iy=[0,_iv,_is],_iz=new T(function(){return B(unCStr(" 	"));}),_iA=function(_iB){return new F(function(){return _86(_iy,_iB,_iz);});},_iC=function(_iD,_iE){return E(_iE);},_iF=function(_iG){return new F(function(){return err(_iG);});},_iH=function(_iI){return E(_iI);},_iJ=[0,_g7,_iC,_iH,_iF],_iK=function(_iL){return E(E(_iL)[3]);},_iM=function(_iN,_iO){var _iP=E(_iO);return _iP[0]==0?B(A(_iK,[_iN,_28])):B(A(_iK,[_iN,[1,[0,_iP[1],_iP[2]]]]));},_iQ=function(_iR){return new F(function(){return _iM(_iJ,_iR);});},_iS=function(_iT,_iU,_iV,_iW,_iX){var _iY=E(_iT),_iZ=E(_iY[2]);return new F(function(){return _i6(_g7,_iQ,_iA,_iY[1],_iZ[1],_iZ[2],_iZ[3],_iY[3],_iU,_iX);});},_j0=function(_j1){return [0,_j1,function(_j2){return new F(function(){return _iM(_j1,_j2);});}];},_j3=new T(function(){return B(_j0(_iJ));}),_j4=function(_j5){return [2,E(E(_j5))];},_j6=function(_j7,_j8){switch(E(_j7)[0]){case 0:switch(E(_j8)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_j8)[0]==1?false:true;case 2:return E(_j8)[0]==2?false:true;default:return E(_j8)[0]==3?false:true;}},_j9=[2,E(_9)],_ja=function(_j2){return new F(function(){return _j6(_j9,_j2);});},_jb=function(_jc,_jd,_je){var _jf=E(_je);if(!_jf[0]){return [0,_jc,[1,_j9,new T(function(){return B(_7u(_ja,_jd));})]];}else{var _jg=_jf[1],_jh=E(_jf[2]);if(!_jh[0]){var _ji=new T(function(){return [2,E(E(_jg))];});return [0,_jc,[1,_ji,new T(function(){return B(_7u(function(_j2){return new F(function(){return _j6(_ji,_j2);});},_jd));})]];}else{var _jj=new T(function(){return [2,E(E(_jg))];}),_jk=function(_jl){var _jm=E(_jl);if(!_jm[0]){return [0,_jc,[1,_jj,new T(function(){return B(_7u(function(_j2){return new F(function(){return _j6(_jj,_j2);});},_jd));})]];}else{var _jn=B(_jk(_jm[2]));return [0,_jn[1],[1,new T(function(){return B(_j4(_jm[1]));}),_jn[2]]];}};return new F(function(){return (function(_jo,_jp){var _jq=B(_jk(_jp));return [0,_jq[1],[1,new T(function(){return B(_j4(_jo));}),_jq[2]]];})(_jh[1],_jh[2]);});}}},_jr=function(_js,_jt){var _ju=E(_js),_jv=B(_jb(_ju[1],_ju[2],_jt));return [0,E(_jv[1]),_jv[2]];},_jw=function(_jx,_jy,_jz,_jA,_jB,_jC,_jD){return new F(function(){return A(_jx,[_jz,_jA,_jB,function(_jE,_jF,_jG){return new F(function(){return A(_jC,[_jE,_jF,new T(function(){var _jH=E(_jG),_jI=E(_jH[2]);if(!_jI[0]){var _jJ=E(_jH);}else{var _jK=B(_jb(_jH[1],_jI,_jy)),_jJ=[0,E(_jK[1]),_jK[2]];}var _jL=_jJ;return _jL;})]);});},function(_jM){return new F(function(){return A(_jD,[new T(function(){return B(_jr(_jM,_jy));})]);});}]);});},_jN=function(_jO,_jP){return function(_jQ,_jR,_jS,_jT,_jU){return new F(function(){return _jw(function(_jV,_jW,_jX,_jY,_jZ){var _k0=E(_jO),_k1=E(_jV),_k2=E(_k1[2]);return new F(function(){return _i6(E(_k0[1])[1],_k0[2],function(_k3){return new F(function(){return _iv(_k3,_jP);});},_k1[1],_k2[1],_k2[2],_k2[3],_k1[3],_jW,_jZ);});},[1,[1,_ga,new T(function(){return B(_i0([1,_jP,_9],_gb));})],_9],_jQ,_jR,_jS,_jT,_jU);});};},_k4=[0,10],_k5=new T(function(){return B(unCStr("lf new-line"));}),_k6=[1,_k5,_9],_k7=function(_k8){return function(_k9,_ka,_kb,_kc,_kd){return new F(function(){return _jw(new T(function(){return B(_jN(_k8,_k4));}),_k6,_k9,_ka,_kb,_kc,_kd);});};},_ke=new T(function(){return B(_k7(_j3));}),_kf=new T(function(){return B(unCStr("digit"));}),_kg=[1,_kf,_9],_kh=function(_ki){return new F(function(){return _iM(_iJ,_ki);});},_kj=function(_kk){var _kl=E(_kk)[1];return _kl<48?false:_kl<=57;},_km=function(_kn,_ko,_kp,_kq,_kr){var _ks=E(_kn),_kt=E(_ks[2]);return new F(function(){return _i6(_g7,_kh,_kj,_ks[1],_kt[1],_kt[2],_kt[3],_ks[3],_ko,_kr);});},_ku=function(_kv,_kw,_kx,_ky,_kz){return new F(function(){return _jw(_km,_kg,_kv,_kw,_kx,_ky,_kz);});},_kA=function(_kB,_kC,_kD,_kE,_kF){return new F(function(){return _dT(_ku,_kB,_kC,_kD,_kE,_kF);});},_kG=new T(function(){return B(_j0(_iJ));}),_kH=[0,44],_kI=new T(function(){return B(_jN(_kG,_kH));}),_kJ=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_kK=new T(function(){return B(err(_kJ));}),_kL=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kM=new T(function(){return B(err(_kL));}),_kN=new T(function(){return B(_3B("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_kO=function(_kP,_kQ){while(1){var _kR=(function(_kS,_kT){var _kU=E(_kS);switch(_kU[0]){case 0:var _kV=E(_kT);if(!_kV[0]){return [0];}else{_kP=B(A(_kU[1],[_kV[1]]));_kQ=_kV[2];return null;}break;case 1:var _kW=B(A(_kU[1],[_kT])),_kX=_kT;_kP=_kW;_kQ=_kX;return null;case 2:return [0];case 3:return [1,[0,_kU[1],_kT],new T(function(){return B(_kO(_kU[2],_kT));})];default:return E(_kU[1]);}})(_kP,_kQ);if(_kR!=null){return _kR;}}},_kY=function(_kZ,_l0){var _l1=function(_l2){var _l3=E(_l0);if(_l3[0]==3){return [3,_l3[1],new T(function(){return B(_kY(_kZ,_l3[2]));})];}else{var _l4=E(_kZ);if(_l4[0]==2){return E(_l3);}else{var _l5=E(_l3);if(_l5[0]==2){return E(_l4);}else{var _l6=function(_l7){var _l8=E(_l5);if(_l8[0]==4){return [1,function(_l9){return [4,new T(function(){return B(_e(B(_kO(_l4,_l9)),_l8[1]));})];}];}else{var _la=E(_l4);if(_la[0]==1){var _lb=_la[1],_lc=E(_l8);return _lc[0]==0?[1,function(_ld){return new F(function(){return _kY(B(A(_lb,[_ld])),_lc);});}]:[1,function(_le){return new F(function(){return _kY(B(A(_lb,[_le])),new T(function(){return B(A(_lc[1],[_le]));}));});}];}else{var _lf=E(_l8);return _lf[0]==0?E(_kN):[1,function(_lg){return new F(function(){return _kY(_la,new T(function(){return B(A(_lf[1],[_lg]));}));});}];}}},_lh=E(_l4);switch(_lh[0]){case 1:var _li=E(_l5);if(_li[0]==4){return [1,function(_lj){return [4,new T(function(){return B(_e(B(_kO(B(A(_lh[1],[_lj])),_lj)),_li[1]));})];}];}else{return new F(function(){return _l6(_);});}break;case 4:var _lk=_lh[1],_ll=E(_l5);switch(_ll[0]){case 0:return [1,function(_lm){return [4,new T(function(){return B(_e(_lk,new T(function(){return B(_kO(_ll,_lm));},1)));})];}];case 1:return [1,function(_ln){return [4,new T(function(){return B(_e(_lk,new T(function(){return B(_kO(B(A(_ll[1],[_ln])),_ln));},1)));})];}];default:return [4,new T(function(){return B(_e(_lk,_ll[1]));})];}break;default:return new F(function(){return _l6(_);});}}}}},_lo=E(_kZ);switch(_lo[0]){case 0:var _lp=E(_l0);if(!_lp[0]){return [0,function(_lq){return new F(function(){return _kY(B(A(_lo[1],[_lq])),new T(function(){return B(A(_lp[1],[_lq]));}));});}];}else{return new F(function(){return _l1(_);});}break;case 3:return [3,_lo[1],new T(function(){return B(_kY(_lo[2],_l0));})];default:return new F(function(){return _l1(_);});}},_lr=[0,41],_ls=[1,_lr,_9],_lt=[0,40],_lu=[1,_lt,_9],_lv=function(_lw,_lx){while(1){var _ly=E(_lw);if(!_ly[0]){return E(_lx)[0]==0?true:false;}else{var _lz=E(_lx);if(!_lz[0]){return false;}else{if(E(_ly[1])[1]!=E(_lz[1])[1]){return false;}else{_lw=_ly[2];_lx=_lz[2];continue;}}}}},_lA=function(_lB,_lC){var _lD=E(_lB);switch(_lD[0]){case 0:return [0,function(_lE){return new F(function(){return _lA(B(A(_lD[1],[_lE])),_lC);});}];case 1:return [1,function(_lF){return new F(function(){return _lA(B(A(_lD[1],[_lF])),_lC);});}];case 2:return [2];case 3:return new F(function(){return _kY(B(A(_lC,[_lD[1]])),new T(function(){return B(_lA(_lD[2],_lC));}));});break;default:var _lG=function(_lH){var _lI=E(_lH);if(!_lI[0]){return [0];}else{var _lJ=E(_lI[1]);return new F(function(){return _e(B(_kO(B(A(_lC,[_lJ[1]])),_lJ[2])),new T(function(){return B(_lG(_lI[2]));},1));});}},_lK=B(_lG(_lD[1]));return _lK[0]==0?[2]:[4,_lK];}},_lL=[2],_lM=function(_lN){return [3,_lN,_lL];},_lO=function(_lP,_lQ){var _lR=E(_lP);if(!_lR){return new F(function(){return A(_lQ,[_5c]);});}else{return [0,function(_lS){return E(new T(function(){return B(_lO(_lR-1|0,_lQ));}));}];}},_lT=function(_lU,_lV,_lW){return function(_lX){return new F(function(){return A(function(_lY,_lZ,_m0){while(1){var _m1=(function(_m2,_m3,_m4){var _m5=E(_m2);switch(_m5[0]){case 0:var _m6=E(_m3);if(!_m6[0]){return E(_lV);}else{_lY=B(A(_m5[1],[_m6[1]]));_lZ=_m6[2];var _m7=_m4+1|0;_m0=_m7;return null;}break;case 1:var _m8=B(A(_m5[1],[_m3])),_m9=_m3,_m7=_m4;_lY=_m8;_lZ=_m9;_m0=_m7;return null;case 2:return E(_lV);case 3:return function(_ma){return new F(function(){return _lO(_m4,function(_mb){return E(new T(function(){return B(_lA(_m5,_ma));}));});});};default:return function(_mc){return new F(function(){return _lA(_m5,_mc);});};}})(_lY,_lZ,_m0);if(_m1!=null){return _m1;}}},[new T(function(){return B(A(_lU,[_lM]));}),_lX,0,_lW]);});};},_md=function(_me){return new F(function(){return A(_me,[_9]);});},_mf=function(_mg,_mh){var _mi=function(_mj){var _mk=E(_mj);if(!_mk[0]){return E(_md);}else{var _ml=_mk[1];return !B(A(_mg,[_ml]))?E(_md):function(_mm){return [0,function(_mn){return E(new T(function(){return B(A(new T(function(){return B(_mi(_mk[2]));}),[function(_mo){return new F(function(){return A(_mm,[[1,_ml,_mo]]);});}]));}));}];};}};return function(_mp){return new F(function(){return A(_mi,[_mp,_mh]);});};},_mq=[6],_mr=new T(function(){return B(unCStr("valDig: Bad base"));}),_ms=new T(function(){return B(err(_mr));}),_mt=function(_mu,_mv){var _mw=function(_mx,_my){var _mz=E(_mx);if(!_mz[0]){return function(_mA){return new F(function(){return A(_mA,[new T(function(){return B(A(_my,[_9]));})]);});};}else{var _mB=E(_mz[1])[1],_mC=function(_mD){return function(_mE){return [0,function(_mF){return E(new T(function(){return B(A(new T(function(){return B(_mw(_mz[2],function(_mG){return new F(function(){return A(_my,[[1,_mD,_mG]]);});}));}),[_mE]));}));}];};};switch(E(E(_mu)[1])){case 8:if(48>_mB){return function(_mH){return new F(function(){return A(_mH,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>55){return function(_mI){return new F(function(){return A(_mI,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,_mB-48|0]);});}}break;case 10:if(48>_mB){return function(_mJ){return new F(function(){return A(_mJ,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>57){return function(_mK){return new F(function(){return A(_mK,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,_mB-48|0]);});}}break;case 16:if(48>_mB){if(97>_mB){if(65>_mB){return function(_mL){return new F(function(){return A(_mL,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mM){return new F(function(){return A(_mM,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{if(_mB>102){if(65>_mB){return function(_mN){return new F(function(){return A(_mN,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mO){return new F(function(){return A(_mO,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{return new F(function(){return _mC([0,(_mB-97|0)+10|0]);});}}}else{if(_mB>57){if(97>_mB){if(65>_mB){return function(_mP){return new F(function(){return A(_mP,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mQ){return new F(function(){return A(_mQ,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{if(_mB>102){if(65>_mB){return function(_mR){return new F(function(){return A(_mR,[new T(function(){return B(A(_my,[_9]));})]);});};}else{if(_mB>70){return function(_mS){return new F(function(){return A(_mS,[new T(function(){return B(A(_my,[_9]));})]);});};}else{return new F(function(){return _mC([0,(_mB-65|0)+10|0]);});}}}else{return new F(function(){return _mC([0,(_mB-97|0)+10|0]);});}}}else{return new F(function(){return _mC([0,_mB-48|0]);});}}break;default:return E(_ms);}}};return function(_mT){return new F(function(){return A(_mw,[_mT,_5q,function(_mU){var _mV=E(_mU);return _mV[0]==0?[2]:B(A(_mv,[_mV]));}]);});};},_mW=[0,10],_mX=[0,1],_mY=[0,2147483647],_mZ=function(_n0,_n1){while(1){var _n2=E(_n0);if(!_n2[0]){var _n3=_n2[1],_n4=E(_n1);if(!_n4[0]){var _n5=_n4[1],_n6=addC(_n3,_n5);if(!E(_n6[2])){return [0,_n6[1]];}else{_n0=[1,I_fromInt(_n3)];_n1=[1,I_fromInt(_n5)];continue;}}else{_n0=[1,I_fromInt(_n3)];_n1=_n4;continue;}}else{var _n7=E(_n1);if(!_n7[0]){_n0=_n2;_n1=[1,I_fromInt(_n7[1])];continue;}else{return [1,I_add(_n2[1],_n7[1])];}}}},_n8=new T(function(){return B(_mZ(_mY,_mX));}),_n9=function(_na){var _nb=E(_na);if(!_nb[0]){var _nc=E(_nb[1]);return _nc==(-2147483648)?E(_n8):[0, -_nc];}else{return [1,I_negate(_nb[1])];}},_nd=[0,10],_ne=[0,0],_nf=function(_ng){return [0,_ng];},_nh=function(_ni,_nj){while(1){var _nk=E(_ni);if(!_nk[0]){var _nl=_nk[1],_nm=E(_nj);if(!_nm[0]){var _nn=_nm[1];if(!(imul(_nl,_nn)|0)){return [0,imul(_nl,_nn)|0];}else{_ni=[1,I_fromInt(_nl)];_nj=[1,I_fromInt(_nn)];continue;}}else{_ni=[1,I_fromInt(_nl)];_nj=_nm;continue;}}else{var _no=E(_nj);if(!_no[0]){_ni=_nk;_nj=[1,I_fromInt(_no[1])];continue;}else{return [1,I_mul(_nk[1],_no[1])];}}}},_np=function(_nq,_nr,_ns){while(1){var _nt=E(_ns);if(!_nt[0]){return E(_nr);}else{var _nu=B(_mZ(B(_nh(_nr,_nq)),B(_nf(E(_nt[1])[1]))));_ns=_nt[2];_nr=_nu;continue;}}},_nv=function(_nw){var _nx=new T(function(){return B(_kY(B(_kY([0,function(_ny){return E(E(_ny)[1])==45?[1,B(_mt(_mW,function(_nz){return new F(function(){return A(_nw,[[1,new T(function(){return B(_n9(B(_np(_nd,_ne,_nz))));})]]);});}))]:[2];}],[0,function(_nA){return E(E(_nA)[1])==43?[1,B(_mt(_mW,function(_nB){return new F(function(){return A(_nw,[[1,new T(function(){return B(_np(_nd,_ne,_nB));})]]);});}))]:[2];}])),new T(function(){return [1,B(_mt(_mW,function(_nC){return new F(function(){return A(_nw,[[1,new T(function(){return B(_np(_nd,_ne,_nC));})]]);});}))];})));});return new F(function(){return _kY([0,function(_nD){return E(E(_nD)[1])==101?E(_nx):[2];}],[0,function(_nE){return E(E(_nE)[1])==69?E(_nx):[2];}]);});},_nF=function(_nG){return new F(function(){return A(_nG,[_28]);});},_nH=function(_nI){return new F(function(){return A(_nI,[_28]);});},_nJ=function(_nK){return function(_nL){return E(E(_nL)[1])==46?[1,B(_mt(_mW,function(_nM){return new F(function(){return A(_nK,[[1,_nM]]);});}))]:[2];};},_nN=function(_nO){return [0,B(_nJ(_nO))];},_nP=function(_nQ){return new F(function(){return _mt(_mW,function(_nR){return [1,B(_lT(_nN,_nF,function(_nS){return [1,B(_lT(_nv,_nH,function(_nT){return new F(function(){return A(_nQ,[[5,[1,_nR,_nS,_nT]]]);});}))];}))];});});},_nU=function(_nV){return [1,B(_nP(_nV))];},_nW=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_nX=function(_nY){return new F(function(){return _86(_iy,_nY,_nW);});},_nZ=[0,8],_o0=[0,16],_o1=function(_o2){var _o3=function(_o4){return new F(function(){return A(_o2,[[5,[0,_nZ,_o4]]]);});},_o5=function(_o6){return new F(function(){return A(_o2,[[5,[0,_o0,_o6]]]);});};return function(_o7){return E(E(_o7)[1])==48?E([0,function(_o8){switch(E(E(_o8)[1])){case 79:return [1,B(_mt(_nZ,_o3))];case 88:return [1,B(_mt(_o0,_o5))];case 111:return [1,B(_mt(_nZ,_o3))];case 120:return [1,B(_mt(_o0,_o5))];default:return [2];}}]):[2];};},_o9=function(_oa){return [0,B(_o1(_oa))];},_ob=true,_oc=function(_od){var _oe=new T(function(){return B(A(_od,[_nZ]));}),_of=new T(function(){return B(A(_od,[_o0]));});return function(_og){switch(E(E(_og)[1])){case 79:return E(_oe);case 88:return E(_of);case 111:return E(_oe);case 120:return E(_of);default:return [2];}};},_oh=function(_oi){return [0,B(_oc(_oi))];},_oj=[0,92],_ok=function(_ol){return new F(function(){return A(_ol,[_mW]);});},_om=function(_on){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_on,_9));}))));});},_oo=function(_op){var _oq=E(_op);return _oq[0]==0?E(_oq[1]):I_toInt(_oq[1]);},_or=function(_os,_ot){var _ou=E(_os);if(!_ou[0]){var _ov=_ou[1],_ow=E(_ot);return _ow[0]==0?_ov<=_ow[1]:I_compareInt(_ow[1],_ov)>=0;}else{var _ox=_ou[1],_oy=E(_ot);return _oy[0]==0?I_compareInt(_ox,_oy[1])<=0:I_compare(_ox,_oy[1])<=0;}},_oz=function(_oA){return [2];},_oB=function(_oC){var _oD=E(_oC);if(!_oD[0]){return E(_oz);}else{var _oE=_oD[1],_oF=E(_oD[2]);return _oF[0]==0?E(_oE):function(_oG){return new F(function(){return _kY(B(A(_oE,[_oG])),new T(function(){return B(A(new T(function(){return B(_oB(_oF));}),[_oG]));}));});};}},_oH=function(_oI){return [2];},_oJ=function(_oK,_oL){var _oM=function(_oN,_oO){var _oP=E(_oN);if(!_oP[0]){return function(_oQ){return new F(function(){return A(_oQ,[_oK]);});};}else{var _oR=E(_oO);return _oR[0]==0?E(_oH):E(_oP[1])[1]!=E(_oR[1])[1]?E(_oH):function(_oS){return [0,function(_oT){return E(new T(function(){return B(A(new T(function(){return B(_oM(_oP[2],_oR[2]));}),[_oS]));}));}];};}};return function(_oU){return new F(function(){return A(_oM,[_oK,_oU,_oL]);});};},_oV=new T(function(){return B(unCStr("SOH"));}),_oW=[0,1],_oX=function(_oY){return [1,B(_oJ(_oV,function(_oZ){return E(new T(function(){return B(A(_oY,[_oW]));}));}))];},_p0=new T(function(){return B(unCStr("SO"));}),_p1=[0,14],_p2=function(_p3){return [1,B(_oJ(_p0,function(_p4){return E(new T(function(){return B(A(_p3,[_p1]));}));}))];},_p5=function(_p6){return [1,B(_lT(_oX,_p2,_p6))];},_p7=new T(function(){return B(unCStr("NUL"));}),_p8=[0,0],_p9=function(_pa){return [1,B(_oJ(_p7,function(_pb){return E(new T(function(){return B(A(_pa,[_p8]));}));}))];},_pc=new T(function(){return B(unCStr("STX"));}),_pd=[0,2],_pe=function(_pf){return [1,B(_oJ(_pc,function(_pg){return E(new T(function(){return B(A(_pf,[_pd]));}));}))];},_ph=new T(function(){return B(unCStr("ETX"));}),_pi=[0,3],_pj=function(_pk){return [1,B(_oJ(_ph,function(_pl){return E(new T(function(){return B(A(_pk,[_pi]));}));}))];},_pm=new T(function(){return B(unCStr("EOT"));}),_pn=[0,4],_po=function(_pp){return [1,B(_oJ(_pm,function(_pq){return E(new T(function(){return B(A(_pp,[_pn]));}));}))];},_pr=new T(function(){return B(unCStr("ENQ"));}),_ps=[0,5],_pt=function(_pu){return [1,B(_oJ(_pr,function(_pv){return E(new T(function(){return B(A(_pu,[_ps]));}));}))];},_pw=new T(function(){return B(unCStr("ACK"));}),_px=[0,6],_py=function(_pz){return [1,B(_oJ(_pw,function(_pA){return E(new T(function(){return B(A(_pz,[_px]));}));}))];},_pB=new T(function(){return B(unCStr("BEL"));}),_pC=[0,7],_pD=function(_pE){return [1,B(_oJ(_pB,function(_pF){return E(new T(function(){return B(A(_pE,[_pC]));}));}))];},_pG=new T(function(){return B(unCStr("BS"));}),_pH=[0,8],_pI=function(_pJ){return [1,B(_oJ(_pG,function(_pK){return E(new T(function(){return B(A(_pJ,[_pH]));}));}))];},_pL=new T(function(){return B(unCStr("HT"));}),_pM=[0,9],_pN=function(_pO){return [1,B(_oJ(_pL,function(_pP){return E(new T(function(){return B(A(_pO,[_pM]));}));}))];},_pQ=new T(function(){return B(unCStr("LF"));}),_pR=[0,10],_pS=function(_pT){return [1,B(_oJ(_pQ,function(_pU){return E(new T(function(){return B(A(_pT,[_pR]));}));}))];},_pV=new T(function(){return B(unCStr("VT"));}),_pW=[0,11],_pX=function(_pY){return [1,B(_oJ(_pV,function(_pZ){return E(new T(function(){return B(A(_pY,[_pW]));}));}))];},_q0=new T(function(){return B(unCStr("FF"));}),_q1=[0,12],_q2=function(_q3){return [1,B(_oJ(_q0,function(_q4){return E(new T(function(){return B(A(_q3,[_q1]));}));}))];},_q5=new T(function(){return B(unCStr("CR"));}),_q6=[0,13],_q7=function(_q8){return [1,B(_oJ(_q5,function(_q9){return E(new T(function(){return B(A(_q8,[_q6]));}));}))];},_qa=new T(function(){return B(unCStr("SI"));}),_qb=[0,15],_qc=function(_qd){return [1,B(_oJ(_qa,function(_qe){return E(new T(function(){return B(A(_qd,[_qb]));}));}))];},_qf=new T(function(){return B(unCStr("DLE"));}),_qg=[0,16],_qh=function(_qi){return [1,B(_oJ(_qf,function(_qj){return E(new T(function(){return B(A(_qi,[_qg]));}));}))];},_qk=new T(function(){return B(unCStr("DC1"));}),_ql=[0,17],_qm=function(_qn){return [1,B(_oJ(_qk,function(_qo){return E(new T(function(){return B(A(_qn,[_ql]));}));}))];},_qp=new T(function(){return B(unCStr("DC2"));}),_qq=[0,18],_qr=function(_qs){return [1,B(_oJ(_qp,function(_qt){return E(new T(function(){return B(A(_qs,[_qq]));}));}))];},_qu=new T(function(){return B(unCStr("DC3"));}),_qv=[0,19],_qw=function(_qx){return [1,B(_oJ(_qu,function(_qy){return E(new T(function(){return B(A(_qx,[_qv]));}));}))];},_qz=new T(function(){return B(unCStr("DC4"));}),_qA=[0,20],_qB=function(_qC){return [1,B(_oJ(_qz,function(_qD){return E(new T(function(){return B(A(_qC,[_qA]));}));}))];},_qE=new T(function(){return B(unCStr("NAK"));}),_qF=[0,21],_qG=function(_qH){return [1,B(_oJ(_qE,function(_qI){return E(new T(function(){return B(A(_qH,[_qF]));}));}))];},_qJ=new T(function(){return B(unCStr("SYN"));}),_qK=[0,22],_qL=function(_qM){return [1,B(_oJ(_qJ,function(_qN){return E(new T(function(){return B(A(_qM,[_qK]));}));}))];},_qO=new T(function(){return B(unCStr("ETB"));}),_qP=[0,23],_qQ=function(_qR){return [1,B(_oJ(_qO,function(_qS){return E(new T(function(){return B(A(_qR,[_qP]));}));}))];},_qT=new T(function(){return B(unCStr("CAN"));}),_qU=[0,24],_qV=function(_qW){return [1,B(_oJ(_qT,function(_qX){return E(new T(function(){return B(A(_qW,[_qU]));}));}))];},_qY=new T(function(){return B(unCStr("EM"));}),_qZ=[0,25],_r0=function(_r1){return [1,B(_oJ(_qY,function(_r2){return E(new T(function(){return B(A(_r1,[_qZ]));}));}))];},_r3=new T(function(){return B(unCStr("SUB"));}),_r4=[0,26],_r5=function(_r6){return [1,B(_oJ(_r3,function(_r7){return E(new T(function(){return B(A(_r6,[_r4]));}));}))];},_r8=new T(function(){return B(unCStr("ESC"));}),_r9=[0,27],_ra=function(_rb){return [1,B(_oJ(_r8,function(_rc){return E(new T(function(){return B(A(_rb,[_r9]));}));}))];},_rd=new T(function(){return B(unCStr("FS"));}),_re=[0,28],_rf=function(_rg){return [1,B(_oJ(_rd,function(_rh){return E(new T(function(){return B(A(_rg,[_re]));}));}))];},_ri=new T(function(){return B(unCStr("GS"));}),_rj=[0,29],_rk=function(_rl){return [1,B(_oJ(_ri,function(_rm){return E(new T(function(){return B(A(_rl,[_rj]));}));}))];},_rn=new T(function(){return B(unCStr("RS"));}),_ro=[0,30],_rp=function(_rq){return [1,B(_oJ(_rn,function(_rr){return E(new T(function(){return B(A(_rq,[_ro]));}));}))];},_rs=new T(function(){return B(unCStr("US"));}),_rt=[0,31],_ru=function(_rv){return [1,B(_oJ(_rs,function(_rw){return E(new T(function(){return B(A(_rv,[_rt]));}));}))];},_rx=new T(function(){return B(unCStr("SP"));}),_ry=[0,32],_rz=function(_rA){return [1,B(_oJ(_rx,function(_rB){return E(new T(function(){return B(A(_rA,[_ry]));}));}))];},_rC=new T(function(){return B(unCStr("DEL"));}),_rD=[0,127],_rE=function(_rF){return [1,B(_oJ(_rC,function(_rG){return E(new T(function(){return B(A(_rF,[_rD]));}));}))];},_rH=[1,_rE,_9],_rI=[1,_rz,_rH],_rJ=[1,_ru,_rI],_rK=[1,_rp,_rJ],_rL=[1,_rk,_rK],_rM=[1,_rf,_rL],_rN=[1,_ra,_rM],_rO=[1,_r5,_rN],_rP=[1,_r0,_rO],_rQ=[1,_qV,_rP],_rR=[1,_qQ,_rQ],_rS=[1,_qL,_rR],_rT=[1,_qG,_rS],_rU=[1,_qB,_rT],_rV=[1,_qw,_rU],_rW=[1,_qr,_rV],_rX=[1,_qm,_rW],_rY=[1,_qh,_rX],_rZ=[1,_qc,_rY],_s0=[1,_q7,_rZ],_s1=[1,_q2,_s0],_s2=[1,_pX,_s1],_s3=[1,_pS,_s2],_s4=[1,_pN,_s3],_s5=[1,_pI,_s4],_s6=[1,_pD,_s5],_s7=[1,_py,_s6],_s8=[1,_pt,_s7],_s9=[1,_po,_s8],_sa=[1,_pj,_s9],_sb=[1,_pe,_sa],_sc=[1,_p9,_sb],_sd=[1,_p5,_sc],_se=new T(function(){return B(_oB(_sd));}),_sf=[0,1114111],_sg=[0,34],_sh=[0,39],_si=function(_sj){var _sk=new T(function(){return B(A(_sj,[_pC]));}),_sl=new T(function(){return B(A(_sj,[_pH]));}),_sm=new T(function(){return B(A(_sj,[_pM]));}),_sn=new T(function(){return B(A(_sj,[_pR]));}),_so=new T(function(){return B(A(_sj,[_pW]));}),_sp=new T(function(){return B(A(_sj,[_q1]));}),_sq=new T(function(){return B(A(_sj,[_q6]));});return new F(function(){return _kY([0,function(_sr){switch(E(E(_sr)[1])){case 34:return E(new T(function(){return B(A(_sj,[_sg]));}));case 39:return E(new T(function(){return B(A(_sj,[_sh]));}));case 92:return E(new T(function(){return B(A(_sj,[_oj]));}));case 97:return E(_sk);case 98:return E(_sl);case 102:return E(_sp);case 110:return E(_sn);case 114:return E(_sq);case 116:return E(_sm);case 118:return E(_so);default:return [2];}}],new T(function(){return B(_kY([1,B(_lT(_oh,_ok,function(_ss){return [1,B(_mt(_ss,function(_st){var _su=B(_np(new T(function(){return B(_nf(E(_ss)[1]));}),_ne,_st));return !B(_or(_su,_sf))?[2]:B(A(_sj,[new T(function(){var _sv=B(_oo(_su));if(_sv>>>0>1114111){var _sw=B(_om(_sv));}else{var _sw=[0,_sv];}var _sx=_sw,_sy=_sx,_sz=_sy;return _sz;})]));}))];}))],new T(function(){return B(_kY([0,function(_sA){return E(E(_sA)[1])==94?E([0,function(_sB){switch(E(E(_sB)[1])){case 64:return E(new T(function(){return B(A(_sj,[_p8]));}));case 65:return E(new T(function(){return B(A(_sj,[_oW]));}));case 66:return E(new T(function(){return B(A(_sj,[_pd]));}));case 67:return E(new T(function(){return B(A(_sj,[_pi]));}));case 68:return E(new T(function(){return B(A(_sj,[_pn]));}));case 69:return E(new T(function(){return B(A(_sj,[_ps]));}));case 70:return E(new T(function(){return B(A(_sj,[_px]));}));case 71:return E(_sk);case 72:return E(_sl);case 73:return E(_sm);case 74:return E(_sn);case 75:return E(_so);case 76:return E(_sp);case 77:return E(_sq);case 78:return E(new T(function(){return B(A(_sj,[_p1]));}));case 79:return E(new T(function(){return B(A(_sj,[_qb]));}));case 80:return E(new T(function(){return B(A(_sj,[_qg]));}));case 81:return E(new T(function(){return B(A(_sj,[_ql]));}));case 82:return E(new T(function(){return B(A(_sj,[_qq]));}));case 83:return E(new T(function(){return B(A(_sj,[_qv]));}));case 84:return E(new T(function(){return B(A(_sj,[_qA]));}));case 85:return E(new T(function(){return B(A(_sj,[_qF]));}));case 86:return E(new T(function(){return B(A(_sj,[_qK]));}));case 87:return E(new T(function(){return B(A(_sj,[_qP]));}));case 88:return E(new T(function(){return B(A(_sj,[_qU]));}));case 89:return E(new T(function(){return B(A(_sj,[_qZ]));}));case 90:return E(new T(function(){return B(A(_sj,[_r4]));}));case 91:return E(new T(function(){return B(A(_sj,[_r9]));}));case 92:return E(new T(function(){return B(A(_sj,[_re]));}));case 93:return E(new T(function(){return B(A(_sj,[_rj]));}));case 94:return E(new T(function(){return B(A(_sj,[_ro]));}));case 95:return E(new T(function(){return B(A(_sj,[_rt]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_se,[_sj]));})));})));}));});},_sC=function(_sD){return new F(function(){return A(_sD,[_5c]);});},_sE=function(_sF){var _sG=E(_sF);if(!_sG[0]){return E(_sC);}else{var _sH=_sG[2],_sI=E(E(_sG[1])[1]);switch(_sI){case 9:return function(_sJ){return [0,function(_sK){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sJ]));}));}];};case 10:return function(_sL){return [0,function(_sM){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sL]));}));}];};case 11:return function(_sN){return [0,function(_sO){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sN]));}));}];};case 12:return function(_sP){return [0,function(_sQ){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sP]));}));}];};case 13:return function(_sR){return [0,function(_sS){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sR]));}));}];};case 32:return function(_sT){return [0,function(_sU){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sT]));}));}];};case 160:return function(_sV){return [0,function(_sW){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sV]));}));}];};default:var _sX=u_iswspace(_sI),_sY=_sX;return E(_sY)==0?E(_sC):function(_sZ){return [0,function(_t0){return E(new T(function(){return B(A(new T(function(){return B(_sE(_sH));}),[_sZ]));}));}];};}}},_t1=function(_t2){var _t3=new T(function(){return B(_t1(_t2));}),_t4=[1,function(_t5){return new F(function(){return A(_sE,[_t5,function(_t6){return E([0,function(_t7){return E(E(_t7)[1])==92?E(_t3):[2];}]);}]);});}];return new F(function(){return _kY([0,function(_t8){return E(E(_t8)[1])==92?E([0,function(_t9){var _ta=E(E(_t9)[1]);switch(_ta){case 9:return E(_t4);case 10:return E(_t4);case 11:return E(_t4);case 12:return E(_t4);case 13:return E(_t4);case 32:return E(_t4);case 38:return E(_t3);case 160:return E(_t4);default:var _tb=u_iswspace(_ta),_tc=_tb;return E(_tc)==0?[2]:E(_t4);}}]):[2];}],[0,function(_td){var _te=E(_td);return E(_te[1])==92?E(new T(function(){return B(_si(function(_tf){return new F(function(){return A(_t2,[[0,_tf,_ob]]);});}));})):B(A(_t2,[[0,_te,_1S]]));}]);});},_tg=function(_th,_ti){return new F(function(){return _t1(function(_tj){var _tk=E(_tj),_tl=E(_tk[1]);if(E(_tl[1])==34){if(!E(_tk[2])){return E(new T(function(){return B(A(_ti,[[1,new T(function(){return B(A(_th,[_9]));})]]));}));}else{return new F(function(){return _tg(function(_tm){return new F(function(){return A(_th,[[1,_tl,_tm]]);});},_ti);});}}else{return new F(function(){return _tg(function(_tn){return new F(function(){return A(_th,[[1,_tl,_tn]]);});},_ti);});}});});},_to=new T(function(){return B(unCStr("_\'"));}),_tp=function(_tq){var _tr=u_iswalnum(_tq),_ts=_tr;return E(_ts)==0?B(_86(_iy,[0,_tq],_to)):true;},_tt=function(_tu){return new F(function(){return _tp(E(_tu)[1]);});},_tv=new T(function(){return B(unCStr(",;()[]{}`"));}),_tw=new T(function(){return B(unCStr(".."));}),_tx=new T(function(){return B(unCStr("::"));}),_ty=new T(function(){return B(unCStr("->"));}),_tz=[0,64],_tA=[1,_tz,_9],_tB=[0,126],_tC=[1,_tB,_9],_tD=new T(function(){return B(unCStr("=>"));}),_tE=[1,_tD,_9],_tF=[1,_tC,_tE],_tG=[1,_tA,_tF],_tH=[1,_ty,_tG],_tI=new T(function(){return B(unCStr("<-"));}),_tJ=[1,_tI,_tH],_tK=[0,124],_tL=[1,_tK,_9],_tM=[1,_tL,_tJ],_tN=[1,_oj,_9],_tO=[1,_tN,_tM],_tP=[0,61],_tQ=[1,_tP,_9],_tR=[1,_tQ,_tO],_tS=[1,_tx,_tR],_tT=[1,_tw,_tS],_tU=function(_tV){return new F(function(){return _kY([1,function(_tW){return E(_tW)[0]==0?E(new T(function(){return B(A(_tV,[_mq]));})):[2];}],new T(function(){return B(_kY([0,function(_tX){return E(E(_tX)[1])==39?E([0,function(_tY){var _tZ=E(_tY);switch(E(_tZ[1])){case 39:return [2];case 92:return E(new T(function(){return B(_si(function(_u0){return [0,function(_u1){return E(E(_u1)[1])==39?E(new T(function(){return B(A(_tV,[[0,_u0]]));})):[2];}];}));}));default:return [0,function(_u2){return E(E(_u2)[1])==39?E(new T(function(){return B(A(_tV,[[0,_tZ]]));})):[2];}];}}]):[2];}],new T(function(){return B(_kY([0,function(_u3){return E(E(_u3)[1])==34?E(new T(function(){return B(_tg(_5q,_tV));})):[2];}],new T(function(){return B(_kY([0,function(_u4){return !B(_86(_iy,_u4,_tv))?[2]:B(A(_tV,[[2,[1,_u4,_9]]]));}],new T(function(){return B(_kY([0,function(_u5){return !B(_86(_iy,_u5,_nW))?[2]:[1,B(_mf(_nX,function(_u6){var _u7=[1,_u5,_u6];return !B(_86(_7i,_u7,_tT))?B(A(_tV,[[4,_u7]])):B(A(_tV,[[2,_u7]]));}))];}],new T(function(){return B(_kY([0,function(_u8){var _u9=E(_u8),_ua=_u9[1],_ub=u_iswalpha(_ua),_uc=_ub;return E(_uc)==0?E(_ua)==95?[1,B(_mf(_tt,function(_ud){return new F(function(){return A(_tV,[[3,[1,_u9,_ud]]]);});}))]:[2]:[1,B(_mf(_tt,function(_ue){return new F(function(){return A(_tV,[[3,[1,_u9,_ue]]]);});}))];}],new T(function(){return [1,B(_lT(_o9,_nU,_tV))];})));})));})));})));})));}));});},_uf=[0,0],_ug=function(_uh,_ui){return function(_uj){return new F(function(){return A(_sE,[_uj,function(_uk){return E(new T(function(){return B(_tU(function(_ul){var _um=E(_ul);return _um[0]==2?!B(_lv(_um[1],_lu))?[2]:E(new T(function(){return B(A(_uh,[_uf,function(_un){return [1,function(_uo){return new F(function(){return A(_sE,[_uo,function(_up){return E(new T(function(){return B(_tU(function(_uq){var _ur=E(_uq);return _ur[0]==2?!B(_lv(_ur[1],_ls))?[2]:E(new T(function(){return B(A(_ui,[_un]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_us=function(_ut,_uu,_uv){var _uw=function(_ux,_uy){return new F(function(){return _kY([1,function(_uz){return new F(function(){return A(_sE,[_uz,function(_uA){return E(new T(function(){return B(_tU(function(_uB){var _uC=E(_uB);if(_uC[0]==4){var _uD=E(_uC[1]);if(!_uD[0]){return new F(function(){return A(_ut,[_uC,_ux,_uy]);});}else{return E(E(_uD[1])[1])==45?E(_uD[2])[0]==0?E([1,function(_uE){return new F(function(){return A(_sE,[_uE,function(_uF){return E(new T(function(){return B(_tU(function(_uG){return new F(function(){return A(_ut,[_uG,_ux,function(_uH){return new F(function(){return A(_uy,[new T(function(){return [0, -E(_uH)[1]];})]);});}]);});}));}));}]);});}]):B(A(_ut,[_uC,_ux,_uy])):B(A(_ut,[_uC,_ux,_uy]));}}else{return new F(function(){return A(_ut,[_uC,_ux,_uy]);});}}));}));}]);});}],new T(function(){return [1,B(_ug(_uw,_uy))];}));});};return new F(function(){return _uw(_uu,_uv);});},_uI=function(_uJ,_uK){return [2];},_uL=function(_uM){var _uN=E(_uM);return _uN[0]==0?[1,new T(function(){return B(_np(new T(function(){return B(_nf(E(_uN[1])[1]));}),_ne,_uN[2]));})]:E(_uN[2])[0]==0?E(_uN[3])[0]==0?[1,new T(function(){return B(_np(_nd,_ne,_uN[1]));})]:[0]:[0];},_uO=function(_uP){var _uQ=E(_uP);if(_uQ[0]==5){var _uR=B(_uL(_uQ[1]));return _uR[0]==0?E(_uI):function(_uS,_uT){return new F(function(){return A(_uT,[new T(function(){return [0,B(_oo(_uR[1]))];})]);});};}else{return E(_uI);}},_uU=function(_uV){return [1,function(_uW){return new F(function(){return A(_sE,[_uW,function(_uX){return E([3,_uV,_lL]);}]);});}];},_uY=new T(function(){return B(_us(_uO,_uf,_uU));}),_uZ=function(_v0){while(1){var _v1=(function(_v2){var _v3=E(_v2);if(!_v3[0]){return [0];}else{var _v4=_v3[2],_v5=E(_v3[1]);if(!E(_v5[2])[0]){return [1,_v5[1],new T(function(){return B(_uZ(_v4));})];}else{_v0=_v4;return null;}}})(_v0);if(_v1!=null){return _v1;}}},_v6=function(_v7){var _v8=B(_uZ(B(_kO(_uY,_v7))));return _v8[0]==0?E(_kK):E(_v8[2])[0]==0?E(_v8[1]):E(_kM);},_v9=function(_va,_vb,_vc,_vd,_ve,_vf){var _vg=function(_vh){var _vi=[0,_va,new T(function(){return B(_7X(_v6,_vh));})];return function(_vj,_vk,_vl,_vm,_vn){return new F(function(){return A(_ke,[_vj,function(_vo,_vp,_vq){return new F(function(){return A(_vk,[_vi,_vp,new T(function(){var _vr=E(E(_vp)[2]),_vs=E(_vq),_vt=E(_vs[1]),_vu=B(_cW(_vt[1],_vt[2],_vt[3],_vs[2],_vr[1],_vr[2],_vr[3],_9));return [0,E(_vu[1]),_vu[2]];})]);});},_vn,function(_vv,_vw,_vx){return new F(function(){return A(_vm,[_vi,_vw,new T(function(){var _vy=E(E(_vw)[2]),_vz=E(_vx),_vA=E(_vz[1]),_vB=B(_cW(_vA[1],_vA[2],_vA[3],_vz[2],_vy[1],_vy[2],_vy[3],_9));return [0,E(_vB[1]),_vB[2]];})]);});},_vn]);});};},_vC=function(_vD,_vE,_vF,_vG,_vH){var _vI=function(_vJ,_vK,_vL){return new F(function(){return A(_vg,[_vJ,_vK,_vE,_vF,function(_vM,_vN,_vO){return new F(function(){return A(_vG,[_vM,_vN,new T(function(){return B(_dL(_vL,_vO));})]);});},function(_vP){return new F(function(){return A(_vH,[new T(function(){return B(_dL(_vL,_vP));})]);});}]);});},_vQ=function(_vR){return new F(function(){return _vI(_9,_vD,new T(function(){var _vS=E(E(_vD)[2]),_vT=E(_vR),_vU=E(_vT[1]),_vV=B(_cW(_vU[1],_vU[2],_vU[3],_vT[2],_vS[1],_vS[2],_vS[3],_9));return [0,E(_vV[1]),_vV[2]];}));});};return new F(function(){return _eW(_kA,_kI,_vD,function(_vW,_vX,_vY){return new F(function(){return A(_vg,[_vW,_vX,_vE,_vF,function(_vZ,_w0,_w1){return new F(function(){return A(_vE,[_vZ,_w0,new T(function(){return B(_dL(_vY,_w1));})]);});},function(_w2){return new F(function(){return A(_vF,[new T(function(){return B(_dL(_vY,_w2));})]);});}]);});},_vQ,_vI,_vQ);});};return new F(function(){return _ew(_iS,_vb,function(_w3,_w4,_w5){return new F(function(){return _vC(_w4,_vc,_vd,function(_w6,_w7,_w8){return new F(function(){return A(_vc,[_w6,_w7,new T(function(){return B(_dL(_w5,_w8));})]);});},function(_w9){return new F(function(){return A(_vd,[new T(function(){return B(_dL(_w5,_w9));})]);});});});},_vd,function(_wa,_wb,_wc){return new F(function(){return _vC(_wb,_vc,_vd,function(_wd,_we,_wf){return new F(function(){return A(_ve,[_wd,_we,new T(function(){return B(_dL(_wc,_wf));})]);});},function(_wg){return new F(function(){return A(_vf,[new T(function(){return B(_dL(_wc,_wg));})]);});});});});});},_wh=new T(function(){return B(unCStr("letter or digit"));}),_wi=[1,_wh,_9],_wj=function(_wk){var _wl=u_iswalnum(E(_wk)[1]),_wm=_wl;return E(_wm)==0?false:true;},_wn=function(_wo,_wp,_wq,_wr,_ws){var _wt=E(_wo),_wu=E(_wt[2]);return new F(function(){return _i6(_g7,_kh,_wj,_wt[1],_wu[1],_wu[2],_wu[3],_wt[3],_wp,_ws);});},_wv=function(_ww,_wx,_wy,_wz,_wA){return new F(function(){return _jw(_wn,_wi,_ww,_wx,_wy,_wz,_wA);});},_wB=function(_wC,_wD,_wE,_wF,_wG){return new F(function(){return _dT(_wv,_wC,function(_wH,_wI,_wJ){return new F(function(){return _v9(_wH,_wI,_wD,_wE,function(_wK,_wL,_wM){return new F(function(){return A(_wD,[_wK,_wL,new T(function(){return B(_dL(_wJ,_wM));})]);});},function(_wN){return new F(function(){return A(_wE,[new T(function(){return B(_dL(_wJ,_wN));})]);});});});},_wG,function(_wO,_wP,_wQ){return new F(function(){return _v9(_wO,_wP,_wD,_wE,function(_wR,_wS,_wT){return new F(function(){return A(_wF,[_wR,_wS,new T(function(){return B(_dL(_wQ,_wT));})]);});},function(_wU){return new F(function(){return A(_wG,[new T(function(){return B(_dL(_wQ,_wU));})]);});});});},_wG);});},_wV=new T(function(){return B(unCStr("SHOW"));}),_wW=[0,_wV,_9],_wX=function(_wY,_wZ,_x0,_x1){var _x2=function(_x3){return new F(function(){return A(_x1,[[0,_wY,_wW],_wZ,new T(function(){var _x4=E(E(_wZ)[2]),_x5=_x4[1],_x6=_x4[2],_x7=_x4[3],_x8=E(_x3),_x9=E(_x8[1]),_xa=B(_cW(_x9[1],_x9[2],_x9[3],_x8[2],_x5,_x6,_x7,_9)),_xb=E(_xa[1]),_xc=B(_cW(_xb[1],_xb[2],_xb[3],_xa[2],_x5,_x6,_x7,_9));return [0,E(_xc[1]),_xc[2]];})]);});};return new F(function(){return _wB(_wZ,function(_xd,_xe,_xf){return new F(function(){return A(_x0,[[0,_wY,_xd],_xe,new T(function(){var _xg=E(E(_xe)[2]),_xh=E(_xf),_xi=E(_xh[1]),_xj=B(_cW(_xi[1],_xi[2],_xi[3],_xh[2],_xg[1],_xg[2],_xg[3],_9));return [0,E(_xj[1]),_xj[2]];})]);});},_x2,function(_xk,_xl,_xm){return new F(function(){return A(_x1,[[0,_wY,_xk],_xl,new T(function(){var _xn=E(E(_xl)[2]),_xo=E(_xm),_xp=E(_xo[1]),_xq=B(_cW(_xp[1],_xp[2],_xp[3],_xo[2],_xn[1],_xn[2],_xn[3],_9));return [0,E(_xq[1]),_xq[2]];})]);});},_x2);});},_xr=new T(function(){return B(unCStr("sS"));}),_xs=[0,58],_xt=new T(function(){return B(_jN(_j3,_xs));}),_xu=[1,_wh,_9],_xv=function(_xw,_xx,_xy,_xz,_xA,_xB,_xC,_xD,_xE){var _xF=function(_xG,_xH){var _xI=new T(function(){var _xJ=B(_jb(_xG,_xH,_xu));return [0,E(_xJ[1]),_xJ[2]];});return new F(function(){return A(_xt,[[0,_xw,E([0,_xx,_xy,_xz]),E(_xA)],_xB,_xC,function(_xK,_xL,_xM){return new F(function(){return A(_xD,[_xK,_xL,new T(function(){return B(_dL(_xI,_xM));})]);});},function(_xN){return new F(function(){return A(_xE,[new T(function(){return B(_dL(_xI,_xN));})]);});}]);});},_xO=E(_xw);if(!_xO[0]){return new F(function(){return _xF([0,_xx,_xy,_xz],_gd);});}else{var _xP=_xO[2],_xQ=E(_xO[1]),_xR=_xQ[1],_xS=u_iswalnum(_xR),_xT=_xS;if(!E(_xT)){return new F(function(){return _xF([0,_xx,_xy,_xz],[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_xQ,_9],_gb));})])],_9]);});}else{switch(E(_xR)){case 9:var _xU=[0,_xx,_xy,(_xz+8|0)-B(_ge(_xz-1|0,8))|0];break;case 10:var _xU=[0,_xx,_xy+1|0,1];break;default:var _xU=[0,_xx,_xy,_xz+1|0];}var _xV=_xU,_xW=[0,E(_xV),_9],_xX=[0,_xP,E(_xV),E(_xA)];return new F(function(){return A(_xB,[_xQ,_xX,_xW]);});}}},_xY=function(_xZ,_y0,_y1,_y2,_y3){var _y4=E(_xZ),_y5=E(_y4[2]);return new F(function(){return _xv(_y4[1],_y5[1],_y5[2],_y5[3],_y4[3],_y0,_y1,_y2,_y3);});},_y6=function(_y7,_y8,_y9,_ya,_yb,_yc,_yd){var _ye=function(_yf,_yg,_yh,_yi,_yj,_yk){return new F(function(){return _yl(_yg,function(_ym,_yn,_yo){return new F(function(){return A(_yh,[[1,_yf,_ym],_yn,new T(function(){var _yp=E(E(_yn)[2]),_yq=E(_yo),_yr=E(_yq[1]),_ys=B(_cW(_yr[1],_yr[2],_yr[3],_yq[2],_yp[1],_yp[2],_yp[3],_9));return [0,E(_ys[1]),_ys[2]];})]);});},_yi,function(_yt,_yu,_yv){return new F(function(){return A(_yj,[[1,_yf,_yt],_yu,new T(function(){var _yw=E(E(_yu)[2]),_yx=E(_yv),_yy=E(_yx[1]),_yz=B(_cW(_yy[1],_yy[2],_yy[3],_yx[2],_yw[1],_yw[2],_yw[3],_9));return [0,E(_yz[1]),_yz[2]];})]);});},_yk);});},_yl=function(_yA,_yB,_yC,_yD,_yE){return new F(function(){return A(_y8,[_yA,function(_yF,_yG,_yH){return new F(function(){return A(_yB,[_9,_yG,new T(function(){var _yI=E(E(_yG)[2]),_yJ=E(_yH),_yK=E(_yJ[1]),_yL=B(_cW(_yK[1],_yK[2],_yK[3],_yJ[2],_yI[1],_yI[2],_yI[3],_9));return [0,E(_yL[1]),_yL[2]];})]);});},_yC,function(_yM,_yN,_yO){return new F(function(){return A(_yD,[_9,_yN,new T(function(){var _yP=E(E(_yN)[2]),_yQ=E(_yO),_yR=E(_yQ[1]),_yS=B(_cW(_yR[1],_yR[2],_yR[3],_yQ[2],_yP[1],_yP[2],_yP[3],_9));return [0,E(_yS[1]),_yS[2]];})]);});},function(_yT){return new F(function(){return A(_y7,[_yA,function(_yU,_yV,_yW){return new F(function(){return _ye(_yU,_yV,_yB,_yC,function(_yX,_yY,_yZ){return new F(function(){return A(_yB,[_yX,_yY,new T(function(){return B(_dL(_yW,_yZ));})]);});},function(_z0){return new F(function(){return A(_yC,[new T(function(){return B(_dL(_yW,_z0));})]);});});});},_yC,function(_z1,_z2,_z3){return new F(function(){return _ye(_z1,_z2,_yB,_yC,function(_z4,_z5,_z6){return new F(function(){return A(_yD,[_z4,_z5,new T(function(){var _z7=E(_yT),_z8=E(_z7[1]),_z9=E(_z3),_za=E(_z9[1]),_zb=E(_z6),_zc=E(_zb[1]),_zd=B(_cW(_za[1],_za[2],_za[3],_z9[2],_zc[1],_zc[2],_zc[3],_zb[2])),_ze=E(_zd[1]),_zf=B(_cW(_z8[1],_z8[2],_z8[3],_z7[2],_ze[1],_ze[2],_ze[3],_zd[2]));return [0,E(_zf[1]),_zf[2]];})]);});},function(_zg){return new F(function(){return A(_yE,[new T(function(){var _zh=E(_yT),_zi=E(_zh[1]),_zj=E(_z3),_zk=E(_zj[1]),_zl=E(_zg),_zm=E(_zl[1]),_zn=B(_cW(_zk[1],_zk[2],_zk[3],_zj[2],_zm[1],_zm[2],_zm[3],_zl[2])),_zo=E(_zn[1]),_zp=B(_cW(_zi[1],_zi[2],_zi[3],_zh[2],_zo[1],_zo[2],_zo[3],_zn[2]));return [0,E(_zp[1]),_zp[2]];})]);});});});},function(_zq){return new F(function(){return A(_yE,[new T(function(){return B(_dL(_yT,_zq));})]);});}]);});}]);});};return new F(function(){return _yl(_y9,_ya,_yb,_yc,_yd);});},_zr=new T(function(){return B(unCStr("tab"));}),_zs=[1,_zr,_9],_zt=[0,9],_zu=function(_zv){return function(_zw,_zx,_zy,_zz,_zA){return new F(function(){return _jw(new T(function(){return B(_jN(_zv,_zt));}),_zs,_zw,_zx,_zy,_zz,_zA);});};},_zB=new T(function(){return B(_zu(_j3));}),_zC=[0,39],_zD=[1,_zC,_9],_zE=new T(function(){return B(unCStr("\'\\\'\'"));}),_zF=function(_zG){var _zH=E(E(_zG)[1]);return _zH==39?E(_zE):[1,_zC,new T(function(){return B(_hJ(_zH,_zD));})];},_zI=function(_zJ,_zK){return [1,_ga,new T(function(){return B(_i0(_zJ,[1,_ga,_zK]));})];},_zL=function(_zM){return new F(function(){return _e(_zE,_zM);});},_zN=function(_zO,_zP){var _zQ=E(E(_zP)[1]);return _zQ==39?E(_zL):function(_zR){return [1,_zC,new T(function(){return B(_hJ(_zQ,[1,_zC,_zR]));})];};},_zS=[0,_zN,_zF,_zI],_zT=function(_zU,_zV,_zW,_zX,_zY){var _zZ=new T(function(){return B(_bm(_zU));}),_A0=function(_A1){return new F(function(){return A(_zX,[_5c,_zW,new T(function(){var _A2=E(E(_zW)[2]),_A3=E(_A1),_A4=E(_A3[1]),_A5=B(_cW(_A4[1],_A4[2],_A4[3],_A3[2],_A2[1],_A2[2],_A2[3],_9));return [0,E(_A5[1]),_A5[2]];})]);});};return new F(function(){return A(_zV,[_zW,function(_A6,_A7,_A8){return new F(function(){return A(_zY,[new T(function(){var _A9=E(E(_A7)[2]),_Aa=E(_A8),_Ab=E(_Aa[1]),_Ac=B(_cW(_Ab[1],_Ab[2],_Ab[3],_Aa[2],_A9[1],_A9[2],_A9[3],[1,new T(function(){return [1,E(B(A(_zZ,[_A6])))];}),_9]));return [0,E(_Ac[1]),_Ac[2]];})]);});},_A0,function(_Ad,_Ae,_Af){return new F(function(){return A(_zX,[_5c,_zW,new T(function(){var _Ag=E(E(_zW)[2]),_Ah=E(E(_Ae)[2]),_Ai=E(_Af),_Aj=E(_Ai[1]),_Ak=B(_cW(_Aj[1],_Aj[2],_Aj[3],_Ai[2],_Ah[1],_Ah[2],_Ah[3],[1,new T(function(){return [1,E(B(A(_zZ,[_Ad])))];}),_9])),_Al=E(_Ak[1]),_Am=B(_cW(_Al[1],_Al[2],_Al[3],_Ak[2],_Ag[1],_Ag[2],_Ag[3],_9));return [0,E(_Am[1]),_Am[2]];})]);});},_A0]);});},_An=function(_Ao,_Ap,_Aq,_Ar){return new F(function(){return _zT(_zS,_zB,_Ap,function(_As,_At,_Au){return new F(function(){return A(_Aq,[_Ao,_At,new T(function(){var _Av=E(E(_At)[2]),_Aw=E(_Au),_Ax=E(_Aw[1]),_Ay=B(_cW(_Ax[1],_Ax[2],_Ax[3],_Aw[2],_Av[1],_Av[2],_Av[3],_9));return [0,E(_Ay[1]),_Ay[2]];})]);});},_Ar);});},_Az=function(_AA,_AB,_AC,_AD,_AE){return new F(function(){return A(_ke,[_AA,function(_AF,_AG,_AH){return new F(function(){return _An(_AF,_AG,function(_AI,_AJ,_AK){return new F(function(){return A(_AB,[_AI,_AJ,new T(function(){return B(_dL(_AH,_AK));})]);});},function(_AL){return new F(function(){return A(_AC,[new T(function(){return B(_dL(_AH,_AL));})]);});});});},_AC,function(_AM,_AN,_AO){return new F(function(){return _An(_AM,_AN,function(_AP,_AQ,_AR){return new F(function(){return A(_AD,[_AP,_AQ,new T(function(){return B(_dL(_AO,_AR));})]);});},function(_AS){return new F(function(){return A(_AE,[new T(function(){return B(_dL(_AO,_AS));})]);});});});},_AE]);});},_AT=[0,E(_9)],_AU=[1,_AT,_9],_AV=function(_AW,_AX,_AY,_AZ,_B0,_B1,_B2){return new F(function(){return A(_AW,[new T(function(){return B(A(_AX,[_AY]));}),function(_B3){var _B4=E(_B3);if(!_B4[0]){return E(new T(function(){return B(A(_B2,[[0,E(_AZ),_AU]]));}));}else{var _B5=E(_B4[1]);return new F(function(){return A(_B1,[_B5[1],[0,_B5[2],E(_AZ),E(_B0)],[0,E(_AZ),_9]]);});}}]);});},_B6=new T(function(){return B(unCStr("end of input"));}),_B7=[1,_B6,_9],_B8=function(_B9,_Ba,_Bb,_Bc,_Bd,_Be,_Bf,_Bg){return new F(function(){return _jw(function(_Bh,_Bi,_Bj,_Bk,_Bl){return new F(function(){return _zT(_Bb,function(_Bm,_Bn,_Bo,_Bp,_Bq){var _Br=E(_Bm);return new F(function(){return _AV(_B9,_Ba,_Br[1],_Br[2],_Br[3],_Bn,_Bq);});},_Bh,_Bk,_Bl);});},_B7,_Bc,_Bd,_Be,_Bf,_Bg);});},_Bs=function(_Bt,_Bu,_Bv,_Bw,_Bx,_By){return new F(function(){return _B8(_g7,_iQ,_zS,_Bu,function(_Bz,_BA,_BB){return new F(function(){return A(_Bv,[_Bt,_BA,new T(function(){var _BC=E(E(_BA)[2]),_BD=E(_BB),_BE=E(_BD[1]),_BF=B(_cW(_BE[1],_BE[2],_BE[3],_BD[2],_BC[1],_BC[2],_BC[3],_9));return [0,E(_BF[1]),_BF[2]];})]);});},_Bw,function(_BG,_BH,_BI){return new F(function(){return A(_Bx,[_Bt,_BH,new T(function(){var _BJ=E(E(_BH)[2]),_BK=E(_BI),_BL=E(_BK[1]),_BM=B(_cW(_BL[1],_BL[2],_BL[3],_BK[2],_BJ[1],_BJ[2],_BJ[3],_9));return [0,E(_BM[1]),_BM[2]];})]);});},_By);});},_BN=function(_BO,_BP,_BQ,_BR,_BS){return new F(function(){return A(_ke,[_BO,function(_BT,_BU,_BV){return new F(function(){return _Bs(_BT,_BU,_BP,_BQ,function(_BW,_BX,_BY){return new F(function(){return A(_BP,[_BW,_BX,new T(function(){return B(_dL(_BV,_BY));})]);});},function(_BZ){return new F(function(){return A(_BQ,[new T(function(){return B(_dL(_BV,_BZ));})]);});});});},_BQ,function(_C0,_C1,_C2){return new F(function(){return _Bs(_C0,_C1,_BP,_BQ,function(_C3,_C4,_C5){return new F(function(){return A(_BR,[_C3,_C4,new T(function(){return B(_dL(_C2,_C5));})]);});},function(_C6){return new F(function(){return A(_BS,[new T(function(){return B(_dL(_C2,_C6));})]);});});});},_BS]);});},_C7=function(_C8,_C9,_Ca,_Cb){var _Cc=function(_Cd){var _Ce=function(_Cf){return new F(function(){return A(_Cb,[new T(function(){return B(_dL(_Cd,_Cf));})]);});};return new F(function(){return _Az(_C8,_C9,_Ce,function(_Cg,_Ch,_Ci){return new F(function(){return A(_Ca,[_Cg,_Ch,new T(function(){return B(_dL(_Cd,_Ci));})]);});},_Ce);});};return new F(function(){return _BN(_C8,_C9,_Cc,_Ca,_Cc);});},_Cj=function(_Ck,_Cl,_Cm,_Cn,_Co){return new F(function(){return _C7(_Ck,_Cl,_Cn,_Co);});},_Cp=function(_Cq){return true;},_Cr=function(_Cs,_Ct,_Cu,_Cv,_Cw){var _Cx=E(_Cs),_Cy=E(_Cx[2]);return new F(function(){return _i6(_g7,_iQ,_Cp,_Cx[1],_Cy[1],_Cy[2],_Cy[3],_Cx[3],_Ct,_Cw);});},_Cz=function(_CA,_CB,_CC,_CD,_CE){return new F(function(){return A(_zB,[_CA,function(_CF,_CG,_CH){return new F(function(){return _y6(_Cr,_Cj,_CG,_CB,_CC,function(_CI,_CJ,_CK){return new F(function(){return A(_CB,[_CI,_CJ,new T(function(){return B(_dL(_CH,_CK));})]);});},function(_CL){return new F(function(){return A(_CC,[new T(function(){return B(_dL(_CH,_CL));})]);});});});},_CC,function(_CM,_CN,_CO){return new F(function(){return _y6(_Cr,_Cj,_CN,_CB,_CC,function(_CP,_CQ,_CR){return new F(function(){return A(_CD,[_CP,_CQ,new T(function(){return B(_dL(_CO,_CR));})]);});},function(_CS){return new F(function(){return A(_CE,[new T(function(){return B(_dL(_CO,_CS));})]);});});});},_CE]);});},_CT=[0,_wV,_9],_CU=[0,_9,1,1],_CV=function(_CW){return E(_CW);},_CX=function(_CY){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_CY));}))));});},_CZ=new T(function(){return B(_CX("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_D0=new T(function(){return B(_CX("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_D1=[0,_g7,_D0,_CV,_CZ],_D2=[0,10],_D3=[1,_D2,_9],_D4=function(_D5){return new F(function(){return unAppCStr("string error",new T(function(){var _D6=E(_D5),_D7=E(_D6[1]);return B(_e(B(_9R(_D7[1],_D7[2],_D7[3],_D6[2])),_D3));}));});},_D8=function(_D9,_Da,_Db,_Dc,_Dd){return new F(function(){return A(_zB,[_Da,function(_De,_Df,_Dg){return new F(function(){return A(_Db,[_D9,_Df,new T(function(){var _Dh=E(E(_Df)[2]),_Di=E(_Dg),_Dj=E(_Di[1]),_Dk=B(_cW(_Dj[1],_Dj[2],_Dj[3],_Di[2],_Dh[1],_Dh[2],_Dh[3],_9));return [0,E(_Dk[1]),_Dk[2]];})]);});},_Dd,function(_Dl,_Dm,_Dn){return new F(function(){return A(_Dc,[_D9,_Dm,new T(function(){var _Do=E(E(_Dm)[2]),_Dp=E(_Dn),_Dq=E(_Dp[1]),_Dr=B(_cW(_Dq[1],_Dq[2],_Dq[3],_Dp[2],_Do[1],_Do[2],_Do[3],_9));return [0,E(_Dr[1]),_Dr[2]];})]);});},_Dd]);});},_Ds=function(_Dt,_Du,_Dv,_Dw,_Dx){return new F(function(){return A(_ke,[_Dt,function(_Dy,_Dz,_DA){return new F(function(){return _D8(_Dy,_Dz,_Du,function(_DB,_DC,_DD){return new F(function(){return A(_Du,[_DB,_DC,new T(function(){return B(_dL(_DA,_DD));})]);});},function(_DE){return new F(function(){return A(_Dv,[new T(function(){return B(_dL(_DA,_DE));})]);});});});},_Dv,function(_DF,_DG,_DH){return new F(function(){return _D8(_DF,_DG,_Du,function(_DI,_DJ,_DK){return new F(function(){return A(_Dw,[_DI,_DJ,new T(function(){return B(_dL(_DH,_DK));})]);});},function(_DL){return new F(function(){return A(_Dx,[new T(function(){return B(_dL(_DH,_DL));})]);});});});},_Dx]);});},_DM=function(_DN,_DO,_DP,_DQ,_DR){return new F(function(){return _Ds(_DN,_DO,_DP,_DQ,function(_DS){var _DT=E(_DN),_DU=E(_DT[2]),_DV=E(_DT[1]);return _DV[0]==0?B(A(_DR,[new T(function(){var _DW=E(_DS),_DX=E(_DW[1]),_DY=B(_cW(_DX[1],_DX[2],_DX[3],_DW[2],_DU[1],_DU[2],_DU[3],_AU));return [0,E(_DY[1]),_DY[2]];})])):B(A(_DO,[_DV[1],[0,_DV[2],E(_DU),E(_DT[3])],[0,E(_DU),_9]]));});});},_DZ=function(_E0,_E1,_E2,_E3,_E4){return new F(function(){return _dj(_DM,_E0,_E1,_E2,_E3);});},_E5=function(_E6,_E7,_E8){return [0,_E6,E(E(_E7)),_E8];},_E9=function(_Ea,_Eb,_Ec){var _Ed=new T(function(){return B(_iK(_Ea));}),_Ee=new T(function(){return B(_iK(_Ea));});return new F(function(){return A(_Eb,[_Ec,function(_Ef,_Eg,_Eh){return new F(function(){return A(_Ed,[[0,new T(function(){return B(A(_Ee,[new T(function(){return B(_E5(_Ef,_Eg,_Eh));})]));})]]);});},function(_Ei){return new F(function(){return A(_Ed,[[0,new T(function(){return B(A(_Ee,[[1,_Ei]]));})]]);});},function(_Ej,_Ek,_El){return new F(function(){return A(_Ed,[new T(function(){return [1,E(B(A(_Ee,[new T(function(){return B(_E5(_Ej,_Ek,_El));})])))];})]);});},function(_Em){return new F(function(){return A(_Ed,[new T(function(){return [1,E(B(A(_Ee,[[1,_Em]])))];})]);});}]);});},_En=function(_Eo){return function(_Ep,_Eq,_Er,_Es,_Et){return new F(function(){return A(_Es,[new T(function(){var _Eu=B(_E9(_D1,_Ev,[0,new T(function(){var _Ew=B(_E9(_D1,_DZ,[0,_Eo,E(_CU),E(_5c)]));if(!_Ew[0]){var _Ex=E(_Ew[1]),_Ey=_Ex[0]==0?B(_e(_Ex[1],_D3)):B(_D4(_Ex[1]));}else{var _Ez=E(_Ew[1]),_Ey=_Ez[0]==0?B(_e(_Ez[1],_D3)):B(_D4(_Ez[1]));}return _Ey;}),E(_CU),E(_5c)]));if(!_Eu[0]){var _EA=E(_Eu[1]),_EB=_EA[0]==0?E(_EA[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_EA[1]));})));})],_9],_9],_CT];}else{var _EC=E(_Eu[1]),_EB=_EC[0]==0?E(_EC[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_EC[1]));})));})],_9],_9],_CT];}return _EB;}),_Ep,new T(function(){return [0,E(E(_Ep)[2]),_9];})]);});};},_ED=function(_EE,_EF,_EG,_EH,_EI){return new F(function(){return _Cz(_EE,function(_EJ,_EK,_EL){return new F(function(){return A(_En,[_EJ,_EK,_EF,_EG,function(_EM,_EN,_EO){return new F(function(){return A(_EF,[_EM,_EN,new T(function(){return B(_dL(_EL,_EO));})]);});},function(_EP){return new F(function(){return A(_EG,[new T(function(){return B(_dL(_EL,_EP));})]);});}]);});},_EG,function(_EQ,_ER,_ES){return new F(function(){return A(_En,[_EQ,_ER,_EF,_EG,function(_ET,_EU,_EV){return new F(function(){return A(_EH,[_ET,_EU,new T(function(){return B(_dL(_ES,_EV));})]);});},function(_EW){return new F(function(){return A(_EI,[new T(function(){return B(_dL(_ES,_EW));})]);});}]);});},_EI);});},_EX=function(_EY,_EZ,_F0,_F1,_F2,_F3){var _F4=function(_F5,_F6,_F7,_F8,_F9){var _Fa=function(_Fb,_Fc,_Fd,_Fe,_Ff){return new F(function(){return A(_F8,[[0,[1,[0,_EY,_Fc,_Fd]],_Fb],_Fe,new T(function(){var _Fg=E(_Ff),_Fh=E(_Fg[1]),_Fi=E(E(_Fe)[2]),_Fj=B(_cW(_Fh[1],_Fh[2],_Fh[3],_Fg[2],_Fi[1],_Fi[2],_Fi[3],_9));return [0,E(_Fj[1]),_Fj[2]];})]);});},_Fk=function(_Fl){return new F(function(){return _Fa(_9,_wV,_9,_F5,new T(function(){var _Fm=E(E(_F5)[2]),_Fn=E(_Fl),_Fo=E(_Fn[1]),_Fp=B(_cW(_Fo[1],_Fo[2],_Fo[3],_Fn[2],_Fm[1],_Fm[2],_Fm[3],_9));return [0,E(_Fp[1]),_Fp[2]];}));});};return new F(function(){return _ED(_F5,function(_Fq,_Fr,_Fs){var _Ft=E(_Fq),_Fu=E(_Ft[2]);return new F(function(){return A(_F6,[[0,[1,[0,_EY,_Fu[1],_Fu[2]]],_Ft[1]],_Fr,new T(function(){var _Fv=E(_Fs),_Fw=E(_Fv[1]),_Fx=E(E(_Fr)[2]),_Fy=B(_cW(_Fw[1],_Fw[2],_Fw[3],_Fv[2],_Fx[1],_Fx[2],_Fx[3],_9));return [0,E(_Fy[1]),_Fy[2]];})]);});},_Fk,function(_Fz,_FA,_FB){var _FC=E(_Fz),_FD=E(_FC[2]);return new F(function(){return _Fa(_FC[1],_FD[1],_FD[2],_FA,_FB);});},_Fk);});};return new F(function(){return A(_ke,[_EZ,function(_FE,_FF,_FG){return new F(function(){return _F4(_FF,_F0,_F1,function(_FH,_FI,_FJ){return new F(function(){return A(_F0,[_FH,_FI,new T(function(){return B(_dL(_FG,_FJ));})]);});},function(_FK){return new F(function(){return A(_F1,[new T(function(){return B(_dL(_FG,_FK));})]);});});});},_F3,function(_FL,_FM,_FN){return new F(function(){return _F4(_FM,_F0,_F1,function(_FO,_FP,_FQ){return new F(function(){return A(_F2,[_FO,_FP,new T(function(){return B(_dL(_FN,_FQ));})]);});},function(_FR){return new F(function(){return A(_F3,[new T(function(){return B(_dL(_FN,_FR));})]);});});});},_F3]);});},_FS=new T(function(){return B(unCStr(" associative operator"));}),_FT=function(_FU,_FV){var _FW=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_FU,_FS));}))))];}),_9];return function(_FX,_FY,_FZ,_G0,_G1){return new F(function(){return A(_FV,[_FX,function(_G2,_G3,_G4){return new F(function(){return A(_G1,[new T(function(){var _G5=E(E(_G3)[2]),_G6=E(_G4),_G7=E(_G6[1]),_G8=B(_cW(_G7[1],_G7[2],_G7[3],_G6[2],_G5[1],_G5[2],_G5[3],_FW));return [0,E(_G8[1]),_G8[2]];})]);});},_G1,function(_G9,_Ga,_Gb){return new F(function(){return A(_G1,[new T(function(){var _Gc=E(E(_Ga)[2]),_Gd=E(_Gb),_Ge=E(_Gd[1]),_Gf=B(_cW(_Ge[1],_Ge[2],_Ge[3],_Gd[2],_Gc[1],_Gc[2],_Gc[3],_FW));return [0,E(_Gf[1]),_Gf[2]];})]);});},_G1]);});};},_Gg=function(_Gh,_Gi,_Gj,_Gk,_Gl,_Gm){var _Gn=E(_Gh);if(!_Gn[0]){return new F(function(){return A(_Gm,[new T(function(){return [0,E(E(_Gi)[2]),_9];})]);});}else{return new F(function(){return A(_Gn[1],[_Gi,_Gj,_Gk,_Gl,function(_Go){return new F(function(){return _Gg(_Gn[2],_Gi,_Gj,_Gk,function(_Gp,_Gq,_Gr){return new F(function(){return A(_Gl,[_Gp,_Gq,new T(function(){return B(_dL(_Go,_Gr));})]);});},function(_Gs){return new F(function(){return A(_Gm,[new T(function(){return B(_dL(_Go,_Gs));})]);});});});}]);});}},_Gt=new T(function(){return B(unCStr("right"));}),_Gu=new T(function(){return B(unCStr("left"));}),_Gv=new T(function(){return B(unCStr("non"));}),_Gw=new T(function(){return B(unCStr("operator"));}),_Gx=[1,_Gw,_9],_Gy=[1,_9,_9],_Gz=function(_GA){var _GB=E(_GA);if(!_GB[0]){return [0,_9,_9,_9,_9,_9];}else{var _GC=_GB[2],_GD=E(_GB[1]);switch(_GD[0]){case 0:var _GE=_GD[1],_GF=B(_Gz(_GC)),_GG=_GF[1],_GH=_GF[2],_GI=_GF[3],_GJ=_GF[4],_GK=_GF[5];switch(E(_GD[2])){case 0:return [0,_GG,_GH,[1,_GE,_GI],_GJ,_GK];case 1:return [0,_GG,[1,_GE,_GH],_GI,_GJ,_GK];default:return [0,[1,_GE,_GG],_GH,_GI,_GJ,_GK];}break;case 1:var _GL=B(_Gz(_GC));return [0,_GL[1],_GL[2],_GL[3],[1,_GD[1],_GL[4]],_GL[5]];default:var _GM=B(_Gz(_GC));return [0,_GM[1],_GM[2],_GM[3],_GM[4],[1,_GD[1],_GM[5]]];}}},_GN=function(_GO,_GP){while(1){var _GQ=(function(_GR,_GS){var _GT=E(_GS);if(!_GT[0]){return E(_GR);}else{var _GU=new T(function(){var _GV=B(_Gz(_GT[1]));return [0,_GV[1],_GV[2],_GV[3],_GV[4],_GV[5]];}),_GW=new T(function(){return E(E(_GU)[2]);}),_GX=new T(function(){return B(_FT(_Gu,function(_GY,_GZ,_H0,_H1,_H2){return new F(function(){return _Gg(_GW,_GY,_GZ,_H0,_H1,_H2);});}));}),_H3=new T(function(){return E(E(_GU)[1]);}),_H4=new T(function(){return E(E(_GU)[3]);}),_H5=new T(function(){return B(_FT(_Gv,function(_H6,_H7,_H8,_H9,_Ha){return new F(function(){return _Gg(_H4,_H6,_H7,_H8,_H9,_Ha);});}));}),_Hb=function(_Hc,_Hd,_He,_Hf,_Hg,_Hh){var _Hi=function(_Hj,_Hk,_Hl,_Hm,_Hn){var _Ho=new T(function(){return B(A(_Hc,[_Hj]));});return new F(function(){return _Gg(new T(function(){return E(E(_GU)[5]);}),_Hk,function(_Hp,_Hq,_Hr){return new F(function(){return A(_Hl,[new T(function(){return B(A(_Hp,[_Ho]));}),_Hq,new T(function(){var _Hs=E(E(_Hq)[2]),_Ht=E(_Hr),_Hu=E(_Ht[1]),_Hv=B(_cW(_Hu[1],_Hu[2],_Hu[3],_Ht[2],_Hs[1],_Hs[2],_Hs[3],_9));return [0,E(_Hv[1]),_Hv[2]];})]);});},_Hm,function(_Hw,_Hx,_Hy){return new F(function(){return A(_Hn,[new T(function(){return B(A(_Hw,[_Ho]));}),_Hx,new T(function(){var _Hz=E(E(_Hx)[2]),_HA=_Hz[1],_HB=_Hz[2],_HC=_Hz[3],_HD=E(_Hy),_HE=E(_HD[1]),_HF=_HE[2],_HG=_HE[3],_HH=E(_HD[2]);if(!_HH[0]){switch(B(_cO(_HE[1],_HA))){case 0:var _HI=[0,E(_Hz),_9];break;case 1:if(_HF>=_HB){if(_HF!=_HB){var _HJ=[0,E(_HE),_9];}else{if(_HG>=_HC){var _HK=_HG!=_HC?[0,E(_HE),_9]:[0,E(_HE),_cV];}else{var _HK=[0,E(_Hz),_9];}var _HL=_HK,_HJ=_HL;}var _HM=_HJ,_HN=_HM;}else{var _HN=[0,E(_Hz),_9];}var _HO=_HN,_HI=_HO;break;default:var _HI=[0,E(_HE),_9];}var _HP=_HI;}else{var _HQ=B(_jb(_HE,_HH,_Gy)),_HR=E(_HQ[1]),_HS=B(_cW(_HR[1],_HR[2],_HR[3],_HQ[2],_HA,_HB,_HC,_9)),_HP=[0,E(_HS[1]),_HS[2]];}var _HT=_HP,_HU=_HT,_HV=_HU,_HW=_HV;return _HW;})]);});},function(_HX){return new F(function(){return A(_Hn,[_Ho,_Hk,new T(function(){var _HY=E(E(_Hk)[2]),_HZ=_HY[1],_I0=_HY[2],_I1=_HY[3],_I2=E(_HX),_I3=B(_jb(_I2[1],_I2[2],_Gy)),_I4=E(_I3[1]),_I5=B(_cW(_I4[1],_I4[2],_I4[3],_I3[2],_HZ,_I0,_I1,_9)),_I6=E(_I5[1]),_I7=B(_cW(_I6[1],_I6[2],_I6[3],_I5[2],_HZ,_I0,_I1,_9));return [0,E(_I7[1]),_I7[2]];})]);});});});};return new F(function(){return A(_GR,[_Hd,function(_I8,_I9,_Ia){return new F(function(){return _Hi(_I8,_I9,_He,_Hf,function(_Ib,_Ic,_Id){return new F(function(){return A(_He,[_Ib,_Ic,new T(function(){return B(_dL(_Ia,_Id));})]);});});});},_Hf,function(_Ie,_If,_Ig){return new F(function(){return _Hi(_Ie,_If,_He,_Hf,function(_Ih,_Ii,_Ij){return new F(function(){return A(_Hg,[_Ih,_Ii,new T(function(){return B(_dL(_Ig,_Ij));})]);});});});},_Hh]);});},_Ik=function(_Il,_Im,_In,_Io,_Ip){var _Iq=function(_Ir,_Is,_It){return new F(function(){return _Hb(_Ir,_Is,_Im,_In,function(_Iu,_Iv,_Iw){return new F(function(){return A(_Io,[_Iu,_Iv,new T(function(){return B(_dL(_It,_Iw));})]);});},function(_Ix){return new F(function(){return A(_Ip,[new T(function(){return B(_dL(_It,_Ix));})]);});});});};return new F(function(){return _Gg(new T(function(){return E(E(_GU)[4]);}),_Il,function(_Iy,_Iz,_IA){return new F(function(){return _Hb(_Iy,_Iz,_Im,_In,function(_IB,_IC,_ID){return new F(function(){return A(_Im,[_IB,_IC,new T(function(){return B(_dL(_IA,_ID));})]);});},function(_IE){return new F(function(){return A(_In,[new T(function(){return B(_dL(_IA,_IE));})]);});});});},_In,function(_IF,_IG,_IH){return new F(function(){return _Iq(_IF,_IG,new T(function(){var _II=E(_IH),_IJ=E(_II[2]);if(!_IJ[0]){var _IK=E(_II);}else{var _IL=B(_jb(_II[1],_IJ,_Gy)),_IK=[0,E(_IL[1]),_IL[2]];}var _IM=_IK;return _IM;}));});},function(_IN){return new F(function(){return _Iq(_5q,_Il,new T(function(){var _IO=E(E(_Il)[2]),_IP=E(_IN),_IQ=B(_jb(_IP[1],_IP[2],_Gy)),_IR=E(_IQ[1]),_IS=B(_cW(_IR[1],_IR[2],_IR[3],_IQ[2],_IO[1],_IO[2],_IO[3],_9));return [0,E(_IS[1]),_IS[2]];}));});});});},_IT=function(_IU,_IV,_IW,_IX,_IY,_IZ){var _J0=function(_J1){return new F(function(){return A(_GX,[_IV,_IW,_IX,function(_J2,_J3,_J4){return new F(function(){return A(_IY,[_J2,_J3,new T(function(){return B(_dL(_J1,_J4));})]);});},function(_J5){return new F(function(){return A(_H5,[_IV,_IW,_IX,function(_J6,_J7,_J8){return new F(function(){return A(_IY,[_J6,_J7,new T(function(){var _J9=E(_J1),_Ja=E(_J9[1]),_Jb=E(_J5),_Jc=E(_Jb[1]),_Jd=E(_J8),_Je=E(_Jd[1]),_Jf=B(_cW(_Jc[1],_Jc[2],_Jc[3],_Jb[2],_Je[1],_Je[2],_Je[3],_Jd[2])),_Jg=E(_Jf[1]),_Jh=B(_cW(_Ja[1],_Ja[2],_Ja[3],_J9[2],_Jg[1],_Jg[2],_Jg[3],_Jf[2]));return [0,E(_Jh[1]),_Jh[2]];})]);});},function(_Ji){return new F(function(){return A(_IZ,[new T(function(){var _Jj=E(_J1),_Jk=E(_Jj[1]),_Jl=E(_J5),_Jm=E(_Jl[1]),_Jn=E(_Ji),_Jo=E(_Jn[1]),_Jp=B(_cW(_Jm[1],_Jm[2],_Jm[3],_Jl[2],_Jo[1],_Jo[2],_Jo[3],_Jn[2])),_Jq=E(_Jp[1]),_Jr=B(_cW(_Jk[1],_Jk[2],_Jk[3],_Jj[2],_Jq[1],_Jq[2],_Jq[3],_Jp[2]));return [0,E(_Jr[1]),_Jr[2]];})]);});}]);});}]);});},_Js=function(_Jt,_Ju,_Jv,_Jw,_Jx,_Jy){var _Jz=function(_JA,_JB,_JC){return new F(function(){return A(_Jv,[new T(function(){return B(A(_Jt,[_IU,_JA]));}),_JB,new T(function(){var _JD=E(E(_JB)[2]),_JE=E(_JC),_JF=E(_JE[1]),_JG=B(_cW(_JF[1],_JF[2],_JF[3],_JE[2],_JD[1],_JD[2],_JD[3],_9));return [0,E(_JG[1]),_JG[2]];})]);});};return new F(function(){return _Ik(_Ju,function(_JH,_JI,_JJ){return new F(function(){return _IT(_JH,_JI,_Jz,_Jw,function(_JK,_JL,_JM){return new F(function(){return _Jz(_JK,_JL,new T(function(){var _JN=E(_JJ),_JO=E(_JN[1]),_JP=E(_JM),_JQ=E(_JP[1]),_JR=B(_cW(_JO[1],_JO[2],_JO[3],_JN[2],_JQ[1],_JQ[2],_JQ[3],_JP[2]));return [0,E(_JR[1]),_JR[2]];},1));});},function(_JS){return new F(function(){return _Jz(_JH,_JI,new T(function(){var _JT=E(E(_JI)[2]),_JU=E(_JJ),_JV=E(_JU[1]),_JW=E(_JS),_JX=E(_JW[1]),_JY=B(_cW(_JX[1],_JX[2],_JX[3],_JW[2],_JT[1],_JT[2],_JT[3],_9)),_JZ=E(_JY[1]),_K0=B(_cW(_JV[1],_JV[2],_JV[3],_JU[2],_JZ[1],_JZ[2],_JZ[3],_JY[2]));return [0,E(_K0[1]),_K0[2]];},1));});});});},_Jw,function(_K1,_K2,_K3){var _K4=function(_K5,_K6,_K7){return new F(function(){return A(_Jx,[new T(function(){return B(A(_Jt,[_IU,_K5]));}),_K6,new T(function(){var _K8=E(E(_K6)[2]),_K9=E(_K3),_Ka=E(_K9[1]),_Kb=E(_K7),_Kc=E(_Kb[1]),_Kd=B(_cW(_Ka[1],_Ka[2],_Ka[3],_K9[2],_Kc[1],_Kc[2],_Kc[3],_Kb[2])),_Ke=E(_Kd[1]),_Kf=B(_cW(_Ke[1],_Ke[2],_Ke[3],_Kd[2],_K8[1],_K8[2],_K8[3],_9));return [0,E(_Kf[1]),_Kf[2]];})]);});};return new F(function(){return _IT(_K1,_K2,_Jz,_Jw,_K4,function(_Kg){return new F(function(){return _K4(_K1,_K2,new T(function(){var _Kh=E(E(_K2)[2]),_Ki=E(_Kg),_Kj=E(_Ki[1]),_Kk=B(_cW(_Kj[1],_Kj[2],_Kj[3],_Ki[2],_Kh[1],_Kh[2],_Kh[3],_9));return [0,E(_Kk[1]),_Kk[2]];},1));});});});},_Jy);});};return new F(function(){return _Gg(_H3,_IV,function(_Kl,_Km,_Kn){return new F(function(){return _Js(_Kl,_Km,_IW,_IX,function(_Ko,_Kp,_Kq){return new F(function(){return A(_IW,[_Ko,_Kp,new T(function(){return B(_dL(_Kn,_Kq));})]);});},function(_Kr){return new F(function(){return A(_IX,[new T(function(){return B(_dL(_Kn,_Kr));})]);});});});},_IX,function(_Ks,_Kt,_Ku){return new F(function(){return _Js(_Ks,_Kt,_IW,_IX,function(_Kv,_Kw,_Kx){return new F(function(){return A(_IY,[_Kv,_Kw,new T(function(){return B(_dL(_Ku,_Kx));})]);});},function(_Ky){return new F(function(){return _J0(new T(function(){return B(_dL(_Ku,_Ky));}));});});});},_J0);});},_Kz=new T(function(){return B(_FT(_Gt,function(_KA,_KB,_KC,_KD,_KE){return new F(function(){return _Gg(_H3,_KA,_KB,_KC,_KD,_KE);});}));}),_KF=function(_KG,_KH,_KI,_KJ,_KK,_KL){var _KM=function(_KN){return new F(function(){return A(_Kz,[_KH,_KI,_KJ,function(_KO,_KP,_KQ){return new F(function(){return A(_KK,[_KO,_KP,new T(function(){return B(_dL(_KN,_KQ));})]);});},function(_KR){return new F(function(){return A(_H5,[_KH,_KI,_KJ,function(_KS,_KT,_KU){return new F(function(){return A(_KK,[_KS,_KT,new T(function(){var _KV=E(_KN),_KW=E(_KV[1]),_KX=E(_KR),_KY=E(_KX[1]),_KZ=E(_KU),_L0=E(_KZ[1]),_L1=B(_cW(_KY[1],_KY[2],_KY[3],_KX[2],_L0[1],_L0[2],_L0[3],_KZ[2])),_L2=E(_L1[1]),_L3=B(_cW(_KW[1],_KW[2],_KW[3],_KV[2],_L2[1],_L2[2],_L2[3],_L1[2]));return [0,E(_L3[1]),_L3[2]];})]);});},function(_L4){return new F(function(){return A(_KL,[new T(function(){var _L5=E(_KN),_L6=E(_L5[1]),_L7=E(_KR),_L8=E(_L7[1]),_L9=E(_L4),_La=E(_L9[1]),_Lb=B(_cW(_L8[1],_L8[2],_L8[3],_L7[2],_La[1],_La[2],_La[3],_L9[2])),_Lc=E(_Lb[1]),_Ld=B(_cW(_L6[1],_L6[2],_L6[3],_L5[2],_Lc[1],_Lc[2],_Lc[3],_Lb[2]));return [0,E(_Ld[1]),_Ld[2]];})]);});}]);});}]);});},_Le=function(_Lf,_Lg,_Lh,_Li,_Lj,_Lk){var _Ll=function(_Lm){var _Ln=new T(function(){return B(A(_Lf,[_KG,_Lm]));});return function(_Lo,_Lp,_Lq,_Lr,_Ls){return new F(function(){return _KF(_Ln,_Lo,_Lp,_Lq,_Lr,function(_Lt){return new F(function(){return A(_Lr,[_Ln,_Lo,new T(function(){var _Lu=E(E(_Lo)[2]),_Lv=E(_Lt),_Lw=E(_Lv[1]),_Lx=B(_cW(_Lw[1],_Lw[2],_Lw[3],_Lv[2],_Lu[1],_Lu[2],_Lu[3],_9));return [0,E(_Lx[1]),_Lx[2]];})]);});});});};};return new F(function(){return _Ik(_Lg,function(_Ly,_Lz,_LA){return new F(function(){return A(_Ll,[_Ly,_Lz,_Lh,_Li,function(_LB,_LC,_LD){return new F(function(){return A(_Lh,[_LB,_LC,new T(function(){return B(_dL(_LA,_LD));})]);});},function(_LE){return new F(function(){return A(_Li,[new T(function(){return B(_dL(_LA,_LE));})]);});}]);});},_Li,function(_LF,_LG,_LH){return new F(function(){return A(_Ll,[_LF,_LG,_Lh,_Li,function(_LI,_LJ,_LK){return new F(function(){return A(_Lj,[_LI,_LJ,new T(function(){return B(_dL(_LH,_LK));})]);});},function(_LL){return new F(function(){return A(_Lk,[new T(function(){return B(_dL(_LH,_LL));})]);});}]);});},_Lk);});};return new F(function(){return _Gg(_GW,_KH,function(_LM,_LN,_LO){return new F(function(){return _Le(_LM,_LN,_KI,_KJ,function(_LP,_LQ,_LR){return new F(function(){return A(_KI,[_LP,_LQ,new T(function(){return B(_dL(_LO,_LR));})]);});},function(_LS){return new F(function(){return A(_KJ,[new T(function(){return B(_dL(_LO,_LS));})]);});});});},_KJ,function(_LT,_LU,_LV){return new F(function(){return _Le(_LT,_LU,_KI,_KJ,function(_LW,_LX,_LY){return new F(function(){return A(_KK,[_LW,_LX,new T(function(){return B(_dL(_LV,_LY));})]);});},function(_LZ){return new F(function(){return _KM(new T(function(){return B(_dL(_LV,_LZ));}));});});});},_KM);});},_M0=function(_M1,_M2,_M3,_M4,_M5,_M6){var _M7=function(_M8,_M9,_Ma,_Mb,_Mc,_Md){var _Me=function(_Mf){return function(_Mg,_Mh,_Mi,_Mj,_Mk){return new F(function(){return A(_Kz,[_Mg,_Mh,_Mi,_Mj,function(_Ml){return new F(function(){return A(_GX,[_Mg,_Mh,_Mi,function(_Mm,_Mn,_Mo){return new F(function(){return A(_Mj,[_Mm,_Mn,new T(function(){return B(_dL(_Ml,_Mo));})]);});},function(_Mp){return new F(function(){return A(_H5,[_Mg,_Mh,_Mi,function(_Mq,_Mr,_Ms){return new F(function(){return A(_Mj,[_Mq,_Mr,new T(function(){var _Mt=E(_Ml),_Mu=E(_Mt[1]),_Mv=E(_Mp),_Mw=E(_Mv[1]),_Mx=E(_Ms),_My=E(_Mx[1]),_Mz=B(_cW(_Mw[1],_Mw[2],_Mw[3],_Mv[2],_My[1],_My[2],_My[3],_Mx[2])),_MA=E(_Mz[1]),_MB=B(_cW(_Mu[1],_Mu[2],_Mu[3],_Mt[2],_MA[1],_MA[2],_MA[3],_Mz[2]));return [0,E(_MB[1]),_MB[2]];})]);});},function(_MC){return new F(function(){return A(_Mj,[new T(function(){return B(A(_M8,[_M1,_Mf]));}),_Mg,new T(function(){var _MD=E(E(_Mg)[2]),_ME=E(_Ml),_MF=E(_ME[1]),_MG=E(_Mp),_MH=E(_MG[1]),_MI=E(_MC),_MJ=E(_MI[1]),_MK=B(_cW(_MJ[1],_MJ[2],_MJ[3],_MI[2],_MD[1],_MD[2],_MD[3],_9)),_ML=E(_MK[1]),_MM=B(_cW(_MH[1],_MH[2],_MH[3],_MG[2],_ML[1],_ML[2],_ML[3],_MK[2])),_MN=E(_MM[1]),_MO=B(_cW(_MF[1],_MF[2],_MF[3],_ME[2],_MN[1],_MN[2],_MN[3],_MM[2]));return [0,E(_MO[1]),_MO[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _Ik(_M9,function(_MP,_MQ,_MR){return new F(function(){return A(_Me,[_MP,_MQ,_Ma,_Mb,function(_MS,_MT,_MU){return new F(function(){return A(_Ma,[_MS,_MT,new T(function(){return B(_dL(_MR,_MU));})]);});},function(_MV){return new F(function(){return A(_Mb,[new T(function(){return B(_dL(_MR,_MV));})]);});}]);});},_Mb,function(_MW,_MX,_MY){return new F(function(){return A(_Me,[_MW,_MX,_Ma,_Mb,function(_MZ,_N0,_N1){return new F(function(){return A(_Mc,[_MZ,_N0,new T(function(){return B(_dL(_MY,_N1));})]);});},function(_N2){return new F(function(){return A(_Md,[new T(function(){return B(_dL(_MY,_N2));})]);});}]);});},_Md);});};return new F(function(){return _jw(function(_N3,_N4,_N5,_N6,_N7){return new F(function(){return _IT(_M1,_N3,_N4,_N5,_N6,function(_N8){return new F(function(){return _KF(_M1,_N3,_N4,_N5,function(_N9,_Na,_Nb){return new F(function(){return A(_N6,[_N9,_Na,new T(function(){return B(_dL(_N8,_Nb));})]);});},function(_Nc){var _Nd=function(_Ne){return new F(function(){return A(_N6,[_M1,_N3,new T(function(){var _Nf=E(E(_N3)[2]),_Ng=E(_N8),_Nh=E(_Ng[1]),_Ni=E(_Nc),_Nj=E(_Ni[1]),_Nk=E(_Ne),_Nl=E(_Nk[1]),_Nm=B(_cW(_Nl[1],_Nl[2],_Nl[3],_Nk[2],_Nf[1],_Nf[2],_Nf[3],_9)),_Nn=E(_Nm[1]),_No=B(_cW(_Nj[1],_Nj[2],_Nj[3],_Ni[2],_Nn[1],_Nn[2],_Nn[3],_Nm[2])),_Np=E(_No[1]),_Nq=B(_cW(_Nh[1],_Nh[2],_Nh[3],_Ng[2],_Np[1],_Np[2],_Np[3],_No[2]));return [0,E(_Nq[1]),_Nq[2]];})]);});};return new F(function(){return _Gg(_H4,_N3,function(_Nr,_Ns,_Nt){return new F(function(){return _M7(_Nr,_Ns,_N4,_N5,function(_Nu,_Nv,_Nw){return new F(function(){return A(_N4,[_Nu,_Nv,new T(function(){return B(_dL(_Nt,_Nw));})]);});},function(_Nx){return new F(function(){return A(_N5,[new T(function(){return B(_dL(_Nt,_Nx));})]);});});});},_N5,function(_Ny,_Nz,_NA){return new F(function(){return _M7(_Ny,_Nz,_N4,_N5,function(_NB,_NC,_ND){return new F(function(){return A(_N6,[_NB,_NC,new T(function(){var _NE=E(_N8),_NF=E(_NE[1]),_NG=E(_Nc),_NH=E(_NG[1]),_NI=E(_NA),_NJ=E(_NI[1]),_NK=E(_ND),_NL=E(_NK[1]),_NM=B(_cW(_NJ[1],_NJ[2],_NJ[3],_NI[2],_NL[1],_NL[2],_NL[3],_NK[2])),_NN=E(_NM[1]),_NO=B(_cW(_NH[1],_NH[2],_NH[3],_NG[2],_NN[1],_NN[2],_NN[3],_NM[2])),_NP=E(_NO[1]),_NQ=B(_cW(_NF[1],_NF[2],_NF[3],_NE[2],_NP[1],_NP[2],_NP[3],_NO[2]));return [0,E(_NQ[1]),_NQ[2]];})]);});},function(_NR){return new F(function(){return _Nd(new T(function(){var _NS=E(_NA),_NT=E(_NS[1]),_NU=E(_NR),_NV=E(_NU[1]),_NW=B(_cW(_NT[1],_NT[2],_NT[3],_NS[2],_NV[1],_NV[2],_NV[3],_NU[2]));return [0,E(_NW[1]),_NW[2]];},1));});});});},_Nd);});});});});});},_Gx,_M2,_M3,_M4,_M5,_M6);});};_GO=function(_NX,_NY,_NZ,_O0,_O1){return new F(function(){return _Ik(_NX,function(_O2,_O3,_O4){return new F(function(){return _M0(_O2,_O3,_NY,_NZ,function(_O5,_O6,_O7){return new F(function(){return A(_NY,[_O5,_O6,new T(function(){return B(_dL(_O4,_O7));})]);});},function(_O8){return new F(function(){return A(_NZ,[new T(function(){return B(_dL(_O4,_O8));})]);});});});},_NZ,function(_O9,_Oa,_Ob){return new F(function(){return _M0(_O9,_Oa,_NY,_NZ,function(_Oc,_Od,_Oe){return new F(function(){return A(_O0,[_Oc,_Od,new T(function(){return B(_dL(_Ob,_Oe));})]);});},function(_Of){return new F(function(){return A(_O1,[new T(function(){return B(_dL(_Ob,_Of));})]);});});});},_O1);});};_GP=_GT[2];return null;}})(_GO,_GP);if(_GQ!=null){return _GQ;}}},_Og=0,_Oh=[3,_],_Oi=function(_Oj,_Ok){return [5,_Oh,_Oj,_Ok];},_Ol=new T(function(){return B(unCStr("=>"));}),_Om=function(_On){return E(E(_On)[1]);},_Oo=function(_Op,_Oq,_Or,_Os){while(1){var _Ot=E(_Os);if(!_Ot[0]){return [0,_Op,_Oq,_Or];}else{var _Ou=_Ot[2];switch(E(E(_Ot[1])[1])){case 9:var _Ov=(_Or+8|0)-B(_ge(_Or-1|0,8))|0;_Os=_Ou;_Or=_Ov;continue;case 10:var _Ow=_Oq+1|0;_Or=1;_Os=_Ou;_Oq=_Ow;continue;default:var _Ov=_Or+1|0;_Os=_Ou;_Or=_Ov;continue;}}}},_Ox=function(_Oy){return E(E(_Oy)[1]);},_Oz=function(_OA){return E(E(_OA)[2]);},_OB=function(_OC){return [0,E(E(_OC)[2]),_9];},_OD=function(_OE,_OF,_OG,_OH,_OI,_OJ,_OK){var _OL=E(_OF);if(!_OL[0]){return new F(function(){return A(_OJ,[_9,_OG,new T(function(){return B(_OB(_OG));})]);});}else{var _OM=E(_OG),_ON=E(_OM[2]),_OO=new T(function(){return B(_Om(_OE));}),_OP=[0,E(_ON),[1,[2,E([1,_ga,new T(function(){return B(_i0(_OL,_gb));})])],_gd]],_OQ=[2,E([1,_ga,new T(function(){return B(_i0(_OL,_gb));})])],_OR=new T(function(){var _OS=B(_Oo(_ON[1],_ON[2],_ON[3],_OL));return [0,_OS[1],_OS[2],_OS[3]];}),_OT=function(_OU,_OV){var _OW=E(_OU);if(!_OW[0]){return new F(function(){return A(_OH,[_OL,new T(function(){return [0,_OV,E(E(_OR)),E(_OM[3])];}),new T(function(){return [0,E(E(_OR)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_Ox(_OO));}),[new T(function(){return B(A(new T(function(){return B(_Oz(_OE));}),[_OV]));}),function(_OX){var _OY=E(_OX);if(!_OY[0]){return E(new T(function(){return B(A(_OI,[_OP]));}));}else{var _OZ=E(_OY[1]),_P0=E(_OZ[1]);return E(_OW[1])[1]!=_P0[1]?B(A(_OI,[[0,E(_ON),[1,_OQ,[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_P0,_9],_gb));})])],_9]]]])):B(_OT(_OW[2],_OZ[2]));}}]);});}};return new F(function(){return A(_Ox,[_OO,new T(function(){return B(A(_Oz,[_OE,_OM[1]]));}),function(_P1){var _P2=E(_P1);if(!_P2[0]){return E(new T(function(){return B(A(_OK,[_OP]));}));}else{var _P3=E(_P2[1]),_P4=E(_P3[1]);return E(_OL[1])[1]!=_P4[1]?B(A(_OK,[[0,E(_ON),[1,_OQ,[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_P4,_9],_gb));})])],_9]]]])):B(_OT(_OL[2],_P3[2]));}}]);});}},_P5=function(_P6,_P7,_P8,_P9,_Pa){return new F(function(){return _OD(_kG,_Ol,_P6,function(_Pb,_Pc,_Pd){return new F(function(){return A(_P7,[_Oi,_Pc,new T(function(){var _Pe=E(E(_Pc)[2]),_Pf=E(_Pd),_Pg=E(_Pf[1]),_Ph=B(_cW(_Pg[1],_Pg[2],_Pg[3],_Pf[2],_Pe[1],_Pe[2],_Pe[3],_9));return [0,E(_Ph[1]),_Ph[2]];})]);});},_P8,function(_Pi,_Pj,_Pk){return new F(function(){return A(_P9,[_Oi,_Pj,new T(function(){var _Pl=E(E(_Pj)[2]),_Pm=E(_Pk),_Pn=E(_Pm[1]),_Po=B(_cW(_Pn[1],_Pn[2],_Pn[3],_Pm[2],_Pl[1],_Pl[2],_Pl[3],_9));return [0,E(_Po[1]),_Po[2]];})]);});},_Pa);});},_Pp=[0,_P5,_Og],_Pq=[1,_Pp,_9],_Pr=[1,_Pq,_9],_Ps=1,_Pt=[2,_],_Pu=function(_Oj,_Ok){return [5,_Pt,_Oj,_Ok];},_Pv=new T(function(){return B(unCStr("\\/"));}),_Pw=function(_Px,_Py,_Pz,_PA,_PB){return new F(function(){return _OD(_kG,_Pv,_Px,function(_PC,_PD,_PE){return new F(function(){return A(_Py,[_Pu,_PD,new T(function(){var _PF=E(E(_PD)[2]),_PG=E(_PE),_PH=E(_PG[1]),_PI=B(_cW(_PH[1],_PH[2],_PH[3],_PG[2],_PF[1],_PF[2],_PF[3],_9));return [0,E(_PI[1]),_PI[2]];})]);});},_Pz,function(_PJ,_PK,_PL){return new F(function(){return A(_PA,[_Pu,_PK,new T(function(){var _PM=E(E(_PK)[2]),_PN=E(_PL),_PO=E(_PN[1]),_PP=B(_cW(_PO[1],_PO[2],_PO[3],_PN[2],_PM[1],_PM[2],_PM[3],_9));return [0,E(_PP[1]),_PP[2]];})]);});},_PB);});},_PQ=[0,_Pw,_Ps],_PR=[1,_],_PS=function(_Oj,_Ok){return [5,_PR,_Oj,_Ok];},_PT=new T(function(){return B(unCStr("/\\"));}),_PU=function(_PV,_PW,_PX,_PY,_PZ){return new F(function(){return _OD(_kG,_PT,_PV,function(_Q0,_Q1,_Q2){return new F(function(){return A(_PW,[_PS,_Q1,new T(function(){var _Q3=E(E(_Q1)[2]),_Q4=E(_Q2),_Q5=E(_Q4[1]),_Q6=B(_cW(_Q5[1],_Q5[2],_Q5[3],_Q4[2],_Q3[1],_Q3[2],_Q3[3],_9));return [0,E(_Q6[1]),_Q6[2]];})]);});},_PX,function(_Q7,_Q8,_Q9){return new F(function(){return A(_PY,[_PS,_Q8,new T(function(){var _Qa=E(E(_Q8)[2]),_Qb=E(_Q9),_Qc=E(_Qb[1]),_Qd=B(_cW(_Qc[1],_Qc[2],_Qc[3],_Qb[2],_Qa[1],_Qa[2],_Qa[3],_9));return [0,E(_Qd[1]),_Qd[2]];})]);});},_PZ);});},_Qe=[0,_PU,_Ps],_Qf=[1,_Qe,_9],_Qg=[1,_PQ,_Qf],_Qh=[1,_Qg,_Pr],_Qi=[0,_],_Qj=function(_Ok){return [4,_Qi,_Ok];},_Qk=[0,45],_Ql=[1,_Qk,_9],_Qm=function(_Qn,_Qo,_Qp,_Qq,_Qr){return new F(function(){return _OD(_kG,_Ql,_Qn,function(_Qs,_Qt,_Qu){return new F(function(){return A(_Qo,[_Qj,_Qt,new T(function(){var _Qv=E(E(_Qt)[2]),_Qw=E(_Qu),_Qx=E(_Qw[1]),_Qy=B(_cW(_Qx[1],_Qx[2],_Qx[3],_Qw[2],_Qv[1],_Qv[2],_Qv[3],_9));return [0,E(_Qy[1]),_Qy[2]];})]);});},_Qp,function(_Qz,_QA,_QB){return new F(function(){return A(_Qq,[_Qj,_QA,new T(function(){var _QC=E(E(_QA)[2]),_QD=E(_QB),_QE=E(_QD[1]),_QF=B(_cW(_QE[1],_QE[2],_QE[3],_QD[2],_QC[1],_QC[2],_QC[3],_9));return [0,E(_QF[1]),_QF[2]];})]);});},_Qr);});},_QG=[1,_Qm],_QH=[1,_QG,_9],_QI=[1,_QH,_Qh],_QJ=new T(function(){return B(unCStr("number"));}),_QK=[1,_QJ,_9],_QL=new T(function(){return B(err(_kL));}),_QM=new T(function(){return B(err(_kJ));}),_QN=new T(function(){return B(_us(_uO,_uf,_uU));}),_QO=function(_QP){return function(_QQ,_QR,_QS,_QT,_QU){return new F(function(){return A(_QT,[new T(function(){var _QV=B(_uZ(B(_kO(_QN,_QP))));return _QV[0]==0?E(_QM):E(_QV[2])[0]==0?E(_QV[1]):E(_QL);}),_QQ,new T(function(){return [0,E(E(_QQ)[2]),_9];})]);});};},_QW=function(_QX,_QY,_QZ,_R0,_R1){return new F(function(){return _dT(_ku,_QX,function(_R2,_R3,_R4){return new F(function(){return A(_QO,[_R2,_R3,_QY,_QZ,function(_R5,_R6,_R7){return new F(function(){return A(_QY,[_R5,_R6,new T(function(){return B(_dL(_R4,_R7));})]);});},function(_R8){return new F(function(){return A(_QZ,[new T(function(){return B(_dL(_R4,_R8));})]);});}]);});},_QZ,function(_R9,_Ra,_Rb){return new F(function(){return A(_QO,[_R9,_Ra,_QY,_QZ,function(_Rc,_Rd,_Re){return new F(function(){return A(_R0,[_Rc,_Rd,new T(function(){return B(_dL(_Rb,_Re));})]);});},function(_Rf){return new F(function(){return A(_R1,[new T(function(){return B(_dL(_Rb,_Rf));})]);});}]);});},_R1);});},_Rg=function(_Rh,_Ri,_Rj,_Rk,_Rl){return new F(function(){return _QW(_Rh,function(_Rm,_Rn,_Ro){return new F(function(){return A(_Ri,[[1,[0,_,_Rm]],_Rn,new T(function(){var _Rp=E(E(_Rn)[2]),_Rq=E(_Ro),_Rr=E(_Rq[1]),_Rs=B(_cW(_Rr[1],_Rr[2],_Rr[3],_Rq[2],_Rp[1],_Rp[2],_Rp[3],_9));return [0,E(_Rs[1]),_Rs[2]];})]);});},_Rj,function(_Rt,_Ru,_Rv){return new F(function(){return A(_Rk,[[1,[0,_,_Rt]],_Ru,new T(function(){var _Rw=E(E(_Ru)[2]),_Rx=_Rw[1],_Ry=_Rw[2],_Rz=_Rw[3],_RA=E(_Rv),_RB=E(_RA[1]),_RC=_RB[2],_RD=_RB[3],_RE=E(_RA[2]);if(!_RE[0]){switch(B(_cO(_RB[1],_Rx))){case 0:var _RF=[0,E(_Rw),_9];break;case 1:if(_RC>=_Ry){if(_RC!=_Ry){var _RG=[0,E(_RB),_9];}else{if(_RD>=_Rz){var _RH=_RD!=_Rz?[0,E(_RB),_9]:[0,E(_RB),_cV];}else{var _RH=[0,E(_Rw),_9];}var _RI=_RH,_RG=_RI;}var _RJ=_RG,_RK=_RJ;}else{var _RK=[0,E(_Rw),_9];}var _RL=_RK,_RF=_RL;break;default:var _RF=[0,E(_RB),_9];}var _RM=_RF;}else{var _RN=B(_jb(_RB,_RE,_QK)),_RO=E(_RN[1]),_RP=B(_cW(_RO[1],_RO[2],_RO[3],_RN[2],_Rx,_Ry,_Rz,_9)),_RM=[0,E(_RP[1]),_RP[2]];}var _RQ=_RM,_RR=_RQ,_RS=_RR,_RT=_RS;return _RT;})]);});},function(_RU){return new F(function(){return A(_Rl,[new T(function(){var _RV=E(_RU),_RW=B(_jb(_RV[1],_RV[2],_QK));return [0,E(_RW[1]),_RW[2]];})]);});});});},_RX=new T(function(){return B(unCStr("P_"));}),_RY=function(_RZ,_S0,_S1,_S2,_S3){return new F(function(){return _OD(_kG,_RX,_RZ,function(_S4,_S5,_S6){return new F(function(){return _Rg(_S5,_S0,_S1,function(_S7,_S8,_S9){return new F(function(){return A(_S0,[_S7,_S8,new T(function(){return B(_dL(_S6,_S9));})]);});},function(_Sa){return new F(function(){return A(_S1,[new T(function(){return B(_dL(_S6,_Sa));})]);});});});},_S1,function(_Sb,_Sc,_Sd){return new F(function(){return _Rg(_Sc,_S0,_S1,function(_Se,_Sf,_Sg){return new F(function(){return A(_S2,[_Se,_Sf,new T(function(){return B(_dL(_Sd,_Sg));})]);});},function(_Sh){return new F(function(){return A(_S3,[new T(function(){return B(_dL(_Sd,_Sh));})]);});});});},_S3);});},_Si=[0,41],_Sj=new T(function(){return B(_jN(_kG,_Si));}),_Sk=function(_Sl,_Sm,_Sn,_So,_Sp,_Sq){return new F(function(){return A(_Sj,[_Sm,function(_Sr,_Ss,_St){return new F(function(){return A(_Sn,[_Sl,_Ss,new T(function(){var _Su=E(E(_Ss)[2]),_Sv=E(_St),_Sw=E(_Sv[1]),_Sx=B(_cW(_Sw[1],_Sw[2],_Sw[3],_Sv[2],_Su[1],_Su[2],_Su[3],_9));return [0,E(_Sx[1]),_Sx[2]];})]);});},_So,function(_Sy,_Sz,_SA){return new F(function(){return A(_Sp,[_Sl,_Sz,new T(function(){var _SB=E(E(_Sz)[2]),_SC=E(_SA),_SD=E(_SC[1]),_SE=B(_cW(_SD[1],_SD[2],_SD[3],_SC[2],_SB[1],_SB[2],_SB[3],_9));return [0,E(_SE[1]),_SE[2]];})]);});},_Sq]);});},_SF=function(_SG,_SH,_SI,_SJ,_SK){return new F(function(){return A(_SL,[_SG,function(_SM,_SN,_SO){return new F(function(){return _Sk(_SM,_SN,_SH,_SI,function(_SP,_SQ,_SR){return new F(function(){return A(_SH,[_SP,_SQ,new T(function(){return B(_dL(_SO,_SR));})]);});},function(_SS){return new F(function(){return A(_SI,[new T(function(){return B(_dL(_SO,_SS));})]);});});});},_SI,function(_ST,_SU,_SV){return new F(function(){return _Sk(_ST,_SU,_SH,_SI,function(_SW,_SX,_SY){return new F(function(){return A(_SJ,[_SW,_SX,new T(function(){return B(_dL(_SV,_SY));})]);});},function(_SZ){return new F(function(){return A(_SK,[new T(function(){return B(_dL(_SV,_SZ));})]);});});});},_SK]);});},_T0=[0,40],_T1=new T(function(){return B(_jN(_kG,_T0));}),_T2=function(_T3,_T4,_T5,_T6,_T7){var _T8=function(_T9){return new F(function(){return _RY(_T3,_T4,_T5,function(_Ta,_Tb,_Tc){return new F(function(){return A(_T6,[_Ta,_Tb,new T(function(){return B(_dL(_T9,_Tc));})]);});},function(_Td){return new F(function(){return A(_T7,[new T(function(){return B(_dL(_T9,_Td));})]);});});});};return new F(function(){return A(_T1,[_T3,function(_Te,_Tf,_Tg){return new F(function(){return _SF(_Tf,_T4,_T5,function(_Th,_Ti,_Tj){return new F(function(){return A(_T4,[_Th,_Ti,new T(function(){return B(_dL(_Tg,_Tj));})]);});},function(_Tk){return new F(function(){return A(_T5,[new T(function(){return B(_dL(_Tg,_Tk));})]);});});});},_T5,function(_Tl,_Tm,_Tn){return new F(function(){return _SF(_Tm,_T4,_T5,function(_To,_Tp,_Tq){return new F(function(){return A(_T6,[_To,_Tp,new T(function(){return B(_dL(_Tn,_Tq));})]);});},function(_Tr){return new F(function(){return _T8(new T(function(){return B(_dL(_Tn,_Tr));}));});});});},_T8]);});},_SL=new T(function(){return B(_GN(_T2,_QI));}),_Ts=function(_Tt,_Tu,_Tv,_Tw,_Tx){return new F(function(){return A(_SL,[_Tt,function(_Ty,_Tz,_TA){return new F(function(){return _EX(_Ty,_Tz,_Tu,_Tv,function(_TB,_TC,_TD){return new F(function(){return A(_Tu,[_TB,_TC,new T(function(){return B(_dL(_TA,_TD));})]);});},function(_TE){return new F(function(){return A(_Tv,[new T(function(){return B(_dL(_TA,_TE));})]);});});});},_Tv,function(_TF,_TG,_TH){return new F(function(){return _EX(_TF,_TG,_Tu,_Tv,function(_TI,_TJ,_TK){return new F(function(){return A(_Tw,[_TI,_TJ,new T(function(){return B(_dL(_TH,_TK));})]);});},function(_TL){return new F(function(){return A(_Tx,[new T(function(){return B(_dL(_TH,_TL));})]);});});});},_Tx]);});},_TM=function(_TN,_TO,_TP,_TQ,_TR){return new F(function(){return _ew(_iS,_TN,function(_TS,_TT,_TU){return new F(function(){return _Ts(_TT,_TO,_TP,function(_TV,_TW,_TX){return new F(function(){return A(_TO,[_TV,_TW,new T(function(){return B(_dL(_TU,_TX));})]);});},function(_TY){return new F(function(){return A(_TP,[new T(function(){return B(_dL(_TU,_TY));})]);});});});},_TP,function(_TZ,_U0,_U1){return new F(function(){return _Ts(_U0,_TO,_TP,function(_U2,_U3,_U4){return new F(function(){return A(_TQ,[_U2,_U3,new T(function(){return B(_dL(_U1,_U4));})]);});},function(_U5){return new F(function(){return A(_TR,[new T(function(){return B(_dL(_U1,_U5));})]);});});});});});},_U6=function(_U7,_U8,_U9,_Ua,_Ub,_Uc,_Ud,_Ue){var _Uf=E(_U7);if(!_Uf[0]){return new F(function(){return A(_Ue,[[0,E([0,_U8,_U9,_Ua]),_gd]]);});}else{var _Ug=_Uf[1];if(!B(_86(_iy,_Ug,_xr))){return new F(function(){return A(_Ue,[[0,E([0,_U8,_U9,_Ua]),[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_Ug,_9],_gb));})])],_9]]]);});}else{var _Uh=function(_Ui,_Uj,_Uk,_Ul){var _Um=[0,E([0,_Ui,_Uj,_Uk]),_9],_Un=[0,E([0,_Ui,_Uj,_Uk]),_cV];return new F(function(){return _ew(_xY,[0,_Uf[2],E(_Ul),E(_Ub)],function(_Uo,_Up,_Uq){return new F(function(){return _TM(_Up,_Uc,_Ud,function(_Ur,_Us,_Ut){return new F(function(){return A(_Uc,[_Ur,_Us,new T(function(){return B(_dL(_Uq,_Ut));})]);});},function(_Uu){return new F(function(){return A(_Ud,[new T(function(){return B(_dL(_Uq,_Uu));})]);});});});},_Ud,function(_Uv,_Uw,_Ux){return new F(function(){return _TM(_Uw,_Uc,_Ud,function(_Uy,_Uz,_UA){return new F(function(){return A(_Uc,[_Uy,_Uz,new T(function(){var _UB=E(_Ux),_UC=E(_UB[1]),_UD=E(_UA),_UE=E(_UD[1]),_UF=B(_cW(_UC[1],_UC[2],_UC[3],_UB[2],_UE[1],_UE[2],_UE[3],_UD[2])),_UG=E(_UF[1]),_UH=_UG[2],_UI=_UG[3],_UJ=E(_UF[2]);if(!_UJ[0]){switch(B(_cO(_Ui,_UG[1]))){case 0:var _UK=[0,E(_UG),_9];break;case 1:if(_Uj>=_UH){if(_Uj!=_UH){var _UL=E(_Um);}else{if(_Uk>=_UI){var _UM=_Uk!=_UI?E(_Um):E(_Un);}else{var _UM=[0,E(_UG),_9];}var _UN=_UM,_UL=_UN;}var _UO=_UL,_UP=_UO;}else{var _UP=[0,E(_UG),_9];}var _UQ=_UP,_UK=_UQ;break;default:var _UK=E(_Um);}var _UR=_UK;}else{var _UR=[0,E(_UG),_UJ];}var _US=_UR,_UT=_US,_UU=_UT,_UV=_UU,_UW=_UV,_UX=_UW;return _UX;})]);});},function(_UY){return new F(function(){return A(_Ud,[new T(function(){var _UZ=E(_Ux),_V0=E(_UZ[1]),_V1=E(_UY),_V2=E(_V1[1]),_V3=B(_cW(_V0[1],_V0[2],_V0[3],_UZ[2],_V2[1],_V2[2],_V2[3],_V1[2])),_V4=E(_V3[1]),_V5=_V4[2],_V6=_V4[3],_V7=E(_V3[2]);if(!_V7[0]){switch(B(_cO(_Ui,_V4[1]))){case 0:var _V8=[0,E(_V4),_9];break;case 1:if(_Uj>=_V5){if(_Uj!=_V5){var _V9=E(_Um);}else{if(_Uk>=_V6){var _Va=_Uk!=_V6?E(_Um):E(_Un);}else{var _Va=[0,E(_V4),_9];}var _Vb=_Va,_V9=_Vb;}var _Vc=_V9,_Vd=_Vc;}else{var _Vd=[0,E(_V4),_9];}var _Ve=_Vd,_V8=_Ve;break;default:var _V8=E(_Um);}var _Vf=_V8;}else{var _Vf=[0,E(_V4),_V7];}var _Vg=_Vf,_Vh=_Vg,_Vi=_Vh,_Vj=_Vi,_Vk=_Vj,_Vl=_Vk;return _Vl;})]);});});});});});};switch(E(E(_Ug)[1])){case 9:var _Vm=(_Ua+8|0)-B(_ge(_Ua-1|0,8))|0;return new F(function(){return _Uh(_U8,_U9,_Vm,[0,_U8,_U9,_Vm]);});break;case 10:var _Vn=_U9+1|0;return new F(function(){return _Uh(_U8,_Vn,1,[0,_U8,_Vn,1]);});break;default:var _Vo=_Ua+1|0;return new F(function(){return _Uh(_U8,_U9,_Vo,[0,_U8,_U9,_Vo]);});}}}},_Vp=function(_Vq,_Vr,_Vs,_Vt,_Vu,_Vv){var _Vw=function(_Vx,_Vy,_Vz,_VA,_VB,_VC){var _VD=function(_VE){var _VF=[0,[1,[0,_Vq,_Vx,new T(function(){return B(_7X(_v6,_VE));})]],_9];return function(_VG,_VH,_VI,_VJ,_VK){return new F(function(){return A(_ke,[_VG,function(_VL,_VM,_VN){return new F(function(){return A(_VH,[_VF,_VM,new T(function(){var _VO=E(E(_VM)[2]),_VP=E(_VN),_VQ=E(_VP[1]),_VR=B(_cW(_VQ[1],_VQ[2],_VQ[3],_VP[2],_VO[1],_VO[2],_VO[3],_9));return [0,E(_VR[1]),_VR[2]];})]);});},_VK,function(_VS,_VT,_VU){return new F(function(){return A(_VJ,[_VF,_VT,new T(function(){var _VV=E(E(_VT)[2]),_VW=E(_VU),_VX=E(_VW[1]),_VY=B(_cW(_VX[1],_VX[2],_VX[3],_VW[2],_VV[1],_VV[2],_VV[3],_9));return [0,E(_VY[1]),_VY[2]];})]);});},_VK]);});};},_VZ=function(_W0,_W1,_W2,_W3,_W4){var _W5=function(_W6,_W7,_W8){return new F(function(){return A(_VD,[_W6,_W7,_W1,_W2,function(_W9,_Wa,_Wb){return new F(function(){return A(_W3,[_W9,_Wa,new T(function(){return B(_dL(_W8,_Wb));})]);});},function(_Wc){return new F(function(){return A(_W4,[new T(function(){return B(_dL(_W8,_Wc));})]);});}]);});},_Wd=function(_We){return new F(function(){return _W5(_9,_W0,new T(function(){var _Wf=E(E(_W0)[2]),_Wg=E(_We),_Wh=E(_Wg[1]),_Wi=B(_cW(_Wh[1],_Wh[2],_Wh[3],_Wg[2],_Wf[1],_Wf[2],_Wf[3],_9));return [0,E(_Wi[1]),_Wi[2]];}));});};return new F(function(){return _eW(_kA,_kI,_W0,function(_Wj,_Wk,_Wl){return new F(function(){return A(_VD,[_Wj,_Wk,_W1,_W2,function(_Wm,_Wn,_Wo){return new F(function(){return A(_W1,[_Wm,_Wn,new T(function(){return B(_dL(_Wl,_Wo));})]);});},function(_Wp){return new F(function(){return A(_W2,[new T(function(){return B(_dL(_Wl,_Wp));})]);});}]);});},_Wd,_W5,_Wd);});};return new F(function(){return _ew(_iS,_Vy,function(_Wq,_Wr,_Ws){return new F(function(){return _VZ(_Wr,_Vz,_VA,function(_Wt,_Wu,_Wv){return new F(function(){return A(_Vz,[_Wt,_Wu,new T(function(){return B(_dL(_Ws,_Wv));})]);});},function(_Ww){return new F(function(){return A(_VA,[new T(function(){return B(_dL(_Ws,_Ww));})]);});});});},_VA,function(_Wx,_Wy,_Wz){return new F(function(){return _VZ(_Wy,_Vz,_VA,function(_WA,_WB,_WC){return new F(function(){return A(_VB,[_WA,_WB,new T(function(){return B(_dL(_Wz,_WC));})]);});},function(_WD){return new F(function(){return A(_VC,[new T(function(){return B(_dL(_Wz,_WD));})]);});});});});});},_WE=function(_WF,_WG,_WH,_WI,_WJ){return new F(function(){return _dT(_wv,_WF,function(_WK,_WL,_WM){return new F(function(){return _Vw(_WK,_WL,_WG,_WH,function(_WN,_WO,_WP){return new F(function(){return A(_WG,[_WN,_WO,new T(function(){return B(_dL(_WM,_WP));})]);});},function(_WQ){return new F(function(){return A(_WH,[new T(function(){return B(_dL(_WM,_WQ));})]);});});});},_WJ,function(_WR,_WS,_WT){return new F(function(){return _Vw(_WR,_WS,_WG,_WH,function(_WU,_WV,_WW){return new F(function(){return A(_WI,[_WU,_WV,new T(function(){return B(_dL(_WT,_WW));})]);});},function(_WX){return new F(function(){return A(_WJ,[new T(function(){return B(_dL(_WT,_WX));})]);});});});},_WJ);});};return new F(function(){return _ew(_iS,_Vr,function(_WY,_WZ,_X0){return new F(function(){return _WE(_WZ,_Vs,_Vt,function(_X1,_X2,_X3){return new F(function(){return A(_Vs,[_X1,_X2,new T(function(){return B(_dL(_X0,_X3));})]);});},function(_X4){return new F(function(){return A(_Vt,[new T(function(){return B(_dL(_X0,_X4));})]);});});});},_Vt,function(_X5,_X6,_X7){return new F(function(){return _WE(_X6,_Vs,_Vt,function(_X8,_X9,_Xa){return new F(function(){return A(_Vu,[_X8,_X9,new T(function(){return B(_dL(_X7,_Xa));})]);});},function(_Xb){return new F(function(){return A(_Vv,[new T(function(){return B(_dL(_X7,_Xb));})]);});});});});});},_Xc=function(_Xd,_Xe,_Xf,_Xg,_Xh){return new F(function(){return A(_SL,[_Xd,function(_Xi,_Xj,_Xk){return new F(function(){return _Vp(_Xi,_Xj,_Xe,_Xf,function(_Xl,_Xm,_Xn){return new F(function(){return A(_Xe,[_Xl,_Xm,new T(function(){return B(_dL(_Xk,_Xn));})]);});},function(_Xo){return new F(function(){return A(_Xf,[new T(function(){return B(_dL(_Xk,_Xo));})]);});});});},_Xf,function(_Xp,_Xq,_Xr){return new F(function(){return _Vp(_Xp,_Xq,_Xe,_Xf,function(_Xs,_Xt,_Xu){return new F(function(){return A(_Xg,[_Xs,_Xt,new T(function(){return B(_dL(_Xr,_Xu));})]);});},function(_Xv){return new F(function(){return A(_Xh,[new T(function(){return B(_dL(_Xr,_Xv));})]);});});});},_Xh]);});},_Xw=function(_Xx,_Xy,_Xz,_XA,_XB){return new F(function(){return _Xc(_Xx,_Xy,_Xz,_XA,function(_XC){var _XD=E(_Xx),_XE=E(_XD[2]);return new F(function(){return _U6(_XD[1],_XE[1],_XE[2],_XE[3],_XD[3],_Xy,_Xz,function(_XF){return new F(function(){return A(_XB,[new T(function(){return B(_dL(_XC,_XF));})]);});});});});});},_Ev=function(_XG,_XH,_XI,_XJ,_XK){return new F(function(){return _dT(_Xw,_XG,function(_XL,_XM,_XN){return new F(function(){return _wX(_XL,_XM,_XH,function(_XO,_XP,_XQ){return new F(function(){return A(_XH,[_XO,_XP,new T(function(){return B(_dL(_XN,_XQ));})]);});});});},_XI,function(_XR,_XS,_XT){return new F(function(){return _wX(_XR,_XS,_XH,function(_XU,_XV,_XW){return new F(function(){return A(_XJ,[_XU,_XV,new T(function(){return B(_dL(_XT,_XW));})]);});});});},_XK);});},_XX=function(_XY,_XZ,_Y0){while(1){var _Y1=E(_XZ);if(!_Y1[0]){return E(_Y0)[0]==0?true:false;}else{var _Y2=E(_Y0);if(!_Y2[0]){return false;}else{if(!B(A(_84,[_XY,_Y1[1],_Y2[1]]))){return false;}else{_XZ=_Y1[2];_Y0=_Y2[2];continue;}}}}},_Y3=function(_Y4,_Y5,_Y6){var _Y7=E(_Y5),_Y8=E(_Y6);return !B(_XX(_Y4,_Y7[1],_Y8[1]))?true:!B(A(_84,[_Y4,_Y7[2],_Y8[2]]))?true:false;},_Y9=function(_Ya,_Yb,_Yc,_Yd,_Ye){return !B(_XX(_Ya,_Yb,_Yd))?false:B(A(_84,[_Ya,_Yc,_Ye]));},_Yf=function(_Yg,_Yh,_Yi){var _Yj=E(_Yh),_Yk=E(_Yi);return new F(function(){return _Y9(_Yg,_Yj[1],_Yj[2],_Yk[1],_Yk[2]);});},_Yl=function(_Ym){return [0,function(_Yn,_Yo){return new F(function(){return _Yf(_Ym,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _Y3(_Ym,_Yn,_Yo);});}];},_Yp=function(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx,_Yy){return new F(function(){return _lv(B(_aA(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx)),B(_aA(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yy)));});},_Yz=function(_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI){return !B(_Yp(_YA,_YB,_YC,_YD,_YE,_YF,_YG,_YH,_YI))?true:false;},_YJ=function(_YK,_YL,_YM,_YN,_YO,_YP,_YQ){return [0,function(_bi,_bj){return new F(function(){return _Yp(_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _Yz(_YK,_YL,_YM,_YN,_YO,_YP,_YQ,_bi,_bj);});}];},_YR=function(_YS,_YT,_YU){var _YV=E(_YT),_YW=E(_YU);return !B(_XX(_YS,_YV[1],_YW[1]))?true:!B(A(_84,[_YS,_YV[2],_YW[2]]))?true:false;},_YX=function(_YY,_YZ,_Z0){var _Z1=E(_YZ),_Z2=E(_Z0);return new F(function(){return _Y9(_YY,_Z1[1],_Z1[2],_Z2[1],_Z2[2]);});},_Z3=function(_Z4){return [0,function(_Yn,_Yo){return new F(function(){return _YX(_Z4,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _YR(_Z4,_Yn,_Yo);});}];},_Z5=function(_Z6,_Z7,_Z8){var _Z9=E(_Z6);switch(_Z9[0]){case 0:var _Za=E(_Z7);return _Za[0]==0?!B(_lv(_Z9[3],_Za[3]))?[0]:[1,_Z8]:[0];case 1:var _Zb=E(_Z7);return _Zb[0]==1?!B(_lv(_Z9[3],_Zb[3]))?[0]:[1,_Z8]:[0];case 2:var _Zc=E(_Z7);return _Zc[0]==2?!B(_lv(_Z9[3],_Zc[3]))?[0]:[1,_Z8]:[0];case 3:var _Zd=E(_Z7);return _Zd[0]==3?!B(_lv(_Z9[3],_Zd[3]))?[0]:[1,_Z8]:[0];case 4:var _Ze=E(_Z7);return _Ze[0]==4?!B(_lv(_Z9[3],_Ze[3]))?[0]:[1,_Z8]:[0];case 5:var _Zf=E(_Z7);return _Zf[0]==5?!B(_lv(_Z9[3],_Zf[3]))?[0]:[1,_Z8]:[0];case 6:var _Zg=E(_Z7);return _Zg[0]==6?!B(_lv(_Z9[3],_Zg[3]))?[0]:[1,_Z8]:[0];case 7:var _Zh=E(_Z7);return _Zh[0]==7?!B(_lv(_Z9[3],_Zh[3]))?[0]:[1,_Z8]:[0];case 8:var _Zi=E(_Z7);return _Zi[0]==8?!B(_lv(_Z9[3],_Zi[3]))?[0]:[1,_Z8]:[0];default:var _Zj=E(_Z7);return _Zj[0]==9?!B(_lv(_Z9[3],_Zj[3]))?[0]:[1,_Z8]:[0];}},_Zk=new T(function(){return B(_3B("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_Zl=function(_Zm,_Zn){return [3,_,_Zm,_Zn];},_Zo=function(_Zp,_Zq,_Zr){while(1){var _Zs=E(_Zr);if(!_Zs[0]){return [0];}else{var _Zt=E(_Zs[1]),_Zu=B(A(_Zp,[_Zq,_Zt[2],_Zt[3]]));if(!_Zu[0]){_Zr=_Zs[2];continue;}else{return E(_Zu);}}}},_Zv=function(_Zw,_Zx){while(1){var _Zy=(function(_Zz,_ZA){var _ZB=E(_ZA);switch(_ZB[0]){case 2:var _ZC=B(_Zo(_Z5,_ZB[2],_Zz));if(!_ZC[0]){return E(_ZB);}else{var _ZD=_Zz;_Zx=_ZC[1];_Zw=_ZD;return null;}break;case 4:var _ZE=_ZB[3],_ZF=B(_Zo(_Z5,_ZB[2],_Zz));if(!_ZF[0]){return E(_ZB);}else{var _ZG=E(_ZF[1]);switch(_ZG[0]){case 3:return E(_ZG[3])[0]==0?B(_Zl(_ZG[2],_ZE)):E(_ZB);case 4:if(!E(_ZG[3])[0]){var _ZD=_Zz;_Zx=[4,_,_ZG[2],_ZE];_Zw=_ZD;return null;}else{return E(_ZB);}break;default:return E(_ZB);}}break;case 6:var _ZH=_ZB[3],_ZI=_ZB[4],_ZJ=B(_Zo(_Z5,_ZB[2],_Zz));if(!_ZJ[0]){return E(_ZB);}else{var _ZK=E(_ZJ[1]);switch(_ZK[0]){case 5:if(!E(_ZK[3])[0]){if(!E(_ZK[4])[0]){var _ZD=_Zz;_Zx=[5,_,_ZK[2],_ZH,_ZI];_Zw=_ZD;return null;}else{return E(_ZB);}}else{return E(_ZB);}break;case 6:if(!E(_ZK[3])[0]){if(!E(_ZK[4])[0]){var _ZD=_Zz;_Zx=[6,_,_ZK[2],_ZH,_ZI];_Zw=_ZD;return null;}else{return E(_ZB);}}else{return E(_ZB);}break;default:return E(_ZB);}}break;case 7:return [7,_,_ZB[2],new T(function(){return B(_Zv(_Zz,_ZB[3]));})];case 8:var _ZL=_ZB[2],_ZM=_ZB[3],_ZN=B(_Zo(_Z5,_ZL,_Zz));if(!_ZN[0]){return [8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];}else{var _ZO=E(_ZN[1]);switch(_ZO[0]){case 7:return E(_ZO[3])[0]==0?[7,_,_ZO[2],new T(function(){return B(_Zv(_Zz,_ZM));})]:[8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];case 8:if(!E(_ZO[3])[0]){var _ZD=_Zz;_Zx=[8,_,_ZO[2],_ZM];_Zw=_ZD;return null;}else{return [8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];}break;default:return [8,_,_ZL,new T(function(){return B(_Zv(_Zz,_ZM));})];}}break;case 9:return [9,_,_ZB[2],new T(function(){return B(_Zv(_Zz,_ZB[3]));}),new T(function(){return B(_Zv(_Zz,_ZB[4]));})];case 10:var _ZP=_ZB[2],_ZQ=_ZB[3],_ZR=_ZB[4],_ZS=B(_Zo(_Z5,_ZP,_Zz));if(!_ZS[0]){return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}else{var _ZT=E(_ZS[1]);switch(_ZT[0]){case 9:return E(_ZT[3])[0]==0?E(_ZT[4])[0]==0?[9,_,_ZT[2],new T(function(){return B(_Zv(_Zz,B(_Zv(_Zz,_ZQ))));}),new T(function(){return B(_Zv(_Zz,B(_Zv(_Zz,_ZR))));})]:[10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})]:[10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];case 10:if(!E(_ZT[3])[0]){if(!E(_ZT[4])[0]){var _ZD=_Zz;_Zx=[10,_,_ZT[2],_ZQ,_ZR];_Zw=_ZD;return null;}else{return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}}else{return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}break;default:return [10,_,_ZP,new T(function(){return B(_Zv(_Zz,_ZQ));}),new T(function(){return B(_Zv(_Zz,_ZR));})];}}break;case 11:return [11,_,_ZB[2],function(_ZU){return new F(function(){return _Zv(_Zz,B(A(_ZB[3],[_ZU])));});}];case 12:var _ZV=_ZB[2],_ZW=_ZB[3],_ZX=B(_Zo(_Z5,_ZV,_Zz));if(!_ZX[0]){return [12,_,_ZV,function(_ZY){return new F(function(){return _Zv(_Zz,B(A(_ZW,[_ZY])));});}];}else{var _ZZ=E(_ZX[1]);switch(_ZZ[0]){case 11:return [11,_,_ZZ[2],function(_100){return new F(function(){return _Zv(_Zz,B(A(_ZW,[_100])));});}];case 12:var _ZD=_Zz;_Zx=[12,_,_ZZ[2],_ZW];_Zw=_ZD;return null;default:return [12,_,_ZV,function(_101){return new F(function(){return _Zv(_Zz,B(A(_ZW,[_101])));});}];}}break;default:return E(_ZB);}})(_Zw,_Zx);if(_Zy!=null){return _Zy;}}},_102=function(_103,_104){var _105=E(_104);if(!_105[0]){var _106=B(_Zo(_Z5,_105[1],_103));if(!_106[0]){return E(_105);}else{var _107=E(_106[1]);return _107[0]==0?E(_Zk):[1,new T(function(){return B(_7X(function(_108){return new F(function(){return _Zv(_103,_108);});},_107[1]));})];}}else{return [1,new T(function(){return B(_7X(function(_109){return new F(function(){return _Zv(_103,_109);});},_105[1]));})];}},_10a=function(_10b,_10c,_10d,_10e,_10f,_10g,_10h,_10i,_10j){var _10k=E(_10j);return [0,new T(function(){return B(_7X(function(_10l){return new F(function(){return _102(_10i,_10l);});},_10k[1]));}),new T(function(){return B(_102(_10i,_10k[2]));})];},_10m=function(_10n,_10o,_10p,_10q,_10r,_10s,_10t,_10u,_10v){var _10w=E(_10v);return [0,new T(function(){return B(_7X(function(_10x){return new F(function(){return _10a(_10n,_10o,_10p,_10q,_10r,_10s,_10t,_10u,_10x);});},_10w[1]));}),new T(function(){return B(_10a(_10n,_10o,_10p,_10q,_10r,_10s,_10t,_10u,_10w[2]));})];},_10y=function(_10z){return E(E(_10z)[1]);},_10A=function(_10B,_10C){var _10D=E(_10C);return new F(function(){return A(_10y,[_10D[1],E(_10B)[2],_10D[2]]);});},_10E=function(_10F,_10G,_10H){var _10I=E(_10H);if(!_10I[0]){return [0];}else{var _10J=_10I[1],_10K=_10I[2];return !B(A(_10F,[_10G,_10J]))?[1,_10J,new T(function(){return B(_10E(_10F,_10G,_10K));})]:E(_10K);}},_10L=function(_10M,_10N,_10O){while(1){var _10P=E(_10O);if(!_10P[0]){return false;}else{if(!B(A(_10M,[_10N,_10P[1]]))){_10O=_10P[2];continue;}else{return true;}}}},_10Q=function(_10R,_10S){var _10T=function(_10U,_10V){while(1){var _10W=(function(_10X,_10Y){var _10Z=E(_10X);if(!_10Z[0]){return [0];}else{var _110=_10Z[1],_111=_10Z[2];if(!B(_10L(_10R,_110,_10Y))){return [1,_110,new T(function(){return B(_10T(_111,[1,_110,_10Y]));})];}else{_10U=_111;var _112=_10Y;_10V=_112;return null;}}})(_10U,_10V);if(_10W!=null){return _10W;}}};return new F(function(){return _10T(_10S,_9);});},_113=function(_114,_115,_116){return new F(function(){return _e(_115,new T(function(){return B((function(_117,_118){while(1){var _119=E(_118);if(!_119[0]){return E(_117);}else{var _11a=B(_10E(_114,_119[1],_117));_118=_119[2];_117=_11a;continue;}}})(B(_10Q(_114,_116)),_115));},1));});},_11b=function(_11c,_11d){while(1){var _11e=(function(_11f,_11g){var _11h=E(_11g);switch(_11h[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_11f,_11h[2]],_9];case 3:var _11i=_11f;_11d=_11h[3];_11c=_11i;return null;case 4:return new F(function(){return _113(_10A,[1,[0,_11f,_11h[2]],_9],new T(function(){return B(_11b(_11f,_11h[3]));},1));});break;case 5:return new F(function(){return _113(_10A,B(_11b(_11f,_11h[3])),new T(function(){return B(_11b(_11f,_11h[4]));},1));});break;default:return new F(function(){return _113(_10A,B(_113(_10A,[1,[0,_11f,_11h[2]],_9],new T(function(){return B(_11b(_11f,_11h[3]));},1))),new T(function(){return B(_11b(_11f,_11h[4]));},1));});}})(_11c,_11d);if(_11e!=null){return _11e;}}},_11j=function(_11k,_11l,_11m,_11n){while(1){var _11o=(function(_11p,_11q,_11r,_11s){var _11t=E(_11s);switch(_11t[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_11p,_11t[2]],_9];case 3:return new F(function(){return _11b(_11p,_11t[3]);});break;case 4:return new F(function(){return _113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11b(_11p,_11t[3]));},1));});break;case 5:return new F(function(){return _113(_10A,B(_11b(_11p,_11t[3])),new T(function(){return B(_11b(_11p,_11t[4]));},1));});break;case 6:return new F(function(){return _113(_10A,B(_113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11b(_11p,_11t[3]));},1))),new T(function(){return B(_11b(_11p,_11t[4]));},1));});break;case 7:var _11u=_11p,_11v=_11q,_11w=_11r;_11n=_11t[3];_11k=_11u;_11l=_11v;_11m=_11w;return null;case 8:return new F(function(){return _113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11j(_11p,_11q,_11r,_11t[3]));},1));});break;case 9:return new F(function(){return _113(_10A,B(_11j(_11p,_11q,_11r,_11t[3])),new T(function(){return B(_11j(_11p,_11q,_11r,_11t[4]));},1));});break;case 10:return new F(function(){return _113(_10A,B(_113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11j(_11p,_11q,_11r,_11t[3]));},1))),new T(function(){return B(_11j(_11p,_11q,_11r,_11t[4]));},1));});break;case 11:var _11u=_11p,_11v=_11q,_11w=_11r;_11n=B(A(_11t[3],[_ae]));_11k=_11u;_11l=_11v;_11m=_11w;return null;default:return new F(function(){return _113(_10A,[1,[0,_11p,_11t[2]],_9],new T(function(){return B(_11j(_11p,_11q,_11r,B(A(_11t[3],[_ae]))));},1));});}})(_11k,_11l,_11m,_11n);if(_11o!=null){return _11o;}}},_11x=function(_11y,_11z,_11A,_11B,_11C){var _11D=function(_11E){return new F(function(){return _11j(_11y,_11z,_11A,_11E);});};return new F(function(){return _e(B(_7r(B(_7X(function(_11F){var _11G=E(_11F);if(!_11G[0]){return [1,[0,_11y,_11G[1]],_9];}else{return new F(function(){return _7r(B(_7X(_11D,_11G[1])));});}},_11B)))),new T(function(){var _11H=E(_11C);if(!_11H[0]){var _11I=[1,[0,_11y,_11H[1]],_9];}else{var _11I=B(_7r(B(_7X(_11D,_11H[1]))));}return _11I;},1));});},_11J=function(_11K,_11L,_11M,_11N,_11O,_11P,_11Q,_11R,_11S){var _11T=E(_11S);return new F(function(){return _e(B(_7r(B(_7X(function(_11U){var _11V=E(_11U);return new F(function(){return _11x(_11K,_11O,_11P,_11V[1],_11V[2]);});},_11T[1])))),new T(function(){var _11W=E(_11T[2]);return B(_11x(_11K,_11O,_11P,_11W[1],_11W[2]));},1));});},_11X=function(_11Y,_11Z,_120,_121,_122,_123,_124,_125,_126,_127,_128){return [0,_11Y,_11Z,_120,_121,function(_10x){return new F(function(){return _11J(_11Y,_122,_123,_124,_125,_126,_127,_128,_10x);});},function(_129,_10x){return new F(function(){return _10m(_122,_123,_124,_125,_126,_127,_128,_129,_10x);});}];},_12a=function(_12b){return E(E(_12b)[2]);},_12c=function(_12d){return E(E(_12d)[1]);},_12e=[0,_12c,_12a],_12f=[0,125],_12g=new T(function(){return B(unCStr("given = "));}),_12h=new T(function(){return B(unCStr(", "));}),_12i=new T(function(){return B(unCStr("needed = "));}),_12j=new T(function(){return B(unCStr("AbsRule {"));}),_12k=[0,0],_12l=function(_12m){return E(E(_12m)[3]);},_12n=function(_12o){return E(E(_12o)[1]);},_12p=function(_12q,_12r,_12s,_12t){var _12u=function(_12v){return new F(function(){return _e(_12j,new T(function(){return B(_e(_12i,new T(function(){return B(A(new T(function(){return B(A(_12l,[_12q,_12s]));}),[new T(function(){return B(_e(_12h,new T(function(){return B(_e(_12g,new T(function(){return B(A(new T(function(){return B(A(_12n,[_12q,_12k,_12t]));}),[[1,_12f,_12v]]));},1)));},1)));})]));},1)));},1));});};return _12r<11?E(_12u):function(_12w){return [1,_E,new T(function(){return B(_12u([1,_D,_12w]));})];};},_12x=function(_12y,_12z){var _12A=E(_12z);return new F(function(){return A(_12p,[_12y,0,_12A[1],_12A[2],_9]);});},_12B=function(_12C,_12D,_12E){return new F(function(){return _2T(function(_12F){var _12G=E(_12F);return new F(function(){return _12p(_12C,0,_12G[1],_12G[2]);});},_12D,_12E);});},_12H=function(_12I,_12J,_12K){var _12L=E(_12K);return new F(function(){return _12p(_12I,E(_12J)[1],_12L[1],_12L[2]);});},_12M=function(_12N){return [0,function(_Yn,_Yo){return new F(function(){return _12H(_12N,_Yn,_Yo);});},function(_Yo){return new F(function(){return _12x(_12N,_Yo);});},function(_Yn,_Yo){return new F(function(){return _12B(_12N,_Yn,_Yo);});}];},_12O=new T(function(){return B(unCStr("Sequent "));}),_12P=[0,11],_12Q=[0,32],_12R=function(_12S,_12T,_12U,_12V){var _12W=new T(function(){return B(A(_12n,[_12S,_12P,_12V]));}),_12X=new T(function(){return B(A(_12l,[_12S,_12U]));});return _12T<11?function(_12Y){return new F(function(){return _e(_12O,new T(function(){return B(A(_12X,[[1,_12Q,new T(function(){return B(A(_12W,[_12Y]));})]]));},1));});}:function(_12Z){return [1,_E,new T(function(){return B(_e(_12O,new T(function(){return B(A(_12X,[[1,_12Q,new T(function(){return B(A(_12W,[[1,_D,_12Z]]));})]]));},1)));})];};},_130=function(_131,_132){var _133=E(_132);return new F(function(){return A(_12R,[_131,0,_133[1],_133[2],_9]);});},_134=function(_135,_136,_137){return new F(function(){return _2T(function(_138){var _139=E(_138);return new F(function(){return _12R(_135,0,_139[1],_139[2]);});},_136,_137);});},_13a=function(_13b,_13c,_13d){var _13e=E(_13d);return new F(function(){return _12R(_13b,E(_13c)[1],_13e[1],_13e[2]);});},_13f=function(_13g){return [0,function(_Yn,_Yo){return new F(function(){return _13a(_13g,_Yn,_Yo);});},function(_Yo){return new F(function(){return _130(_13g,_Yo);});},function(_Yn,_Yo){return new F(function(){return _134(_13g,_Yn,_Yo);});}];},_13h=function(_13i,_13j){return new F(function(){return _e(B(_a1(_13i)),_13j);});},_13k=function(_13l,_13m){return new F(function(){return _2T(_13h,_13l,_13m);});},_13n=function(_13o,_13p,_13q){return new F(function(){return _e(B(_a1(_13p)),_13q);});},_13r=[0,_13n,_a1,_13k],_13s=function(_13t,_13u,_13v,_13w,_13x,_13y,_13z,_13A,_13B,_13C,_13D,_13E){var _13F=E(_13E);return new F(function(){return _11x(_13t,_13A,_13B,_13F[1],_13F[2]);});},_13G=function(_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_13R){return [0,_13H,_13I,_13J,_13K,function(_10x){return new F(function(){return _13s(_13H,_13I,_13J,_13K,_13L,_13M,_13N,_13O,_13P,_13Q,_13R,_10x);});},function(_129,_10x){return new F(function(){return _10a(_13L,_13M,_13N,_13O,_13P,_13Q,_13R,_129,_10x);});}];},_13S=function(_13T,_13U){return [0];},_13V=function(_13W,_13X,_13Y,_13Z,_140,_141,_142,_143,_144,_145,_146,_147,_148,_149){return [0,_13W,_13X,_13S,_1];},_14a=function(_14b,_14c,_14d,_14e,_14f,_14g,_14h,_14i,_14j,_14k,_14l,_14m){var _14n=E(_14m);if(!_14n[0]){return [1,[0,_14b,_14n[1]],_9];}else{return new F(function(){return _7r(B(_7X(function(_14o){return new F(function(){return _11j(_14b,_14i,_14j,_14o);});},_14n[1])));});}},_14p=function(_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A){return [0,_14q,_14r,_14s,_14t,function(_10x){return new F(function(){return _14a(_14q,_14r,_14s,_14t,_14u,_14v,_14w,_14x,_14y,_14z,_14A,_10x);});},_102];},_14B=new T(function(){return B(_CX("w_syXX{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv ayC0} [tv] quant{tv ayBY} [tv]"));}),_14C=new T(function(){return B(_CX("w_syXW{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv ayBY} [tv]"));}),_14D=new T(function(){return B(_CX("w_syXV{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv ayBX} [tv]"));}),_14E=new T(function(){return B(_CX("w_syXU{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv ayC0} [tv]"));}),_14F=new T(function(){return B(_CX("w_syXT{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv ayBW} [tv]"));}),_14G=new T(function(){return B(_CX("w_syXS{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv ayBZ} [tv]"));}),_14H=new T(function(){return B(_CX("w_syXY{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv ayC0} [tv]"));}),_14I=new T(function(){return B(_CX("w_syXR{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayBY} [tv]"));}),_14J=new T(function(){return B(_CX("w_syXQ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv ayBX} [tv]"));}),_14K=new T(function(){return B(_CX("w_syXP{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv ayC0} [tv]"));}),_14L=new T(function(){return B(_CX("w_syXO{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv ayBW} [tv]"));}),_14M=new T(function(){return B(_CX("w_syXN{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayBZ} [tv]"));}),_14N=function(_14O,_14P){return function(_14Q,_14R){var _14S=E(_14Q);return _14S[0]==0?[1,[0,new T(function(){return B(_14T(_14O,_14P,_14M,_14L,_14K,_14J,_14I,_14G,_14F,_14E,_14D,_14C,_14B,_14H));}),_14S[1],_14R]]:[0];};},_14U=function(_14V){return [0,E(_14V)];},_14T=function(_14W,_14X,_14Y,_14Z,_150,_151,_152,_153,_154,_155,_156,_157,_158,_159){return [0,_14W,_14X,new T(function(){return B(_14N(_14W,_14X));}),_14U];},_15a=[1,_9],_15b=function(_15c,_15d){while(1){var _15e=E(_15c);if(!_15e[0]){return E(_15d);}else{_15c=_15e[2];var _15f=_15d+1|0;_15d=_15f;continue;}}},_15g=[0,95],_15h=[1,_15g,_9],_15i=[1,_15h,_9],_15j=function(_15k,_15l,_15m){return !B(_lv(B(A(_15k,[_15l,_15i])),B(A(_15k,[_15m,_15i]))))?true:false;},_15n=function(_15o){return [0,function(_15p,_15q){return new F(function(){return _lv(B(A(_15o,[_15p,_15i])),B(A(_15o,[_15q,_15i])));});},function(_bi,_bj){return new F(function(){return _15j(_15o,_bi,_bj);});}];},_15r=function(_15s,_15t){return new F(function(){return _Zv(_15s,_15t);});},_15u=function(_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F){return [0,_15v,_15w,_15x,_15y,function(_15G){return new F(function(){return _11j(_15v,_15C,_15D,_15G);});},_15r];},_15H=new T(function(){return B(_CX("w_so5r{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv al2r} [tv] quant{tv al2p} [tv]"));}),_15I=new T(function(){return B(_CX("w_so5q{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv al2p} [tv]"));}),_15J=new T(function(){return B(_CX("w_so5p{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv al2o} [tv]"));}),_15K=new T(function(){return B(_CX("w_so5o{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv al2r} [tv]"));}),_15L=new T(function(){return B(_CX("w_so5n{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv al2n} [tv]"));}),_15M=new T(function(){return B(_CX("w_so5m{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv al2q} [tv]"));}),_15N=new T(function(){return B(_CX("w_so5s{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv al2r} [tv]"));}),_15O=new T(function(){return B(_CX("w_so5l{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv al2p} [tv]"));}),_15P=new T(function(){return B(_CX("w_so5k{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv al2o} [tv]"));}),_15Q=new T(function(){return B(_CX("w_so5j{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv al2r} [tv]"));}),_15R=new T(function(){return B(_CX("w_so5i{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv al2n} [tv]"));}),_15S=new T(function(){return B(_CX("w_so5h{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv al2q} [tv]"));}),_15T=function(_15U,_15V,_15W,_15X){var _15Y=E(_15W);switch(_15Y[0]){case 2:return [1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_15Y[2],_15X]];case 4:var _160=_15Y[2];if(!E(_15Y[3])[0]){var _161=E(_15X);switch(_161[0]){case 3:return E(_161[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_160,_161]]:[0];case 4:return E(_161[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_160,_161]]:[0];default:return [0];}}else{return [0];}break;case 6:var _162=_15Y[2];if(!E(_15Y[3])[0]){if(!E(_15Y[4])[0]){var _163=E(_15X);switch(_163[0]){case 5:return E(_163[3])[0]==0?E(_163[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_162,_163]]:[0]:[0];case 6:return E(_163[3])[0]==0?E(_163[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_162,_163]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _164=_15Y[2];if(!E(_15Y[3])[0]){var _165=E(_15X);switch(_165[0]){case 7:return E(_165[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_164,_165]]:[0];case 8:return E(_165[3])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_164,_165]]:[0];default:return [0];}}else{return [0];}break;case 10:var _166=_15Y[2];if(!E(_15Y[3])[0]){if(!E(_15Y[4])[0]){var _167=E(_15X);switch(_167[0]){case 9:return E(_167[3])[0]==0?E(_167[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_166,_167]]:[0]:[0];case 10:return E(_167[3])[0]==0?E(_167[4])[0]==0?[1,[0,new T(function(){return B(_15Z(_15U,_15V,_15S,_15R,_15Q,_15P,_15O,_15M,_15L,_15K,_15J,_15I,_15H,_15N));}),_166,_167]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_168=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_169=function(_16a){var _16b=E(_16a);switch(_16b[0]){case 3:return [2,_,_16b];case 4:return [4,_,_16b,_V];case 5:return [6,_,_16b,_V,_V];case 6:return [8,_,_16b,_S];case 7:return [10,_,_16b,_S,_S];default:return E(_168);}},_15Z=function(_16c,_16d,_16e,_16f,_16g,_16h,_16i,_16j,_16k,_16l,_16m,_16n,_16o,_16p){return [0,_16c,_16d,function(_16q,_16r){return new F(function(){return _15T(_16c,_16d,_16q,_16r);});},_169];},_16s=function(_16t,_16u,_16v){return new F(function(){return _2T(function(_16w,_16x){return new F(function(){return _e(B(A(_16t,[_16w,_15i])),_16x);});},_16u,_16v);});},_16y=function(_16z){return [0,function(_16A,_16B,_16C){return new F(function(){return _e(B(A(_16z,[_16B,_15i])),_16C);});},function(_16D){return new F(function(){return A(_16z,[_16D,_15i]);});},function(_bi,_bj){return new F(function(){return _16s(_16z,_bi,_bj);});}];},_16E=[1,_9],_16F=function(_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_16Q,_16R){var _16S=E(_16Q);if(_16S[0]==2){return E(_16E);}else{var _16T=E(_16R);if(_16T[0]==2){return E(_16E);}else{var _16U=function(_16V){var _16W=function(_16X){var _16Y=function(_16Z){var _170=function(_171){var _172=function(_173){var _174=function(_175){var _176=function(_177){var _178=function(_179){var _17a=function(_17b){var _17c=function(_17d){var _17e=function(_17f){var _17g=function(_17h){var _17i=E(_16S);switch(_17i[0]){case 1:var _17j=E(_16T);return _17j[0]==1?!B(A(_16H,[_17i[2],_17j[2]]))?[0]:E(_16E):[0];case 3:var _17k=E(_16T);return _17k[0]==3?!B(A(_16G,[_17i[2],_17k[2]]))?[0]:E(_16E):[0];case 4:var _17l=_17i[2],_17m=E(_16T);switch(_17m[0]){case 3:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[4,_,_17l,_V],[3,_,_17m[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[4,_,_17l,_V],[4,_,_17m[2],_V]]));}),_9]];default:return [0];}break;case 5:var _17o=E(_16T);return _17o[0]==5?!B(A(_16G,[_17i[2],_17o[2]]))?[0]:E(_16E):[0];case 6:var _17p=_17i[2],_17q=E(_16T);switch(_17q[0]){case 5:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[6,_,_17p,_V,_V],[5,_,_17q[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[6,_,_17p,_V,_V],[6,_,_17q[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _17r=E(_16T);return _17r[0]==7?!B(A(_16I,[_17i[2],_17r[2]]))?[0]:[1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17i[3],_17r[3]]));}),_9]]:[0];case 8:var _17s=_17i[2],_17t=_17i[3],_17u=E(_16T);switch(_17u[0]){case 7:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[8,_,_17s,_S],[7,_,_17u[2],_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17t,_17u[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[8,_,_17s,_S],[8,_,_17u[2],_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17t,_17u[3]]));}),_9]]];default:return [0];}break;case 9:var _17v=E(_16T);return _17v[0]==9?!B(A(_16I,[_17i[2],_17v[2]]))?[0]:[1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17i[3],_17v[3]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17i[4],_17v[4]]));}),_9]]]:[0];case 10:var _17w=_17i[2],_17x=_17i[3],_17y=_17i[4],_17z=function(_17A){var _17B=E(_16T);switch(_17B[0]){case 9:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[10,_,_17w,_S,_S],[9,_,_17B[2],_S,_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17x,_17B[3]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17y,_17B[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,[10,_,_17w,_S,_S],[10,_,_17B[2],_S,_S]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17x,_17B[3]]));}),[1,new T(function(){return B(A(_17n,[_16G,_16H,_16I,_16J,_16K,_16L,_16M,_16N,_16O,_16P,_17y,_17B[4]]));}),_9]]]];default:return [0];}};return E(_17x)[0]==0?E(_17y)[0]==0?E(_16E):B(_17z(_)):B(_17z(_));default:return [0];}},_17C=E(_16T);return _17C[0]==10?E(_17C[3])[0]==0?E(_17C[4])[0]==0?E(_16E):B(_17g(_)):B(_17g(_)):B(_17g(_));},_17D=E(_16S);return _17D[0]==8?E(_17D[3])[0]==0?E(_16E):B(_17e(_)):B(_17e(_));},_17E=E(_16T);switch(_17E[0]){case 6:return E(_17E[3])[0]==0?E(_17E[4])[0]==0?E(_16E):B(_17c(_)):B(_17c(_));case 8:return E(_17E[3])[0]==0?E(_16E):B(_17c(_));default:return new F(function(){return _17c(_);});}},_17F=E(_16S);return _17F[0]==6?E(_17F[3])[0]==0?E(_17F[4])[0]==0?E(_16E):B(_17a(_)):B(_17a(_)):B(_17a(_));},_17G=E(_16T);return _17G[0]==4?E(_17G[3])[0]==0?E(_16E):B(_178(_)):B(_178(_));},_17H=E(_16S);switch(_17H[0]){case 4:return E(_17H[3])[0]==0?E(_16E):B(_176(_));case 9:return E(_17H[3])[0]==0?E(_17H[4])[0]==0?E(_16E):B(_176(_)):B(_176(_));default:return new F(function(){return _176(_);});}},_17I=E(_16T);return _17I[0]==9?E(_17I[3])[0]==0?E(_17I[4])[0]==0?E(_16E):B(_174(_)):B(_174(_)):B(_174(_));},_17J=E(_16S);return _17J[0]==7?E(_17J[3])[0]==0?E(_16E):B(_172(_)):B(_172(_));},_17K=E(_16T);switch(_17K[0]){case 5:return E(_17K[3])[0]==0?E(_17K[4])[0]==0?E(_16E):B(_170(_)):B(_170(_));case 7:return E(_17K[3])[0]==0?E(_16E):B(_170(_));default:return new F(function(){return _170(_);});}},_17L=E(_16S);return _17L[0]==5?E(_17L[3])[0]==0?E(_17L[4])[0]==0?E(_16E):B(_16Y(_)):B(_16Y(_)):B(_16Y(_));},_17M=E(_16T);return _17M[0]==3?E(_17M[3])[0]==0?E(_16E):B(_16W(_)):B(_16W(_));},_17N=E(_16S);return _17N[0]==3?E(_17N[3])[0]==0?E(_16E):B(_16U(_)):B(_16U(_));}}},_17O=function(_17P,_17Q,_17R){return [0,_17P,_17Q,_17R];},_17S=new T(function(){return B(_CX("w_so5A{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv al1M} [tv]"));}),_17T=new T(function(){return B(_CX("w_so5w{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv al1N} [tv]"));}),_17U=function(_17V){return [0,function(_17W,_17X){return B(A(_17V,[_17W,_17X,_1]))[0]==0?false:true;},function(_17Y,_17Z){return B(A(_17V,[_17Y,_17Z,_1]))[0]==0?true:false;}];},_180=new T(function(){return B(_17U(_Z5));}),_17n=function(_181,_182,_183,_184,_185,_186,_187,_188,_189,_18a){var _18b=function(_18c,_18d){return new F(function(){return _af(_185,_187,_188,_186,_184,_189,_18a,_18c);});};return function(_mc,_18e){return new F(function(){return _17O(new T(function(){return B(_15Z(function(_18f,_18g){return new F(function(){return _16F(_181,_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18f,_18g);});},new T(function(){return B(_15u(_180,_13r,new T(function(){return B(_15n(_18b));}),new T(function(){return B(_16y(_18b));}),_185,_187,_188,_184,_186,_189,_18a));}),_17T,_181,_182,_183,_17S,_184,_185,_186,_187,_188,_189,_18a));}),_mc,_18e);});};},_18h=function(_18i,_18j,_18k){var _18l=E(_18j);if(!_18l[0]){return [0];}else{var _18m=E(_18k);return _18m[0]==0?[0]:[1,new T(function(){return B(A(_18i,[_18l[1],_18m[1]]));}),new T(function(){return B(_18h(_18i,_18l[2],_18m[2]));})];}},_18n=function(_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x,_18y,_18z){var _18A=E(_18y);if(!_18A[0]){return E(_15a);}else{var _18B=_18A[1],_18C=E(_18z);if(!_18C[0]){return E(_15a);}else{var _18D=_18C[1];return B(_15b(_18B,0))!=B(_15b(_18D,0))?[0]:[1,new T(function(){return B(_18h(new T(function(){return B(_17n(_18o,_18p,_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x));}),_18B,_18D));})];}}},_18E=new T(function(){return B(_CX("w_syYI{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayBG} [tv]"));}),_18F=new T(function(){return B(_CX("w_syYM{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayBF} [tv]"));}),_18G=new T(function(){return B(_17U(_Z5));}),_18H=function(_18I,_18J,_18K,_18L,_18M,_18N,_18O,_18P,_18Q,_18R){var _18S=new T(function(){return B(_14T(function(_18T,_18U){return new F(function(){return _18n(_18I,_18J,_18K,_18L,_18M,_18N,_18O,_18P,_18Q,_18R,_18T,_18U);});},new T(function(){return B(_14p(_18G,_13r,new T(function(){return B(_YJ(_18M,_18O,_18P,_18L,_18N,_18Q,_18R));}),new T(function(){return B(_b9(_18M,_18O,_18P,_18L,_18N,_18Q,_18R));}),_18M,_18O,_18P,_18L,_18N,_18Q,_18R));}),_18E,_18I,_18J,_18K,_18F,_18L,_18M,_18N,_18O,_18P,_18Q,_18R));});return function(_18V,_18W){var _18X=E(_18V),_18Y=_18X[1],_18Z=E(_18W),_190=_18Z[1];return B(_15b(_18Y,0))!=B(_15b(_190,0))?[0]:[1,[1,[0,_18S,_18X[2],_18Z[2]],new T(function(){return B(_18h(function(_129,_10x){return [0,_18S,_129,_10x];},_18Y,_190));})]];};},_191=new T(function(){return B(_CX("w_sz1k{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayBd} [tv]"));}),_192=new T(function(){return B(_CX("w_sz1o{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayBc} [tv]"));}),_193=function(_194,_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d){var _19e=new T(function(){return B(_13V(new T(function(){return B(_18H(_194,_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d));}),new T(function(){return B(_13G(_18G,_13r,new T(function(){return B(_Z3(new T(function(){return B(_YJ(_198,_19a,_19b,_197,_199,_19c,_19d));})));}),new T(function(){return B(_13f(new T(function(){return B(_b9(_198,_19a,_19b,_197,_199,_19c,_19d));})));}),_198,_19a,_19b,_197,_199,_19c,_19d));}),_191,_194,_195,_196,_192,_197,_198,_199,_19a,_19b,_19c,_19d));});return function(_19f,_19g){var _19h=E(_19f),_19i=_19h[1],_19j=E(_19g),_19k=_19j[1];return B(_15b(_19i,0))!=B(_15b(_19k,0))?[0]:[1,[1,[0,_19e,_19h[2],_19j[2]],new T(function(){return B(_18h(function(_129,_10x){return [0,_19e,_129,_10x];},_19i,_19k));})]];};},_19l=function(_19m,_19n){while(1){var _19o=E(_19n);if(!_19o[0]){return false;}else{var _19p=E(_19o[1]);if(!B(A(_10y,[_19p[1],_19m,_19p[2]]))){_19n=_19o[2];continue;}else{return true;}}}},_19q=[0,_9],_19r=function(_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_19C){var _19D=E(_19v);return !B(A(_19D[1],[new T(function(){return B(A(_19A,[_19B]));}),_19C]))?!B(_19l(_19B,B(A(_19x,[_19C]))))?[0,[1,[0,[0,_19s,[0,_19t,_19u,_19D,_19w,_19x,_19y],_19z,_19A],_19B,_19C],_9]]:[1,[1,_,[0,_19s,[0,_19t,_19u,_19D,_19w,_19x,_19y],_19z,_19A],[3,_19u,_19w,_19B,_19C]]]:E(_19q);},_19E=function(_19F){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(54,15)-(56,42)|case");});},_19G=new T(function(){return B(_19E(_));}),_19H=new T(function(){return B(unCStr(": empty list"));}),_19I=new T(function(){return B(unCStr("Prelude."));}),_19J=function(_19K){return new F(function(){return err(B(_e(_19I,new T(function(){return B(_e(_19K,_19H));},1))));});},_19L=new T(function(){return B(unCStr("head"));}),_19M=new T(function(){return B(_19J(_19L));}),_19N=function(_19O){return E(E(_19O)[2]);},_19P=function(_19Q,_19R){while(1){var _19S=E(_19Q);if(!_19S){return E(_19R);}else{var _19T=E(_19R);if(!_19T[0]){return [0];}else{_19Q=_19S-1|0;_19R=_19T[2];continue;}}}},_19U=function(_19V,_19W){var _19X=E(_19V)[1];return _19X>=0?B(_19P(_19X,_19W)):E(_19W);},_19Y=function(_19Z){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:96:31-64|function conc");});},_1a0=new T(function(){return B(_19Y(_));}),_1a1=function(_1a2){var _1a3=E(_1a2);switch(_1a3[0]){case 3:return [2,_,_1a3];case 4:return [4,_,_1a3,_V];case 5:return [6,_,_1a3,_V,_V];case 6:return [8,_,_1a3,_S];case 7:return [10,_,_1a3,_S,_S];default:return E(_168);}},_1a4=function(_1a5){var _1a6=E(_1a5);if(!_1a6[0]){return [0];}else{var _1a7=E(_1a6[1]);if(!_1a7[0]){return [0];}else{return new F(function(){return _e(_1a7[1],new T(function(){return B(_1a4(_1a6[2]));},1));});}}},_1a8=function(_1a9){var _1aa=E(_1a9);return [0,[1,[1,new T(function(){return B(_1a4(_1aa[1]));})],_9],_1aa[2]];},_1ab=function(_1ac,_1ad,_1ae){return !B(_86(_1ac,_1ad,_1ae))?E(_1ae):[1,_1ad,new T(function(){return B(_7u(function(_1af){return !B(A(_84,[_1ac,_1af,_1ad]))?true:false;},_1ae));})];},_1ag=function(_1ah,_1ai,_1aj,_1ak,_1al,_1am,_1an){return function(_1ao,_1ap){var _1aq=E(_1ao);if(!_1aq[0]){return new F(function(){return _1a8(_1ap);});}else{var _1ar=E(_1ap);return [0,[1,[1,new T(function(){return B(_1ab(new T(function(){return B(_15n(function(_1as,_1at){return new F(function(){return _af(_1an,_1am,_1al,_1aj,_1ak,_1ah,_1ai,_1as);});}));}),_1aq[1],B(_1a4(_1ar[1]))));})],_9],_1ar[2]];}};},_1au=new T(function(){return B(_17U(_Z5));}),_1av=function(_1aw){return E(E(_1aw)[1]);},_1ax=function(_1ay,_1az){var _1aA=E(_1ay);if(!_1aA){return [0];}else{var _1aB=E(_1az);return _1aB[0]==0?[0]:[1,_1aB[1],new T(function(){return B(_1ax(_1aA-1|0,_1aB[2]));})];}},_1aC=function(_1aD,_1aE){return _1aD<0?[0]:B(_1ax(_1aD,_1aE));},_1aF=function(_1aG,_1aH){var _1aI=E(_1aG)[1];return _1aI>0?B(_1aC(_1aI,_1aH)):[0];},_1aJ=function(_1aK,_1aL){return [1,_,_1aK,_1aL];},_1aM=function(_1aN){return E(E(_1aN)[2]);},_1aO=function(_1aP){return E(E(_1aP)[4]);},_1aQ=function(_1aR,_1aS,_1aT){var _1aU=E(_1aR),_1aV=E(_1aU[2]);return new F(function(){return _19r(_1aU[1],_1aV[1],_1aV[2],_1aV[3],_1aV[4],_1aV[5],_1aV[6],_1aU[3],_1aU[4],_1aS,_1aT);});},_1aW=function(_1aX,_1aY,_1aZ,_1b0,_1b1,_1b2){var _1b3=B(A(_1aZ,[_1b1,_1b2]));if(!_1b3[0]){var _1b4=B(A(_1aZ,[_1b2,_1b1]));if(!_1b4[0]){var _1b5=B(A(_1aX,[_1b1,_1b2]));if(!_1b5[0]){return [1,[0,new T(function(){return B(_1aO(_1aY));}),_1b1,_1b2]];}else{var _1b6=B(_1b7([0,_1aX,_1aY,_1aZ,_1b0],_1b5[1]));return _1b6[0]==0?E(_1b6):[1,[2,new T(function(){return B(_1aO(_1aY));}),_1b6[1],_1b1,_1b2]];}}else{var _1b8=E(_1b4[1]);return new F(function(){return _1aQ(_1b8[1],_1b8[2],_1b8[3]);});}}else{var _1b9=E(_1b3[1]);return new F(function(){return _1aQ(_1b9[1],_1b9[2],_1b9[3]);});}},_1ba=function(_1bb){return E(E(_1bb)[6]);},_1b7=function(_1bc,_1bd){var _1be=E(_1bd);if(!_1be[0]){return E(_19q);}else{var _1bf=E(_1be[1]),_1bg=E(_1bf[1]),_1bh=B(_1aW(_1bg[1],_1bg[2],_1bg[3],_1bg[4],_1bf[2],_1bf[3]));if(!_1bh[0]){var _1bi=_1bh[1],_1bj=B(_1b7(_1bc,B(_7X(function(_1bk){var _1bl=E(_1bk),_1bm=_1bl[1];return [0,_1bm,new T(function(){return B(A(_1ba,[B(_1aM(_1bm)),_1bi,_1bl[2]]));}),new T(function(){return B(A(_1ba,[B(_1aM(_1bm)),_1bi,_1bl[3]]));})];},_1be[2]))));if(!_1bj[0]){var _1bn=_1bj[1];return [0,new T(function(){var _1bo=function(_1bp){var _1bq=E(_1bp);return _1bq[0]==0?E(_1bn):[1,new T(function(){var _1br=E(_1bq[1]),_1bs=_1br[1];return [0,_1bs,_1br[2],new T(function(){return B(A(_1ba,[B(_1aM(_1bs)),_1bn,_1br[3]]));})];}),new T(function(){return B(_1bo(_1bq[2]));})];};return B(_1bo(_1bi));})];}else{return [1,new T(function(){return B(_1aJ(_1bc,_1bj[1]));})];}}else{return [1,[1,_,_1bg,_1bh[1]]];}}},_1bt=function(_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA,_1bB,_1bC,_1bD,_1bE,_1bF){var _1bG=new T(function(){return B(_19N(_1bF));}),_1bH=function(_1bI,_1bJ){return new F(function(){return _af(_1bA,_1bz,_1by,_1bw,_1bx,_1bu,_1bv,_1bI);});},_1bK=new T(function(){return B(_15u(_1au,_13r,new T(function(){return B(_15n(_1bH));}),new T(function(){return B(_16y(_1bH));}),_1bA,_1bz,_1by,_1bx,_1bw,_1bu,_1bv));}),_1bL=function(_1bM,_1bN){return new F(function(){return _16F(_1bE,_1bC,_1bD,_1bx,_1bA,_1bw,_1bz,_1by,_1bu,_1bv,_1bM,_1bN);});};return function(_1bO,_1bP,_1bQ){var _1bR=new T(function(){return B(A(_1bB,[_1bQ]));});return [0,new T(function(){return B(_18h(function(_1bS,_1bT){var _1bU=B(A(new T(function(){return B(_1ag(_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA));}),[new T(function(){var _1bV=E(E(_1bT)[1]);if(!_1bV[0]){var _1bW=[0];}else{var _1bX=E(_1bV[1]),_1bW=_1bX[0]==0?[0]:[1,new T(function(){var _1bY=E(_1bX[1]);return _1bY[0]==0?E(_19M):B(_Zv(new T(function(){var _1bZ=E(B(A(_1bG,[_1bO]))[2]);if(!_1bZ[0]){var _1c0=E(_1a0);}else{var _1c1=E(_1bZ[1]);if(!_1c1[0]){var _1c2=E(_1a0);}else{var _1c3=_1c1[1];if(!E(_1c1[2])[0]){var _1c4=B(_15T(_1bL,_1bK,_1c3,_1bR));if(!_1c4[0]){var _1c5=B(_15T(_1bL,_1bK,_1bR,_1c3));if(!_1c5[0]){var _1c6=B(_1bL(_1c3,_1bR));if(!_1c6[0]){var _1c7=[0];}else{var _1c8=B(_1b7([0,_1bL,_1bK,function(_1c9,_1ca){return new F(function(){return _15T(_1bL,_1bK,_1c9,_1ca);});},_1a1],_1c6[1])),_1c7=_1c8[0]==0?E(_1c8[1]):[0];}var _1cb=_1c7;}else{var _1cc=E(_1c5[1]),_1cd=E(_1cc[1]),_1ce=E(_1cd[2]),_1cf=B(_19r(_1cd[1],_1ce[1],_1ce[2],_1ce[3],_1ce[4],_1ce[5],_1ce[6],_1cd[3],_1cd[4],_1cc[2],_1cc[3])),_1cb=_1cf[0]==0?E(_1cf[1]):[0];}var _1cg=_1cb;}else{var _1ch=E(_1c4[1]),_1ci=E(_1ch[1]),_1cj=E(_1ci[2]),_1ck=B(_19r(_1ci[1],_1cj[1],_1cj[2],_1cj[3],_1cj[4],_1cj[5],_1cj[6],_1ci[3],_1ci[4],_1ch[2],_1ch[3])),_1cg=_1ck[0]==0?E(_1ck[1]):[0];}var _1cl=_1cg;}else{var _1cl=E(_1a0);}var _1c2=_1cl;}var _1c0=_1c2;}var _1cm=_1c0;return _1cm;}),_1bY[1]));})];}var _1cn=_1bW;return _1cn;}),_1bS])),_1co=_1bU[2],_1cp=E(E(_1bT)[1]);if(!_1cp[0]){return E(_19G);}else{var _1cq=E(_1cp[1]);if(!_1cq[0]){return E(_1cp[2])[0]==0?E(_1bU):E(_19G);}else{var _1cr=E(_1bU[1]);if(!_1cr[0]){return [0,_9,_1co];}else{var _1cs=E(_1cr[1]);if(!_1cs[0]){return E(_1bU);}else{var _1ct=_1cs[1],_1cu=new T(function(){return [0,B(_15b(_1cq[1],0))];});return [0,[1,[1,new T(function(){return B(_1aF(_1cu,_1ct));})],[1,[1,new T(function(){return B(_19U(_1cu,_1ct));})],_1cr[2]]],_1co];}}}}},_1bP,new T(function(){return B(A(new T(function(){return B(_1av(_1bF));}),[_1bO]));},1)));}),[0,new T(function(){return E(B(A(_1bG,[_1bO]))[1]);}),[1,[1,_1bR,_9]]]];};},_1cv=[1],_1cw=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1cx=function(_1cy){return new F(function(){return err(_1cw);});},_1cz=new T(function(){return B(_1cx(_));}),_1cA=function(_1cB,_1cC,_1cD){var _1cE=E(_1cD);if(!_1cE[0]){var _1cF=_1cE[1],_1cG=E(_1cC);if(!_1cG[0]){var _1cH=_1cG[1],_1cI=_1cG[2];if(_1cH<=(imul(3,_1cF)|0)){return [0,(1+_1cH|0)+_1cF|0,E(E(_1cB)),E(_1cG),E(_1cE)];}else{var _1cJ=E(_1cG[3]);if(!_1cJ[0]){var _1cK=_1cJ[1],_1cL=E(_1cG[4]);if(!_1cL[0]){var _1cM=_1cL[1],_1cN=_1cL[2],_1cO=_1cL[3];if(_1cM>=(imul(2,_1cK)|0)){var _1cP=function(_1cQ){var _1cR=E(_1cL[4]);return _1cR[0]==0?[0,(1+_1cH|0)+_1cF|0,E(_1cN),E([0,(1+_1cK|0)+_1cQ|0,E(_1cI),E(_1cJ),E(_1cO)]),E([0,(1+_1cF|0)+_1cR[1]|0,E(E(_1cB)),E(_1cR),E(_1cE)])]:[0,(1+_1cH|0)+_1cF|0,E(_1cN),E([0,(1+_1cK|0)+_1cQ|0,E(_1cI),E(_1cJ),E(_1cO)]),E([0,1+_1cF|0,E(E(_1cB)),E(_1cv),E(_1cE)])];},_1cS=E(_1cO);return _1cS[0]==0?B(_1cP(_1cS[1])):B(_1cP(0));}else{return [0,(1+_1cH|0)+_1cF|0,E(_1cI),E(_1cJ),E([0,(1+_1cF|0)+_1cM|0,E(E(_1cB)),E(_1cL),E(_1cE)])];}}else{return E(_1cz);}}else{return E(_1cz);}}}else{return [0,1+_1cF|0,E(E(_1cB)),E(_1cv),E(_1cE)];}}else{var _1cT=E(_1cC);if(!_1cT[0]){var _1cU=_1cT[1],_1cV=_1cT[2],_1cW=_1cT[4],_1cX=E(_1cT[3]);if(!_1cX[0]){var _1cY=_1cX[1],_1cZ=E(_1cW);if(!_1cZ[0]){var _1d0=_1cZ[1],_1d1=_1cZ[2],_1d2=_1cZ[3];if(_1d0>=(imul(2,_1cY)|0)){var _1d3=function(_1d4){var _1d5=E(_1cZ[4]);return _1d5[0]==0?[0,1+_1cU|0,E(_1d1),E([0,(1+_1cY|0)+_1d4|0,E(_1cV),E(_1cX),E(_1d2)]),E([0,1+_1d5[1]|0,E(E(_1cB)),E(_1d5),E(_1cv)])]:[0,1+_1cU|0,E(_1d1),E([0,(1+_1cY|0)+_1d4|0,E(_1cV),E(_1cX),E(_1d2)]),E([0,1,E(E(_1cB)),E(_1cv),E(_1cv)])];},_1d6=E(_1d2);return _1d6[0]==0?B(_1d3(_1d6[1])):B(_1d3(0));}else{return [0,1+_1cU|0,E(_1cV),E(_1cX),E([0,1+_1d0|0,E(E(_1cB)),E(_1cZ),E(_1cv)])];}}else{return [0,3,E(_1cV),E(_1cX),E([0,1,E(E(_1cB)),E(_1cv),E(_1cv)])];}}else{var _1d7=E(_1cW);return _1d7[0]==0?[0,3,E(_1d7[2]),E([0,1,E(_1cV),E(_1cv),E(_1cv)]),E([0,1,E(E(_1cB)),E(_1cv),E(_1cv)])]:[0,2,E(E(_1cB)),E(_1cT),E(_1cv)];}}else{return [0,1,E(E(_1cB)),E(_1cv),E(_1cv)];}}},_1d8=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_1d9=function(_1da){return new F(function(){return err(_1d8);});},_1db=new T(function(){return B(_1d9(_));}),_1dc=function(_1dd,_1de,_1df){var _1dg=E(_1de);if(!_1dg[0]){var _1dh=_1dg[1],_1di=E(_1df);if(!_1di[0]){var _1dj=_1di[1],_1dk=_1di[2];if(_1dj<=(imul(3,_1dh)|0)){return [0,(1+_1dh|0)+_1dj|0,E(E(_1dd)),E(_1dg),E(_1di)];}else{var _1dl=E(_1di[3]);if(!_1dl[0]){var _1dm=_1dl[1],_1dn=_1dl[2],_1do=_1dl[3],_1dp=E(_1di[4]);if(!_1dp[0]){var _1dq=_1dp[1];if(_1dm>=(imul(2,_1dq)|0)){var _1dr=function(_1ds){var _1dt=E(_1dd),_1du=E(_1dl[4]);return _1du[0]==0?[0,(1+_1dh|0)+_1dj|0,E(_1dn),E([0,(1+_1dh|0)+_1ds|0,E(_1dt),E(_1dg),E(_1do)]),E([0,(1+_1dq|0)+_1du[1]|0,E(_1dk),E(_1du),E(_1dp)])]:[0,(1+_1dh|0)+_1dj|0,E(_1dn),E([0,(1+_1dh|0)+_1ds|0,E(_1dt),E(_1dg),E(_1do)]),E([0,1+_1dq|0,E(_1dk),E(_1cv),E(_1dp)])];},_1dv=E(_1do);return _1dv[0]==0?B(_1dr(_1dv[1])):B(_1dr(0));}else{return [0,(1+_1dh|0)+_1dj|0,E(_1dk),E([0,(1+_1dh|0)+_1dm|0,E(E(_1dd)),E(_1dg),E(_1dl)]),E(_1dp)];}}else{return E(_1db);}}else{return E(_1db);}}}else{return [0,1+_1dh|0,E(E(_1dd)),E(_1dg),E(_1cv)];}}else{var _1dw=E(_1df);if(!_1dw[0]){var _1dx=_1dw[1],_1dy=_1dw[2],_1dz=_1dw[4],_1dA=E(_1dw[3]);if(!_1dA[0]){var _1dB=_1dA[1],_1dC=_1dA[2],_1dD=_1dA[3],_1dE=E(_1dz);if(!_1dE[0]){var _1dF=_1dE[1];if(_1dB>=(imul(2,_1dF)|0)){var _1dG=function(_1dH){var _1dI=E(_1dd),_1dJ=E(_1dA[4]);return _1dJ[0]==0?[0,1+_1dx|0,E(_1dC),E([0,1+_1dH|0,E(_1dI),E(_1cv),E(_1dD)]),E([0,(1+_1dF|0)+_1dJ[1]|0,E(_1dy),E(_1dJ),E(_1dE)])]:[0,1+_1dx|0,E(_1dC),E([0,1+_1dH|0,E(_1dI),E(_1cv),E(_1dD)]),E([0,1+_1dF|0,E(_1dy),E(_1cv),E(_1dE)])];},_1dK=E(_1dD);return _1dK[0]==0?B(_1dG(_1dK[1])):B(_1dG(0));}else{return [0,1+_1dx|0,E(_1dy),E([0,1+_1dB|0,E(E(_1dd)),E(_1cv),E(_1dA)]),E(_1dE)];}}else{return [0,3,E(_1dC),E([0,1,E(E(_1dd)),E(_1cv),E(_1cv)]),E([0,1,E(_1dy),E(_1cv),E(_1cv)])];}}else{var _1dL=E(_1dz);return _1dL[0]==0?[0,3,E(_1dy),E([0,1,E(E(_1dd)),E(_1cv),E(_1cv)]),E(_1dL)]:[0,2,E(E(_1dd)),E(_1cv),E(_1dw)];}}else{return [0,1,E(E(_1dd)),E(_1cv),E(_1cv)];}}},_1dM=function(_1dN){return [0,1,E(E(_1dN)),E(_1cv),E(_1cv)];},_1dO=function(_1dP,_1dQ){var _1dR=E(_1dQ);if(!_1dR[0]){return new F(function(){return _1cA(_1dR[2],B(_1dO(_1dP,_1dR[3])),_1dR[4]);});}else{return new F(function(){return _1dM(_1dP);});}},_1dS=function(_1dT,_1dU){var _1dV=E(_1dU);if(!_1dV[0]){return new F(function(){return _1dc(_1dV[2],_1dV[3],B(_1dS(_1dT,_1dV[4])));});}else{return new F(function(){return _1dM(_1dT);});}},_1dW=function(_1dX,_1dY,_1dZ,_1e0,_1e1){return new F(function(){return _1dc(_1dZ,_1e0,B(_1dS(_1dX,_1e1)));});},_1e2=function(_1e3,_1e4,_1e5,_1e6,_1e7){return new F(function(){return _1cA(_1e5,B(_1dO(_1e3,_1e6)),_1e7);});},_1e8=function(_1e9,_1ea,_1eb,_1ec,_1ed,_1ee){var _1ef=E(_1ea);if(!_1ef[0]){var _1eg=_1ef[1],_1eh=_1ef[2],_1ei=_1ef[3],_1ej=_1ef[4];if((imul(3,_1eg)|0)>=_1eb){if((imul(3,_1eb)|0)>=_1eg){return [0,(_1eg+_1eb|0)+1|0,E(E(_1e9)),E(_1ef),E([0,_1eb,E(_1ec),E(_1ed),E(_1ee)])];}else{return new F(function(){return _1dc(_1eh,_1ei,B(_1e8(_1e9,_1ej,_1eb,_1ec,_1ed,_1ee)));});}}else{return new F(function(){return _1cA(_1ec,B(_1ek(_1e9,_1eg,_1eh,_1ei,_1ej,_1ed)),_1ee);});}}else{return new F(function(){return _1e2(_1e9,_1eb,_1ec,_1ed,_1ee);});}},_1ek=function(_1el,_1em,_1en,_1eo,_1ep,_1eq){var _1er=E(_1eq);if(!_1er[0]){var _1es=_1er[1],_1et=_1er[2],_1eu=_1er[3],_1ev=_1er[4];if((imul(3,_1em)|0)>=_1es){if((imul(3,_1es)|0)>=_1em){return [0,(_1em+_1es|0)+1|0,E(E(_1el)),E([0,_1em,E(_1en),E(_1eo),E(_1ep)]),E(_1er)];}else{return new F(function(){return _1dc(_1en,_1eo,B(_1e8(_1el,_1ep,_1es,_1et,_1eu,_1ev)));});}}else{return new F(function(){return _1cA(_1et,B(_1ek(_1el,_1em,_1en,_1eo,_1ep,_1eu)),_1ev);});}}else{return new F(function(){return _1dW(_1el,_1em,_1en,_1eo,_1ep);});}},_1ew=function(_1ex,_1ey,_1ez){var _1eA=E(_1ey);if(!_1eA[0]){var _1eB=_1eA[1],_1eC=_1eA[2],_1eD=_1eA[3],_1eE=_1eA[4],_1eF=E(_1ez);if(!_1eF[0]){var _1eG=_1eF[1],_1eH=_1eF[2],_1eI=_1eF[3],_1eJ=_1eF[4];if((imul(3,_1eB)|0)>=_1eG){if((imul(3,_1eG)|0)>=_1eB){return [0,(_1eB+_1eG|0)+1|0,E(E(_1ex)),E(_1eA),E(_1eF)];}else{return new F(function(){return _1dc(_1eC,_1eD,B(_1e8(_1ex,_1eE,_1eG,_1eH,_1eI,_1eJ)));});}}else{return new F(function(){return _1cA(_1eH,B(_1ek(_1ex,_1eB,_1eC,_1eD,_1eE,_1eI)),_1eJ);});}}else{return new F(function(){return _1dW(_1ex,_1eB,_1eC,_1eD,_1eE);});}}else{return new F(function(){return _1dO(_1ex,_1ez);});}},_1eK=function(_1eL,_1eM,_1eN,_1eO){var _1eP=E(_1eO);if(!_1eP[0]){var _1eQ=new T(function(){var _1eR=B(_1eK(_1eP[1],_1eP[2],_1eP[3],_1eP[4]));return [0,_1eR[1],_1eR[2]];});return [0,new T(function(){return E(E(_1eQ)[1]);}),new T(function(){return B(_1cA(_1eM,_1eN,E(_1eQ)[2]));})];}else{return [0,_1eM,_1eN];}},_1eS=function(_1eT,_1eU,_1eV,_1eW){var _1eX=E(_1eV);if(!_1eX[0]){var _1eY=new T(function(){var _1eZ=B(_1eS(_1eX[1],_1eX[2],_1eX[3],_1eX[4]));return [0,_1eZ[1],_1eZ[2]];});return [0,new T(function(){return E(E(_1eY)[1]);}),new T(function(){return B(_1dc(_1eU,E(_1eY)[2],_1eW));})];}else{return [0,_1eU,_1eW];}},_1f0=function(_1f1,_1f2){var _1f3=E(_1f1);if(!_1f3[0]){var _1f4=_1f3[1],_1f5=E(_1f2);if(!_1f5[0]){var _1f6=_1f5[1];if(_1f4<=_1f6){var _1f7=B(_1eS(_1f6,_1f5[2],_1f5[3],_1f5[4]));return new F(function(){return _1cA(_1f7[1],_1f3,_1f7[2]);});}else{var _1f8=B(_1eK(_1f4,_1f3[2],_1f3[3],_1f3[4]));return new F(function(){return _1dc(_1f8[1],_1f8[2],_1f5);});}}else{return E(_1f3);}}else{return E(_1f2);}},_1f9=function(_1fa,_1fb,_1fc,_1fd,_1fe){var _1ff=E(_1fa);if(!_1ff[0]){var _1fg=_1ff[1],_1fh=_1ff[2],_1fi=_1ff[3],_1fj=_1ff[4];if((imul(3,_1fg)|0)>=_1fb){if((imul(3,_1fb)|0)>=_1fg){return new F(function(){return _1f0(_1ff,[0,_1fb,E(_1fc),E(_1fd),E(_1fe)]);});}else{return new F(function(){return _1dc(_1fh,_1fi,B(_1f9(_1fj,_1fb,_1fc,_1fd,_1fe)));});}}else{return new F(function(){return _1cA(_1fc,B(_1fk(_1fg,_1fh,_1fi,_1fj,_1fd)),_1fe);});}}else{return [0,_1fb,E(_1fc),E(_1fd),E(_1fe)];}},_1fk=function(_1fl,_1fm,_1fn,_1fo,_1fp){var _1fq=E(_1fp);if(!_1fq[0]){var _1fr=_1fq[1],_1fs=_1fq[2],_1ft=_1fq[3],_1fu=_1fq[4];if((imul(3,_1fl)|0)>=_1fr){if((imul(3,_1fr)|0)>=_1fl){return new F(function(){return _1f0([0,_1fl,E(_1fm),E(_1fn),E(_1fo)],_1fq);});}else{return new F(function(){return _1dc(_1fm,_1fn,B(_1f9(_1fo,_1fr,_1fs,_1ft,_1fu)));});}}else{return new F(function(){return _1cA(_1fs,B(_1fk(_1fl,_1fm,_1fn,_1fo,_1ft)),_1fu);});}}else{return [0,_1fl,E(_1fm),E(_1fn),E(_1fo)];}},_1fv=function(_1fw,_1fx){var _1fy=E(_1fw);if(!_1fy[0]){var _1fz=_1fy[1],_1fA=_1fy[2],_1fB=_1fy[3],_1fC=_1fy[4],_1fD=E(_1fx);if(!_1fD[0]){var _1fE=_1fD[1],_1fF=_1fD[2],_1fG=_1fD[3],_1fH=_1fD[4];if((imul(3,_1fz)|0)>=_1fE){if((imul(3,_1fE)|0)>=_1fz){return new F(function(){return _1f0(_1fy,_1fD);});}else{return new F(function(){return _1dc(_1fA,_1fB,B(_1f9(_1fC,_1fE,_1fF,_1fG,_1fH)));});}}else{return new F(function(){return _1cA(_1fF,B(_1fk(_1fz,_1fA,_1fB,_1fC,_1fG)),_1fH);});}}else{return E(_1fy);}}else{return E(_1fx);}},_1fI=function(_1fJ,_1fK){var _1fL=E(_1fK);if(!_1fL[0]){var _1fM=_1fL[2],_1fN=_1fL[3],_1fO=_1fL[4];if(!B(A(_1fJ,[_1fM]))){return new F(function(){return _1fv(B(_1fI(_1fJ,_1fN)),B(_1fI(_1fJ,_1fO)));});}else{return new F(function(){return _1ew(_1fM,B(_1fI(_1fJ,_1fN)),B(_1fI(_1fJ,_1fO)));});}}else{return [1];}},_1fP=function(_1fQ,_1fR,_1fS,_1fT){while(1){var _1fU=E(_1fT);if(!_1fU[0]){_1fQ=_1fU[1];_1fR=_1fU[2];_1fS=_1fU[3];_1fT=_1fU[4];continue;}else{return E(_1fR);}}},_1fV=function(_1fW,_1fX){return [0];},_1fY=function(_1fZ){return E(E(_1fZ)[1]);},_1g0=function(_1g1,_1g2,_1g3,_1g4,_1g5,_1g6,_1g7,_1g8,_1g9,_1ga,_1gb){var _1gc=new T(function(){return B(_1bt(_1g1,_1g2,_1g3,_1g4,_1g5,_1g6,_1g7,_1g8,_1g9,_1ga,_1gb,_12e));}),_1gd=new T(function(){return B(_193(_1gb,_1g9,_1ga,_1g4,_1g7,_1g3,_1g6,_1g5,_1g1,_1g2));}),_1ge=[0,_1gd,new T(function(){return B(_11X(_1au,_13r,new T(function(){return B(_Yl(new T(function(){return B(_Z3(new T(function(){return B(_YJ(_1g7,_1g6,_1g5,_1g4,_1g3,_1g1,_1g2));})));})));}),new T(function(){return B(_12M(new T(function(){return B(_13f(new T(function(){return B(_b9(_1g7,_1g6,_1g5,_1g4,_1g3,_1g1,_1g2));})));})));}),_1g7,_1g6,_1g5,_1g4,_1g3,_1g1,_1g2));}),_1fV,_1];return function(_1gf,_1gg,_1gh){var _1gi=B(_1fI(function(_1gj){var _1gk=B(A(_1gd,[new T(function(){return B(A(_1gc,[_1gj,_1gg,_1gh]));}),_1gj]));return _1gk[0]==0?false:B(_1b7(_1ge,_1gk[1]))[0]==0?true:false;},B(_1fY(_1gf))));if(!_1gi[0]){var _1gl=new T(function(){var _1gm=E(_1gi[4]);return _1gm[0]==0?B(_1fP(_1gm[1],_1gm[2],_1gm[3],_1gm[4])):E(_1gi[2]);}),_1gn=new T(function(){return B(A(_1gc,[_1gl,_1gg,_1gh]));}),_1go=B(A(_1gd,[_1gl,_1gn]));if(!_1go[0]){return [0];}else{var _1gp=B(_1b7(_1ge,_1go[1]));if(!_1gp[0]){var _1gq=_1gp[1];return [1,new T(function(){var _1gr=E(E(_1gn)[2]);return [0,new T(function(){return B(_7X(function(_1gs){return new F(function(){return _102(_1gq,_1gs);});},_1gr[1]));}),new T(function(){return B(_102(_1gq,_1gr[2]));})];})];}else{return [0];}}}else{return [0];}};},_1gt=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_1gu=new T(function(){return B(err(_1gt));}),_1gv=function(_1gw,_1gx,_1gy,_1gz){while(1){var _1gA=E(_1gy);if(!_1gA[0]){_1gw=_1gA[1];_1gx=_1gA[2];_1gy=_1gA[3];_1gz=_1gA[4];continue;}else{return E(_1gx);}}},_1gB=function(_1gC,_1gD){var _1gE=B(_1fI(function(_1gF){return new F(function(){return _lv(E(_1gF)[2],_1gC);});},_1gD));if(!_1gE[0]){var _1gG=E(_1gE[3]);return _1gG[0]==0?B(_1gv(_1gG[1],_1gG[2],_1gG[3],_1gG[4])):E(_1gE[2]);}else{return E(_1gu);}},_1gH=[1,_9],_1gI=function(_1gJ,_1gK,_1gL,_1gM,_1gN,_1gO,_1gP,_1gQ,_1gR,_1gS,_1gT,_1gU,_1gV,_1gW){var _1gX=E(_1gW);if(!_1gX[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_1gQ,[_1gV]));}),_9]],_9],[1,[1,new T(function(){return B(A(_1gQ,[_1gV]));}),_9]]]];}else{var _1gY=function(_1gZ){var _1h0=E(_1gZ);if(!_1h0[0]){return E(_1gH);}else{var _1h1=E(_1h0[1]),_1h2=B(_1gI(_1gJ,_1gK,_1gL,_1gM,_1gN,_1gO,_1gP,_1gQ,_1gR,_1gS,_1gT,_1gU,_1h1[1],_1h1[2]));if(!_1h2[0]){return [0];}else{var _1h3=B(_1gY(_1h0[2]));return _1h3[0]==0?[0]:[1,[1,_1h2[1],_1h3[1]]];}}},_1h4=B(_1gY(_1gX[2]));return _1h4[0]==0?[0]:B(A(_1g0,[_1gJ,_1gK,_1gL,_1gM,_1gN,_1gO,_1gP,_1gQ,_1gR,_1gS,_1gT,new T(function(){return B(_1gB(_1gX[1],_1gU));}),_1h4[1],_1gV]));}},_1h5=function(_1h6,_1h7,_1h8,_1h9,_1ha,_1hb,_1hc,_1hd,_1he,_1hf,_1hg,_1hh,_1hi,_1hj,_1hk){var _1hl=E(_1hk);return new F(function(){return _1gI(_1h6,_1h7,_1h8,_1h9,_1ha,_1hb,_1hc,_1hd,_1he,_1hh,_1hi,_1hj,_1hl[1],_1hl[2]);});},_1hm=function(_1hn){return new F(function(){return _db(_1hn,_9);});},_1ho=function(_1hp,_1hq){return _1hp<=B(_15b(_1hq,0))?[1,new T(function(){var _1hr=_1hp-1|0;if(_1hr>=0){var _1hs=B(_gp(B(_1hm(_1hq)),_1hr));}else{var _1hs=E(_gm);}var _1ht=_1hs,_1hu=_1ht;return _1hu;})]:[0];},_1hv=function(_1hw,_1hx,_1hy){var _1hz=function(_1hA){return _1hA<=B(_15b(_1hy,0))?[1,[0,new T(function(){var _1hB=_1hw-1|0;if(_1hB>=0){var _1hC=B(_gp(B(_1hm(_1hy)),_1hB));}else{var _1hC=E(_gm);}var _1hD=_1hC,_1hE=_1hD;return _1hE;}),new T(function(){var _1hF=_1hx-1|0;if(_1hF>=0){var _1hG=B(_gp(B(_1hm(_1hy)),_1hF));}else{var _1hG=E(_gm);}var _1hH=_1hG,_1hI=_1hH;return _1hI;})]]:[0];};return _1hw>_1hx?B(_1hz(_1hw)):B(_1hz(_1hx));},_1hJ=[0],_1hK=new T(function(){return B(unCStr("depends on unjustified lines"));}),_1hL=new T(function(){return B(unCStr("unavailable lines"));}),_1hM=new T(function(){return B(unCStr("wrong number of premises"));}),_1hN=new T(function(){return B(unCStr("Impossible Error 1"));}),_1hO=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1hP=new T(function(){return B(unCStr("PR"));}),_1hQ=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1hR=function(_1hS,_1hT,_1hU,_1hV,_1hW,_1hX){var _1hY=function(_1hZ){var _1i0=B(A(_1hV,[_1hT]));if(!_1i0[0]){return [0,[1,_1hQ,_1hW],[1,_28,_1hX]];}else{var _1i1=E(_1i0[1]);if(!_1i1[0]){switch(E(E(_1i1[1])[1])){case 1:var _1i2=E(_1hU);if(!_1i2[0]){return [0,[1,_1hM,_1hW],[1,_28,_1hX]];}else{if(!E(_1i2[2])[0]){var _1i3=B(_1ho(E(_1i2[1])[1],_1hX));if(!_1i3[0]){return [0,[1,_1hL,_1hW],[1,_28,_1hX]];}else{var _1i4=E(_1i3[1]);return _1i4[0]==0?[0,[1,_1hK,_1hW],[1,_28,_1hX]]:[0,[1,_9,_1hW],[1,[1,[0,_1hS,[1,_1hT,[1,_1i4[1],_9]]]],_1hX]];}}else{return [0,[1,_1hM,_1hW],[1,_28,_1hX]];}}break;case 2:var _1i5=E(_1hU);if(!_1i5[0]){return [0,[1,_1hM,_1hW],[1,_28,_1hX]];}else{var _1i6=E(_1i5[2]);if(!_1i6[0]){return [0,[1,_1hM,_1hW],[1,_28,_1hX]];}else{if(!E(_1i6[2])[0]){var _1i7=B(_1hv(E(_1i5[1])[1],E(_1i6[1])[1],_1hX));if(!_1i7[0]){return [0,[1,_1hL,_1hW],[1,_28,_1hX]];}else{var _1i8=E(_1i7[1]),_1i9=E(_1i8[1]);if(!_1i9[0]){return [0,[1,_1hK,_1hW],[1,_28,_1hX]];}else{var _1ia=E(_1i8[2]);return _1ia[0]==0?[0,[1,_1hK,_1hW],[1,_28,_1hX]]:[0,[1,_9,_1hW],[1,[1,[0,_1hS,[1,_1hT,[1,_1i9[1],[1,_1ia[1],_9]]]]],_1hX]];}}}else{return [0,[1,_1hM,_1hW],[1,_28,_1hX]];}}}break;default:return [0,[1,_1hN,_1hW],[1,_28,_1hX]];}}else{return [0,[1,_1hO,_1hW],[1,_28,_1hX]];}}};return !B(_lv(_1hT,_1hP))?B(_1hY(_)):E(_1hU)[0]==0?[0,[1,_9,_1hW],[1,[1,[0,_1hS,_1hJ]],_1hX]]:B(_1hY(_));},_1ib=new T(function(){return B(unCStr("depends on an unjustified line"));}),_1ic=new T(function(){return B(unCStr("unavailable line"));}),_1id=function(_1ie,_1if,_1ig,_1ih){return E(B(_1ii(_1ie,_1if,[1,_9,_1ig],[1,_28,_1ih]))[2]);},_1ij=function(_1ik,_1il,_1im,_1in,_1io,_1ip,_1iq,_1ir){var _1is=B(_1hv(_1in,_1io,B(_1id(_1ik,_1il,_1iq,_1ir))));if(!_1is[0]){return new F(function(){return _1ii(_1ik,_1il,[1,_1ic,_1iq],[1,_28,_1ir]);});}else{var _1it=E(_1is[1]),_1iu=E(_1it[1]);if(!_1iu[0]){return new F(function(){return _1ii(_1ik,_1il,[1,_1ib,_1iq],[1,_28,_1ir]);});}else{var _1iv=E(_1it[2]);return _1iv[0]==0?B(_1ii(_1ik,_1il,[1,_1ib,_1iq],[1,_28,_1ir])):B(_1ii(_1ik,_1il,[1,_9,_1iq],[1,[1,[0,_1im,[1,_1ip,[1,_1iu[1],[1,_1iv[1],_9]]]]],_1ir]));}}},_1iw=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1ix=function(_1iy,_1iz,_1iA,_1iB,_1iC,_1iD,_1iE){var _1iF=E(_1iC);if(!_1iF[0]){return new F(function(){return _1ii(_1iy,_1iz,[1,_1iw,_1iD],[1,_28,_1iE]);});}else{var _1iG=E(_1iF[2]);if(!_1iG[0]){return new F(function(){return _1ii(_1iy,_1iz,[1,_1iw,_1iD],[1,_28,_1iE]);});}else{if(!E(_1iG[2])[0]){return new F(function(){return _1ij(_1iy,_1iz,_1iA,E(_1iF[1])[1],E(_1iG[1])[1],_1iB,_1iD,_1iE);});}else{return new F(function(){return _1ii(_1iy,_1iz,[1,_1iw,_1iD],[1,_28,_1iE]);});}}}},_1iH=function(_1iI,_1iJ,_1iK){return [0,[1,_9,_1iJ],[1,_28,new T(function(){var _1iL=B(_15b(_1iJ,0))-E(_1iI)[1]|0,_1iM=new T(function(){return _1iL>=0?B(_19P(_1iL,_1iK)):E(_1iK);});if(_1iL>0){var _1iN=function(_1iO,_1iP){var _1iQ=E(_1iO);return _1iQ[0]==0?E(_1iM):_1iP>1?[1,_28,new T(function(){return B(_1iN(_1iQ[2],_1iP-1|0));})]:E([1,_28,_1iM]);},_1iR=B(_1iN(_1iK,_1iL));}else{var _1iR=E(_1iM);}var _1iS=_1iR,_1iT=_1iS,_1iU=_1iT,_1iV=_1iU;return _1iV;})]];},_1iW=function(_1iX,_1iY,_1iZ,_1j0,_1j1,_1j2,_1j3){var _1j4=new T(function(){return E(B(_1ii(_1iX,_1iY,[1,_9,_1j2],[1,_28,_1j3]))[2]);});if(_1j0<=B(_15b(_1j4,0))){var _1j5=_1j0-1|0;if(_1j5>=0){var _1j6=B(_gp(B(_1hm(_1j4)),_1j5));return _1j6[0]==0?B(_1ii(_1iX,_1iY,[1,_1ib,_1j2],[1,_28,_1j3])):B(_1ii(_1iX,_1iY,[1,_9,_1j2],[1,[1,[0,_1iZ,[1,_1j1,[1,_1j6[1],_9]]]],_1j3]));}else{return E(_gm);}}else{return new F(function(){return _1ii(_1iX,_1iY,[1,_1ic,_1j2],[1,_28,_1j3]);});}},_1j7=function(_1j8,_1j9,_1ja,_1jb,_1jc,_1jd,_1je){var _1jf=E(_1jc);if(!_1jf[0]){return new F(function(){return _1ii(_1j8,_1j9,[1,_1iw,_1jd],[1,_28,_1je]);});}else{if(!E(_1jf[2])[0]){return new F(function(){return _1iW(_1j8,_1j9,_1ja,E(_1jf[1])[1],_1jb,_1jd,_1je);});}else{return new F(function(){return _1ii(_1j8,_1j9,[1,_1iw,_1jd],[1,_28,_1je]);});}}},_1jg=new T(function(){return B(unCStr("Open Subproof"));}),_1jh=new T(function(){return B(unCStr("Impossible Error 2"));}),_1ji=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1jj=new T(function(){return B(unCStr("SHOW"));}),_1jk=function(_1jl,_1jm,_1jn,_1jo,_1jp,_1jq,_1jr){if(!B(_lv(_1jm,_1jj))){var _1js=B(A(_1jo,[_1jm]));if(!_1js[0]){return [0,[1,_1hQ,_1jq],[1,_28,_1jr]];}else{var _1jt=E(_1js[1]);if(!_1jt[0]){return [0,[1,_1ji,_1jq],[1,_28,_1jr]];}else{switch(E(E(_1jt[1])[1])){case 1:var _1ju=B(_1j7(_1jp,_1jo,_1jl,_1jm,_1jn,_1jq,_1jr));return new F(function(){return _1iH(new T(function(){return [0,B(_15b(_1jq,0))+1|0];},1),_1ju[1],_1ju[2]);});break;case 2:var _1jv=B(_1ix(_1jp,_1jo,_1jl,_1jm,_1jn,_1jq,_1jr));return new F(function(){return _1iH(new T(function(){return [0,B(_15b(_1jq,0))+1|0];},1),_1jv[1],_1jv[2]);});break;default:return [0,[1,_1jh,_1jq],[1,_28,_1jr]];}}}}else{var _1jw=B(_1ii(_1jp,_1jo,[1,_1jg,_1jq],[1,_28,_1jr]));return new F(function(){return _1iH(new T(function(){return [0,B(_15b(_1jq,0))+1|0];},1),_1jw[1],_1jw[2]);});}},_1jx=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1jy=new T(function(){return B(unCStr("formula syntax error"));}),_1jz=function(_1jA,_1jB,_1jC,_1jD,_1jE){var _1jF=E(_1jA);if(!_1jF[0]){return E(_1jB)[0]==0?[0,[1,_1jy,_1jD],[1,_28,_1jE]]:[0,[1,_1jx,_1jD],[1,_28,_1jE]];}else{var _1jG=_1jF[1],_1jH=E(_1jB);if(!_1jH[0]){var _1jI=E(_1jG);return new F(function(){return _1hR(_1jI[1],_1jI[2],_1jI[3],_1jC,_1jD,_1jE);});}else{var _1jJ=E(_1jG);return new F(function(){return _1jk(_1jJ[1],_1jJ[2],_1jJ[3],_1jC,_1jH,_1jD,_1jE);});}}},_1ii=function(_1jK,_1jL,_1jM,_1jN){return new F(function(){return (function(_1jO,_1jP,_1jQ){while(1){var _1jR=E(_1jQ);if(!_1jR[0]){return [0,_1jO,_1jP];}else{var _1jS=E(_1jR[1]),_1jT=B(_1jz(_1jS[1],_1jS[2],_1jL,_1jO,_1jP));_1jO=_1jT[1];_1jP=_1jT[2];_1jQ=_1jR[2];continue;}}})(_1jM,_1jN,_1jK);});},_1jU=function(_1jV,_1jW){while(1){var _1jX=E(_1jW);if(!_1jX[0]){return true;}else{if(!B(A(_1jV,[_1jX[1]]))){return false;}else{_1jW=_1jX[2];continue;}}}},_1jY=[0,666],_1jZ=[0,_,_1jY],_1k0=[1,_1jZ],_1k1=[0,_1k0,_1hJ],_1k2=function(_1k3){return new F(function(){return _lv(_1k3,_9);});},_1k4=function(_1k5,_1k6){var _1k7=B(_1ii(_1k5,_1k6,_9,_9)),_1k8=_1k7[1];return !B(_1jU(_1k2,_1k8))?[0,_1k8]:[1,new T(function(){var _1k9=B(_15b(_1k5,0))-1|0;if(_1k9>=0){var _1ka=B(_gp(B(_db(_1k7[2],_9)),_1k9)),_1kb=_1ka[0]==0?E(_1k1):E(_1ka[1]);}else{var _1kb=E(_gm);}var _1kc=_1kb,_1kd=_1kc,_1ke=_1kd;return _1ke;})];},_1kf=function(_1kg,_1kh){return E(_1);},_1ki=function(_1kj,_1kk,_1kl,_1km){var _1kn=E(_1kl);switch(_1kn[0]){case 0:var _1ko=E(_1km);return _1ko[0]==0?E(_1):E(_1ko[1]);case 1:return new F(function(){return A(_1kj,[_1kn[1],_9]);});break;case 2:return new F(function(){return A(_1kk,[_1kn[1],[1,new T(function(){return B(_1ki(_1kj,_1kk,_1kn[2],_1km));}),_9]]);});break;default:return new F(function(){return A(_1kk,[_1kn[1],[1,new T(function(){return B(_1ki(_1kj,_1kk,_1kn[2],_1km));}),[1,new T(function(){return B(_1ki(_1kj,_1kk,_1kn[3],_1km));}),_9]]]);});}},_1kp=function(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,_1kw,_1kx){var _1ky=E(_1kw);switch(_1ky[0]){case 0:return [0];case 1:return new F(function(){return A(_1kt,[_1ky[1],_9]);});break;case 2:return new F(function(){return A(_1kq,[_1ky[1],[1,new T(function(){return B(_1ki(_1kt,_1ku,_1ky[2],_1kx));}),_9]]);});break;case 3:return new F(function(){return A(_1kq,[_1ky[1],[1,new T(function(){return B(_1ki(_1kt,_1ku,_1ky[2],_1kx));}),[1,new T(function(){return B(_1ki(_1kt,_1ku,_1ky[3],_1kx));}),_9]]]);});break;case 4:return new F(function(){return A(_1kr,[_1ky[1],[1,new T(function(){return B(_1kp(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,_1ky[2],_1kx));}),_9]]);});break;case 5:return new F(function(){return A(_1kr,[_1ky[1],[1,new T(function(){return B(_1kp(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,_1ky[2],_1kx));}),[1,new T(function(){return B(_1kp(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,_1ky[3],_1kx));}),_9]]]);});break;default:var _1kz=_1ky[1],_1kA=_1ky[2];return new F(function(){return A(_1ks,[_1kz,[1,new T(function(){return B(A(_1kv,[new T(function(){return B(A(_1kA,[_ae]));}),_1kz]));}),[1,new T(function(){return B(_1kp(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,B(A(_1kA,[_ae])),[1,new T(function(){return B(A(_1kv,[new T(function(){return B(A(_1kA,[_ae]));}),_1kz]));}),_9]));}),_9]]]);});}},_1kB=[0,95],_1kC=[1,_1kB,_9],_1kD=[1,_1kC,_9],_1kE=function(_1kF,_){return _1kF;},_1kG=function(_1kH){var _1kI=E(_1kH);return _1kI[0]==0?E(_1kE):function(_1kJ,_){var _1kK=B(A(new T(function(){var _1kL=E(_1kI[1]);return B(_1kM(_1kL[1],_1kL[2]));}),[_1kJ,_])),_1kN=_1kK,_1kO=B(A(new T(function(){return B(_1kG(_1kI[2]));}),[_1kJ,_])),_1kP=_1kO;return _1kJ;};},_1kQ=function(_1kR,_1kS){return function(_1kT,_){var _1kU=B(A(new T(function(){var _1kV=E(_1kR);return B(_1kM(_1kV[1],_1kV[2]));}),[_1kT,_])),_1kW=_1kU,_1kX=B(A(new T(function(){return B(_1kG(_1kS));}),[_1kT,_])),_1kY=_1kX;return _1kT;};},_1kZ=function(_1l0,_1l1){return new F(function(){return _F(0,E(_1l0)[1],_1l1);});},_1l2=function(_1l3){return function(_mc,_18e){return new F(function(){return _56(new T(function(){return B(_2T(_1kZ,_1l3,_9));}),_mc,_18e);});};},_1l4=function(_1l5){return function(_mc,_18e){return new F(function(){return _56(new T(function(){return B(_1kp(_Q,_u,_Q,_N,_Q,_1kf,_1l5,_1kD));}),_mc,_18e);});};},_1l6=new T(function(){return B(unCStr("open"));}),_1l7=new T(function(){return B(unCStr("termination"));}),_1l8=new T(function(){return B(unCStr("closed"));}),_1l9=function(_1la){var _1lb=E(_1la);return _1lb[0]==0?E(_1kE):function(_1lc,_){var _1ld=B(A(new T(function(){var _1le=E(_1lb[1]);return B(_1kM(_1le[1],_1le[2]));}),[_1lc,_])),_1lf=_1ld,_1lg=B(A(new T(function(){return B(_1l9(_1lb[2]));}),[_1lc,_])),_1lh=_1lg;return _1lc;};},_1li=function(_1lj,_1lk){return function(_1ll,_){var _1lm=B(A(new T(function(){var _1ln=E(_1lj);return B(_1kM(_1ln[1],_1ln[2]));}),[_1ll,_])),_1lo=_1lm,_1lp=B(A(new T(function(){return B(_1l9(_1lk));}),[_1ll,_])),_1lq=_1lp;return _1ll;};},_1lr=new T(function(){return B(unCStr("SHOW"));}),_1kM=function(_1ls,_1lt){var _1lu=E(_1ls);if(!_1lu[0]){return function(_mc,_18e){return new F(function(){return _bX(_56,_1lu[1],_mc,_18e);});};}else{var _1lv=E(_1lu[1]),_1lw=_1lv[1],_1lx=_1lv[2],_1ly=_1lv[3];if(!B(_lv(_1lx,_1lr))){var _1lz=E(_1lt);return _1lz[0]==0?function(_mc,_18e){return new F(function(){return _bX(_63,function(_1lA,_){var _1lB=B(_5T(_1l4,_1lw,_1lA,_)),_1lC=_1lB,_1lD=B(_5T(_63,function(_1lE,_){var _1lF=B(_5T(_56,_1lx,_1lE,_)),_1lG=_1lF,_1lH=B(_5T(_1l2,_1ly,_1lE,_)),_1lI=_1lH;return _1lE;},_1lA,_)),_1lJ=_1lD;return _1lA;},_mc,_18e);});}:function(_mc,_18e){return new F(function(){return _bX(_63,function(_1lK,_){var _1lL=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1kp(_Q,_u,_Q,_N,_Q,_1kf,_1lw,_1kD));})));}),_1lK,_)),_1lM=_1lL,_1lN=B(_bX(_63,function(_1lO,_){var _1lP=B(_5T(_63,new T(function(){return B(_1kQ(_1lz[1],_1lz[2]));}),_1lO,_)),_1lQ=_1lP,_1lR=B(_bX(_63,function(_1lS,_){var _1lT=B(_5T(_56,_9,_1lS,_)),_1lU=_1lT,_1lV=B(A(_5d,[_5q,_1lU,_bP,_1l7,_])),_1lW=_1lV,_1lX=B(_5T(_63,function(_1lY,_){var _1lZ=B(_5T(_56,_1lx,_1lY,_)),_1m0=_1lZ,_1m1=B(_5T(_1l2,_1ly,_1lY,_)),_1m2=_1m1;return _1lY;},_1lS,_)),_1m3=_1lX;return _1lS;},_1lO,_)),_1m4=_1lR;return _1lO;},_1lK,_)),_1m5=_1lN,_1m6=B(A(_5d,[_5q,_1m5,_bP,_1l8,_])),_1m7=_1m6;return _1lK;},_mc,_18e);});};}else{var _1m8=E(_1lt);return _1m8[0]==0?function(_mc,_18e){return new F(function(){return _bX(_63,function(_bB,_){return new F(function(){return _5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1kp(_Q,_u,_Q,_N,_Q,_1kf,_1lw,_1kD));})));}),_bB,_);});},_mc,_18e);});}:function(_mc,_18e){return new F(function(){return _bX(_63,function(_1m9,_){var _1ma=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1kp(_Q,_u,_Q,_N,_Q,_1kf,_1lw,_1kD));})));}),_1m9,_)),_1mb=_1ma,_1mc=B(_bX(_63,function(_bB,_){return new F(function(){return _5T(_63,new T(function(){return B(_1li(_1m8[1],_1m8[2]));}),_bB,_);});},_1m9,_)),_1md=_1mc,_1me=B(A(_5d,[_5q,_1md,_bP,_1l6,_])),_1mf=_1me;return _1m9;},_mc,_18e);});};}}},_1mg=function(_1mh){var _1mi=E(_1mh);return _1mi[0]==0?E(_1kE):function(_1mj,_){var _1mk=B(A(new T(function(){var _1ml=E(_1mi[1]);return B(_1kM(_1ml[1],_1ml[2]));}),[_1mj,_])),_1mm=_1mk,_1mn=B(A(new T(function(){return B(_1mg(_1mi[2]));}),[_1mj,_])),_1mo=_1mn;return _1mj;};},_1mp=[0,10],_1mq=[1,_1mp,_9],_1mr=function(_1ms,_1mt,_){var _1mu=jsCreateElem(toJSStr(E(_1ms))),_1mv=_1mu,_1mw=jsAppendChild(_1mv,E(_1mt)[1]);return [0,_1mv];},_1mx=function(_1my,_1mz,_1mA,_){var _1mB=B(_1mr(_1my,_1mA,_)),_1mC=_1mB,_1mD=B(A(_1mz,[_1mC,_])),_1mE=_1mD;return _1mC;},_1mF=new T(function(){return B(unCStr("()"));}),_1mG=new T(function(){return B(unCStr("GHC.Tuple"));}),_1mH=new T(function(){return B(unCStr("ghc-prim"));}),_1mI=new T(function(){var _1mJ=hs_wordToWord64(2170319554),_1mK=_1mJ,_1mL=hs_wordToWord64(26914641),_1mM=_1mL;return [0,_1mK,_1mM,[0,_1mK,_1mM,_1mH,_1mG,_1mF],_9];}),_1mN=function(_1mO){return E(_1mI);},_1mP=new T(function(){return B(unCStr("PerchM"));}),_1mQ=new T(function(){return B(unCStr("Haste.Perch"));}),_1mR=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1mS=new T(function(){var _1mT=hs_wordToWord64(3005229400),_1mU=_1mT,_1mV=hs_wordToWord64(2682402736),_1mW=_1mV;return [0,_1mU,_1mW,[0,_1mU,_1mW,_1mR,_1mQ,_1mP],_9];}),_1mX=function(_1mY){return E(_1mS);},_1mZ=function(_1n0){var _1n1=E(_1n0);if(!_1n1[0]){return [0];}else{var _1n2=E(_1n1[1]);return [1,[0,_1n2[1],_1n2[2]],new T(function(){return B(_1mZ(_1n1[2]));})];}},_1n3=function(_1n4,_1n5){var _1n6=E(_1n4);if(!_1n6){return [0,_9,_1n5];}else{var _1n7=E(_1n5);if(!_1n7[0]){return [0,_9,_9];}else{var _1n8=new T(function(){var _1n9=B(_1n3(_1n6-1|0,_1n7[2]));return [0,_1n9[1],_1n9[2]];});return [0,[1,_1n7[1],new T(function(){return E(E(_1n8)[1]);})],new T(function(){return E(E(_1n8)[2]);})];}}},_1na=[0,120],_1nb=[0,48],_1nc=function(_1nd){var _1ne=new T(function(){var _1nf=B(_1n3(8,new T(function(){var _1ng=md5(toJSStr(E(_1nd))),_1nh=_1ng;return fromJSStr(_1nh);})));return [0,_1nf[1],_1nf[2]];}),_1ni=parseInt([0,toJSStr([1,_1nb,[1,_1na,new T(function(){return E(E(_1ne)[1]);})]])]),_1nj=_1ni,_1nk=new T(function(){var _1nl=B(_1n3(8,new T(function(){return E(E(_1ne)[2]);})));return [0,_1nl[1],_1nl[2]];}),_1nm=parseInt([0,toJSStr([1,_1nb,[1,_1na,new T(function(){return E(E(_1nk)[1]);})]])]),_1nn=_1nm,_1no=hs_mkWord64(_1nj,_1nn),_1np=_1no,_1nq=parseInt([0,toJSStr([1,_1nb,[1,_1na,new T(function(){return E(B(_1n3(8,new T(function(){return E(E(_1nk)[2]);})))[1]);})]])]),_1nr=_1nq,_1ns=hs_mkWord64(_1nr,_1nr),_1nt=_1ns;return [0,_1np,_1nt];},_1nu=function(_1nv,_1nw){var _1nx=jsShowI(_1nv),_1ny=_1nx,_1nz=md5(_1ny),_1nA=_1nz;return new F(function(){return _e(fromJSStr(_1nA),new T(function(){var _1nB=jsShowI(_1nw),_1nC=_1nB,_1nD=md5(_1nC),_1nE=_1nD;return fromJSStr(_1nE);},1));});},_1nF=function(_1nG){var _1nH=E(_1nG);return new F(function(){return _1nu(_1nH[1],_1nH[2]);});},_1nI=function(_1nJ,_1nK){return function(_1nL){return E(new T(function(){var _1nM=B(A(_1nJ,[_])),_1nN=E(_1nM[3]),_1nO=_1nN[1],_1nP=_1nN[2],_1nQ=B(_e(_1nM[4],[1,new T(function(){return B(A(_1nK,[_]));}),_9]));if(!_1nQ[0]){var _1nR=[0,_1nO,_1nP,_1nN,_9];}else{var _1nS=B(_1nc(new T(function(){return B(_7r(B(_7X(_1nF,[1,[0,_1nO,_1nP],new T(function(){return B(_1mZ(_1nQ));})]))));},1))),_1nR=[0,_1nS[1],_1nS[2],_1nN,_1nQ];}var _1nT=_1nR,_1nU=_1nT;return _1nU;}));};},_1nV=new T(function(){return B(_1nI(_1mX,_1mN));}),_1nW=function(_1nX,_1nY,_1nZ,_){var _1o0=E(_1nY),_1o1=B(A(_1nX,[_1nZ,_])),_1o2=_1o1,_1o3=B(A(_5d,[_5q,_1o2,_1o0[1],_1o0[2],_])),_1o4=_1o3;return _1o2;},_1o5=function(_1o6,_1o7){while(1){var _1o8=(function(_1o9,_1oa){var _1ob=E(_1oa);if(!_1ob[0]){return E(_1o9);}else{_1o6=function(_1oc,_){return new F(function(){return _1nW(_1o9,_1ob[1],_1oc,_);});};_1o7=_1ob[2];return null;}})(_1o6,_1o7);if(_1o8!=null){return _1o8;}}},_1od=new T(function(){return B(unCStr("value"));}),_1oe=new T(function(){return B(unCStr("id"));}),_1of=new T(function(){return B(unCStr("onclick"));}),_1og=new T(function(){return B(unCStr("checked"));}),_1oh=[0,_1og,_9],_1oi=new T(function(){return B(unCStr("type"));}),_1oj=new T(function(){return B(unCStr("input"));}),_1ok=function(_1ol,_){return new F(function(){return _1mr(_1oj,_1ol,_);});},_1om=function(_1on,_1oo,_1op){return new F(function(){return _1o5(function(_1oc,_){return new F(function(){return _1nW(_1on,_1oo,_1oc,_);});},_1op);});},_1oq=function(_1or,_1os,_1ot,_1ou,_1ov){var _1ow=new T(function(){var _1ox=new T(function(){return B(_1om(_1ok,[0,_1oi,_1os],[1,[0,_1oe,_1or],[1,[0,_1od,_1ot],_9]]));});return !E(_1ou)?E(_1ox):B(_1om(_1ox,_1oh,_9));}),_1oy=E(_1ov);return _1oy[0]==0?E(_1ow):B(_1om(_1ow,[0,_1of,_1oy[1]],_9));},_1oz=new T(function(){return B(unCStr("href"));}),_1oA=[0,97],_1oB=[1,_1oA,_9],_1oC=function(_1oD,_){return new F(function(){return _1mr(_1oB,_1oD,_);});},_1oE=function(_1oF,_1oG){return function(_1oH,_){var _1oI=B(A(new T(function(){return B(_1om(_1oC,[0,_1oz,_1oF],_9));}),[_1oH,_])),_1oJ=_1oI,_1oK=B(A(_1oG,[_1oJ,_])),_1oL=_1oK;return _1oJ;};},_1oM=function(_1oN){return new F(function(){return _1oE(_1oN,function(_1oc,_){return new F(function(){return _56(_1oN,_1oc,_);});});});},_1oO=new T(function(){return B(unCStr("option"));}),_1oP=function(_1oQ,_){return new F(function(){return _1mr(_1oO,_1oQ,_);});},_1oR=new T(function(){return B(unCStr("selected"));}),_1oS=[0,_1oR,_9],_1oT=function(_1oU,_1oV,_1oW){var _1oX=new T(function(){return B(_1om(_1oP,[0,_1od,_1oU],_9));});if(!E(_1oW)){return function(_1oY,_){var _1oZ=B(A(_1oX,[_1oY,_])),_1p0=_1oZ,_1p1=B(A(_1oV,[_1p0,_])),_1p2=_1p1;return _1p0;};}else{return new F(function(){return _1om(function(_1p3,_){var _1p4=B(A(_1oX,[_1p3,_])),_1p5=_1p4,_1p6=B(A(_1oV,[_1p5,_])),_1p7=_1p6;return _1p5;},_1oS,_9);});}},_1p8=function(_1p9,_1pa){return new F(function(){return _1oT(_1p9,function(_1oc,_){return new F(function(){return _56(_1p9,_1oc,_);});},_1pa);});},_1pb=new T(function(){return B(unCStr("method"));}),_1pc=new T(function(){return B(unCStr("action"));}),_1pd=new T(function(){return B(unCStr("UTF-8"));}),_1pe=new T(function(){return B(unCStr("acceptCharset"));}),_1pf=[0,_1pe,_1pd],_1pg=new T(function(){return B(unCStr("form"));}),_1ph=function(_1pi,_){return new F(function(){return _1mr(_1pg,_1pi,_);});},_1pj=function(_1pk,_1pl,_1pm){return function(_1pn,_){var _1po=B(A(new T(function(){return B(_1om(_1ph,_1pf,[1,[0,_1pc,_1pk],[1,[0,_1pb,_1pl],_9]]));}),[_1pn,_])),_1pp=_1po,_1pq=B(A(_1pm,[_1pp,_])),_1pr=_1pq;return _1pp;};},_1ps=new T(function(){return B(unCStr("select"));}),_1pt=function(_1pu,_){return new F(function(){return _1mr(_1ps,_1pu,_);});},_1pv=function(_1pw,_1px){return function(_1py,_){var _1pz=B(A(new T(function(){return B(_1om(_1pt,[0,_1oe,_1pw],_9));}),[_1py,_])),_1pA=_1pz,_1pB=B(A(_1px,[_1pA,_])),_1pC=_1pB;return _1pA;};},_1pD=new T(function(){return B(unCStr("textarea"));}),_1pE=function(_1pF,_){return new F(function(){return _1mr(_1pD,_1pF,_);});},_1pG=function(_1pH,_1pI){return function(_1pJ,_){var _1pK=B(A(new T(function(){return B(_1om(_1pE,[0,_1oe,_1pH],_9));}),[_1pJ,_])),_1pL=_1pK,_1pM=B(_56(_1pI,_1pL,_)),_1pN=_1pM;return _1pL;};},_1pO=new T(function(){return B(unCStr("color:red"));}),_1pP=new T(function(){return B(unCStr("style"));}),_1pQ=[0,_1pP,_1pO],_1pR=[0,98],_1pS=[1,_1pR,_9],_1pT=function(_1pU){return new F(function(){return _1om(function(_1pV,_){var _1pW=B(_1mr(_1pS,_1pV,_)),_1pX=_1pW,_1pY=B(A(_1pU,[_1pX,_])),_1pZ=_1pY;return _1pX;},_1pQ,_9);});},_1q0=function(_1q1,_1q2,_){var _1q3=E(_1q1);if(!_1q3[0]){return _1q2;}else{var _1q4=B(A(_1q3[1],[_1q2,_])),_1q5=_1q4,_1q6=B(_1q0(_1q3[2],_1q2,_)),_1q7=_1q6;return _1q2;}},_1q8=function(_1q9,_1qa,_){return new F(function(){return _1q0(_1q9,_1qa,_);});},_1qb=function(_1qc,_1qd,_1qe,_){var _1qf=B(A(_1qc,[_1qe,_])),_1qg=_1qf,_1qh=B(A(_1qd,[_1qe,_])),_1qi=_1qh;return _1qe;},_1qj=[0,_5t,_1qb,_1q8],_1qk=[0,_1qj,_1nV,_56,_56,_1mx,_1pT,_1oE,_1oM,_1oq,_1pG,_1pv,_1oT,_1p8,_1pj,_1o5],_1ql=function(_1qm,_1qn,_){var _1qo=B(A(_1qn,[_])),_1qp=_1qo;return _1qm;},_1qq=function(_1qr,_1qs,_){var _1qt=B(A(_1qs,[_])),_1qu=_1qt;return new T(function(){return B(A(_1qr,[_1qu]));});},_1qv=[0,_1qq,_1ql],_1qw=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1qx=new T(function(){return B(unCStr("base"));}),_1qy=new T(function(){return B(unCStr("IOException"));}),_1qz=new T(function(){var _1qA=hs_wordToWord64(4053623282),_1qB=_1qA,_1qC=hs_wordToWord64(3693590983),_1qD=_1qC;return [0,_1qB,_1qD,[0,_1qB,_1qD,_1qx,_1qw,_1qy],_9];}),_1qE=function(_1qF){return E(_1qz);},_1qG=function(_1qH){var _1qI=E(_1qH);return new F(function(){return _2y(B(_2w(_1qI[1])),_1qE,_1qI[2]);});},_1qJ=new T(function(){return B(unCStr(": "));}),_1qK=[0,41],_1qL=new T(function(){return B(unCStr(" ("));}),_1qM=new T(function(){return B(unCStr("already exists"));}),_1qN=new T(function(){return B(unCStr("does not exist"));}),_1qO=new T(function(){return B(unCStr("protocol error"));}),_1qP=new T(function(){return B(unCStr("failed"));}),_1qQ=new T(function(){return B(unCStr("invalid argument"));}),_1qR=new T(function(){return B(unCStr("inappropriate type"));}),_1qS=new T(function(){return B(unCStr("hardware fault"));}),_1qT=new T(function(){return B(unCStr("unsupported operation"));}),_1qU=new T(function(){return B(unCStr("timeout"));}),_1qV=new T(function(){return B(unCStr("resource vanished"));}),_1qW=new T(function(){return B(unCStr("interrupted"));}),_1qX=new T(function(){return B(unCStr("resource busy"));}),_1qY=new T(function(){return B(unCStr("resource exhausted"));}),_1qZ=new T(function(){return B(unCStr("end of file"));}),_1r0=new T(function(){return B(unCStr("illegal operation"));}),_1r1=new T(function(){return B(unCStr("permission denied"));}),_1r2=new T(function(){return B(unCStr("user error"));}),_1r3=new T(function(){return B(unCStr("unsatisified constraints"));}),_1r4=new T(function(){return B(unCStr("system error"));}),_1r5=function(_1r6,_1r7){switch(E(_1r6)){case 0:return new F(function(){return _e(_1qM,_1r7);});break;case 1:return new F(function(){return _e(_1qN,_1r7);});break;case 2:return new F(function(){return _e(_1qX,_1r7);});break;case 3:return new F(function(){return _e(_1qY,_1r7);});break;case 4:return new F(function(){return _e(_1qZ,_1r7);});break;case 5:return new F(function(){return _e(_1r0,_1r7);});break;case 6:return new F(function(){return _e(_1r1,_1r7);});break;case 7:return new F(function(){return _e(_1r2,_1r7);});break;case 8:return new F(function(){return _e(_1r3,_1r7);});break;case 9:return new F(function(){return _e(_1r4,_1r7);});break;case 10:return new F(function(){return _e(_1qO,_1r7);});break;case 11:return new F(function(){return _e(_1qP,_1r7);});break;case 12:return new F(function(){return _e(_1qQ,_1r7);});break;case 13:return new F(function(){return _e(_1qR,_1r7);});break;case 14:return new F(function(){return _e(_1qS,_1r7);});break;case 15:return new F(function(){return _e(_1qT,_1r7);});break;case 16:return new F(function(){return _e(_1qU,_1r7);});break;case 17:return new F(function(){return _e(_1qV,_1r7);});break;default:return new F(function(){return _e(_1qW,_1r7);});}},_1r8=[0,125],_1r9=new T(function(){return B(unCStr("{handle: "));}),_1ra=function(_1rb,_1rc,_1rd,_1re,_1rf,_1rg){var _1rh=new T(function(){var _1ri=new T(function(){return B(_1r5(_1rc,new T(function(){var _1rj=E(_1re);return _1rj[0]==0?E(_1rg):B(_e(_1qL,new T(function(){return B(_e(_1rj,[1,_1qK,_1rg]));},1)));},1)));},1),_1rk=E(_1rd);return _1rk[0]==0?E(_1ri):B(_e(_1rk,new T(function(){return B(_e(_1qJ,_1ri));},1)));},1),_1rl=E(_1rf);if(!_1rl[0]){var _1rm=E(_1rb);if(!_1rm[0]){return E(_1rh);}else{var _1rn=E(_1rm[1]);return _1rn[0]==0?B(_e(_1r9,new T(function(){return B(_e(_1rn[1],[1,_1r8,new T(function(){return B(_e(_1qJ,_1rh));})]));},1))):B(_e(_1r9,new T(function(){return B(_e(_1rn[1],[1,_1r8,new T(function(){return B(_e(_1qJ,_1rh));})]));},1)));}}else{return new F(function(){return _e(_1rl[1],new T(function(){return B(_e(_1qJ,_1rh));},1));});}},_1ro=function(_1rp){var _1rq=E(_1rp);return new F(function(){return _1ra(_1rq[1],_1rq[2],_1rq[3],_1rq[4],_1rq[6],_9);});},_1rr=function(_1rs,_1rt){var _1ru=E(_1rs);return new F(function(){return _1ra(_1ru[1],_1ru[2],_1ru[3],_1ru[4],_1ru[6],_1rt);});},_1rv=function(_1rw,_1rx){return new F(function(){return _2T(_1rr,_1rw,_1rx);});},_1ry=function(_1rz,_1rA,_1rB){var _1rC=E(_1rA);return new F(function(){return _1ra(_1rC[1],_1rC[2],_1rC[3],_1rC[4],_1rC[6],_1rB);});},_1rD=[0,_1ry,_1ro,_1rv],_1rE=new T(function(){return [0,_1qE,_1rD,_1rF,_1qG];}),_1rF=function(_1rG){return [0,_1rE,_1rG];},_1rH=7,_1rI=function(_1rJ){return [0,_28,_1rH,_9,_1rJ,_28,_28];},_1rK=function(_1rL,_){return new F(function(){return die(new T(function(){return B(_1rF(new T(function(){return B(_1rI(_1rL));})));}));});},_1rM=function(_1rN,_){return new F(function(){return _1rK(_1rN,_);});},_1rO=function(_1rP,_){return new F(function(){return _1rM(_1rP,_);});},_1rQ=function(_1rR,_){return new F(function(){return _1rO(_1rR,_);});},_1rS=function(_1rT,_1rU,_){var _1rV=B(A(_1rT,[_])),_1rW=_1rV;return new F(function(){return A(_1rU,[_1rW,_]);});},_1rX=function(_1rY,_1rZ,_){var _1s0=B(A(_1rY,[_])),_1s1=_1s0;return new F(function(){return A(_1rZ,[_]);});},_1s2=[0,_1rS,_1rX,_5t,_1rQ],_1s3=[0,_1s2,_5q],_1s4=function(_1s5){return E(E(_1s5)[1]);},_1s6=function(_1s7){return E(E(_1s7)[2]);},_1s8=function(_1s9,_1sa){var _1sb=new T(function(){return B(_1s4(_1s9));});return function(_1sc){return new F(function(){return A(new T(function(){return B(_Ox(_1sb));}),[new T(function(){return B(A(_1s6,[_1s9,_1sa]));}),function(_1sd){return new F(function(){return A(new T(function(){return B(_iK(_1sb));}),[[0,_1sd,_1sc]]);});}]);});};},_1se=function(_1sf,_1sg){return [0,_1sf,function(_1sh){return new F(function(){return _1s8(_1sg,_1sh);});}];},_1si=function(_1sj,_1sk,_1sl,_1sm){return new F(function(){return A(_Ox,[_1sj,new T(function(){return B(A(_1sk,[_1sm]));}),function(_1sn){return new F(function(){return A(_1sl,[new T(function(){return E(E(_1sn)[1]);}),new T(function(){return E(E(_1sn)[2]);})]);});}]);});},_1so=function(_1sp,_1sq,_1sr,_1ss){return new F(function(){return A(_Ox,[_1sp,new T(function(){return B(A(_1sq,[_1ss]));}),function(_1st){return new F(function(){return A(_1sr,[new T(function(){return E(E(_1st)[2]);})]);});}]);});},_1su=function(_1sv,_1sw,_1sx,_1sy){return new F(function(){return _1so(_1sv,_1sw,_1sx,_1sy);});},_1sz=function(_1sA){return E(E(_1sA)[4]);},_1sB=function(_1sC,_1sD){return function(_1sE){return E(new T(function(){return B(A(_1sz,[_1sC,_1sD]));}));};},_1sF=function(_1sG){return [0,function(_1sw,_1sx,_1sy){return new F(function(){return _1si(_1sG,_1sw,_1sx,_1sy);});},function(_1sw,_1sx,_1sy){return new F(function(){return _1su(_1sG,_1sw,_1sx,_1sy);});},function(_1sH,_1sI){return new F(function(){return A(new T(function(){return B(_iK(_1sG));}),[[0,_1sH,_1sI]]);});},function(_1sy){return new F(function(){return _1sB(_1sG,_1sy);});}];},_1sJ=function(_1sK,_1sL,_1sM){return new F(function(){return A(_iK,[_1sK,[0,_1sL,_1sM]]);});},_1sN=[0,10],_1sO=function(_1sP,_1sQ){var _1sR=E(_1sQ);if(!_1sR[0]){return E(_5q);}else{var _1sS=_1sR[1],_1sT=E(_1sR[2]);if(!_1sT[0]){var _1sU=E(_1sS);return new F(function(){return _1sV(_1sN,_1sU[3],_1sU[4]);});}else{return function(_1sW){return new F(function(){return A(new T(function(){var _1sX=E(_1sS);return B(_1sV(_1sN,_1sX[3],_1sX[4]));}),[new T(function(){return B(A(_1sP,[new T(function(){return B(A(new T(function(){return B(_1sO(_1sP,_1sT));}),[_1sW]));})]));})]);});};}}},_1sY=new T(function(){return B(unCStr("(->)"));}),_1sZ=new T(function(){return B(unCStr("GHC.Prim"));}),_1t0=new T(function(){var _1t1=hs_wordToWord64(4173248105),_1t2=_1t1,_1t3=hs_wordToWord64(4270398258),_1t4=_1t3;return [0,_1t2,_1t4,[0,_1t2,_1t4,_1mH,_1sZ,_1sY],_9];}),_1t5=new T(function(){return E(E(_1t0)[3]);}),_1t6=new T(function(){return B(unCStr("GHC.Types"));}),_1t7=new T(function(){return B(unCStr("[]"));}),_1t8=new T(function(){var _1t9=hs_wordToWord64(4033920485),_1ta=_1t9,_1tb=hs_wordToWord64(786266835),_1tc=_1tb;return [0,_1ta,_1tc,[0,_1ta,_1tc,_1mH,_1t6,_1t7],_9];}),_1td=[1,_1mI,_9],_1te=function(_1tf){var _1tg=E(_1tf);if(!_1tg[0]){return [0];}else{var _1th=E(_1tg[1]);return [1,[0,_1th[1],_1th[2]],new T(function(){return B(_1te(_1tg[2]));})];}},_1ti=new T(function(){var _1tj=E(_1t8),_1tk=E(_1tj[3]),_1tl=B(_e(_1tj[4],_1td));if(!_1tl[0]){var _1tm=E(_1tk);}else{var _1tn=B(_1nc(new T(function(){return B(_7r(B(_7X(_1nF,[1,[0,_1tk[1],_1tk[2]],new T(function(){return B(_1te(_1tl));})]))));},1))),_1tm=E(_1tk);}var _1to=_1tm,_1tp=_1to;return _1tp;}),_1tq=[0,8],_1tr=[0,32],_1ts=function(_1tt){return [1,_1tr,_1tt];},_1tu=new T(function(){return B(unCStr(" -> "));}),_1tv=[0,9],_1tw=[0,93],_1tx=[0,91],_1ty=[0,41],_1tz=[0,44],_1tA=function(_1tt){return [1,_1tz,_1tt];},_1tB=[0,40],_1tC=[0,0],_1sV=function(_1tD,_1tE,_1tF){var _1tG=E(_1tF);if(!_1tG[0]){return function(_1tH){return new F(function(){return _e(E(_1tE)[5],_1tH);});};}else{var _1tI=_1tG[1],_1tJ=function(_1tK){var _1tL=E(_1tE)[5],_1tM=function(_1tN){var _1tO=new T(function(){return B(_1sO(_1ts,_1tG));});return E(_1tD)[1]<=9?function(_1tP){return new F(function(){return _e(_1tL,[1,_1tr,new T(function(){return B(A(_1tO,[_1tP]));})]);});}:function(_1tQ){return [1,_E,new T(function(){return B(_e(_1tL,[1,_1tr,new T(function(){return B(A(_1tO,[[1,_D,_1tQ]]));})]));})];};},_1tR=E(_1tL);if(!_1tR[0]){return new F(function(){return _1tM(_);});}else{if(E(E(_1tR[1])[1])==40){var _1tS=E(_1tR[2]);if(!_1tS[0]){return new F(function(){return _1tM(_);});}else{if(E(E(_1tS[1])[1])==44){return function(_1tT){return [1,_1tB,new T(function(){return B(A(new T(function(){return B(_1sO(_1tA,_1tG));}),[[1,_1ty,_1tT]]));})];};}else{return new F(function(){return _1tM(_);});}}}else{return new F(function(){return _1tM(_);});}}},_1tU=E(_1tG[2]);if(!_1tU[0]){var _1tV=E(_1tE),_1tW=E(_1ti),_1tX=hs_eqWord64(_1tV[1],_1tW[1]),_1tY=_1tX;if(!E(_1tY)){return new F(function(){return _1tJ(_);});}else{var _1tZ=hs_eqWord64(_1tV[2],_1tW[2]),_1u0=_1tZ;if(!E(_1u0)){return new F(function(){return _1tJ(_);});}else{return function(_1u1){return [1,_1tx,new T(function(){return B(A(new T(function(){var _1u2=E(_1tI);return B(_1sV(_1tC,_1u2[3],_1u2[4]));}),[[1,_1tw,_1u1]]));})];};}}}else{if(!E(_1tU[2])[0]){var _1u3=E(_1tE),_1u4=E(_1t5),_1u5=hs_eqWord64(_1u3[1],_1u4[1]),_1u6=_1u5;if(!E(_1u6)){return new F(function(){return _1tJ(_);});}else{var _1u7=hs_eqWord64(_1u3[2],_1u4[2]),_1u8=_1u7;if(!E(_1u8)){return new F(function(){return _1tJ(_);});}else{var _1u9=new T(function(){var _1ua=E(_1tU[1]);return B(_1sV(_1tq,_1ua[3],_1ua[4]));}),_1ub=new T(function(){var _1uc=E(_1tI);return B(_1sV(_1tv,_1uc[3],_1uc[4]));});return E(_1tD)[1]<=8?function(_1ud){return new F(function(){return A(_1ub,[new T(function(){return B(_e(_1tu,new T(function(){return B(A(_1u9,[_1ud]));},1)));})]);});}:function(_1ue){return [1,_E,new T(function(){return B(A(_1ub,[new T(function(){return B(_e(_1tu,new T(function(){return B(A(_1u9,[[1,_D,_1ue]]));},1)));})]));})];};}}}else{return new F(function(){return _1tJ(_);});}}}},_1uf=function(_1ug,_1uh){return new F(function(){return A(_1ug,[function(_){return new F(function(){return jsFind(toJSStr(E(_1uh)));});}]);});},_1ui=[0],_1uj=function(_1uk){return E(E(_1uk)[3]);},_1ul=new T(function(){return [0,"value"];}),_1um=function(_1un){return E(E(_1un)[6]);},_1uo=function(_1up){return E(E(_1up)[1]);},_1uq=new T(function(){return B(unCStr("Char"));}),_1ur=new T(function(){var _1us=hs_wordToWord64(3763641161),_1ut=_1us,_1uu=hs_wordToWord64(1343745632),_1uv=_1uu;return [0,_1ut,_1uv,[0,_1ut,_1uv,_1mH,_1t6,_1uq],_9];}),_1uw=function(_1ux){return E(_1ur);},_1uy=function(_1uz){return E(_1t8);},_1uA=new T(function(){return B(_1nI(_1uy,_1uw));}),_1uB=new T(function(){return B(A(_1uA,[_]));}),_1uC=function(_1uD,_1uE,_1uF,_1uG,_1uH,_1uI,_1uJ,_1uK,_1uL){var _1uM=new T(function(){return B(A(_1uG,[_1ui]));});return new F(function(){return A(_1uE,[new T(function(){return B(_1uf(E(_1uD)[2],_1uL));}),function(_1uN){var _1uO=E(_1uN);return _1uO[0]==0?E(_1uM):B(A(_1uE,[new T(function(){return B(A(E(_1uD)[2],[function(_){var _1uP=jsGet(E(_1uO[1])[1],E(_1ul)[1]),_1uQ=_1uP;return [1,new T(function(){return fromJSStr(_1uQ);})];}]));}),function(_1uR){var _1uS=E(_1uR);if(!_1uS[0]){return E(_1uM);}else{var _1uT=_1uS[1];if(!E(new T(function(){var _1uU=B(A(_1uI,[_])),_1uV=E(_1uB),_1uW=hs_eqWord64(_1uU[1],_1uV[1]),_1uX=_1uW;if(!E(_1uX)){var _1uY=false;}else{var _1uZ=hs_eqWord64(_1uU[2],_1uV[2]),_1v0=_1uZ,_1uY=E(_1v0)==0?false:true;}var _1v1=_1uY,_1v2=_1v1;return _1v2;}))){var _1v3=function(_1v4){return new F(function(){return A(_1uG,[[1,_1uT,new T(function(){return B(A(new T(function(){return B(_1um(_1uK));}),[new T(function(){return B(A(new T(function(){return B(_1uj(_1uK));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1uT,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1v5=B(A(_1uI,[_]));return B(A(_1sV,[_1tC,_1v5[3],_1v5[4],_9]));})));})));})));})]));})]));})]]);});},_1v6=B(A(new T(function(){return B(A(_1uo,[_1uJ,_1R]));}),[_1uT]));if(!_1v6[0]){return new F(function(){return _1v3(_);});}else{var _1v7=E(_1v6[1]);return E(_1v7[2])[0]==0?E(_1v6[2])[0]==0?B(A(_1uG,[[2,_1v7[1]]])):B(_1v3(_)):B(_1v3(_));}}else{return new F(function(){return A(_1uG,[[2,_1uT]]);});}}}]));}]);});},_1v8=function(_1v9){return E(E(_1v9)[10]);},_1va=function(_1vb){return new F(function(){return _kY([1,function(_1vc){return new F(function(){return A(_sE,[_1vc,function(_1vd){return E(new T(function(){return B(_tU(function(_1ve){var _1vf=E(_1ve);return _1vf[0]==0?B(A(_1vb,[_1vf[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_ug(_1vg,_1vb))];}));});},_1vg=function(_1vh,_1vi){return new F(function(){return _1va(_1vi);});},_1vj=[0,91],_1vk=[1,_1vj,_9],_1vl=function(_1vm,_1vn){var _1vo=function(_1vp,_1vq){return [1,function(_1vr){return new F(function(){return A(_sE,[_1vr,function(_1vs){return E(new T(function(){return B(_tU(function(_1vt){var _1vu=E(_1vt);if(_1vu[0]==2){var _1vv=E(_1vu[1]);if(!_1vv[0]){return [2];}else{var _1vw=_1vv[2];switch(E(E(_1vv[1])[1])){case 44:return E(_1vw)[0]==0?!E(_1vp)?[2]:E(new T(function(){return B(A(_1vm,[_uf,function(_1vx){return new F(function(){return _1vo(_ob,function(_1vy){return new F(function(){return A(_1vq,[[1,_1vx,_1vy]]);});});});}]));})):[2];case 93:return E(_1vw)[0]==0?E(new T(function(){return B(A(_1vq,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1vz=function(_1vA){return new F(function(){return _kY([1,function(_1vB){return new F(function(){return A(_sE,[_1vB,function(_1vC){return E(new T(function(){return B(_tU(function(_1vD){var _1vE=E(_1vD);return _1vE[0]==2?!B(_lv(_1vE[1],_1vk))?[2]:E(new T(function(){return B(_kY(B(_1vo(_1S,_1vA)),new T(function(){return B(A(_1vm,[_uf,function(_1vF){return new F(function(){return _1vo(_ob,function(_1vG){return new F(function(){return A(_1vA,[[1,_1vF,_1vG]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_ug(function(_1vH,_1vI){return new F(function(){return _1vz(_1vI);});},_1vA))];}));});};return new F(function(){return _1vz(_1vn);});},_1vJ=function(_1vK){return new F(function(){return _kY(B(_kY([1,function(_1vL){return new F(function(){return A(_sE,[_1vL,function(_1vM){return E(new T(function(){return B(_tU(function(_1vN){var _1vO=E(_1vN);return _1vO[0]==1?B(A(_1vK,[_1vO[1]])):[2];}));}));}]);});}],new T(function(){return B(_1vl(_1vg,_1vK));}))),new T(function(){return [1,B(_ug(_1vP,_1vK))];}));});},_1vP=function(_1vQ,_1vR){return new F(function(){return _1vJ(_1vR);});},_1vS=new T(function(){return B(_1vJ(_lM));}),_1vT=function(_1vU){return new F(function(){return _kO(_1vS,_1vU);});},_1vV=new T(function(){return B(_1va(_lM));}),_1vW=function(_1vU){return new F(function(){return _kO(_1vV,_1vU);});},_1vX=function(_1vY){return E(_1vW);},_1vZ=[0,_1vX,_1vT,_1vg,_1vP],_1w0=function(_1w1){return E(E(_1w1)[4]);},_1w2=function(_1w3,_1w4,_1w5){return new F(function(){return _1vl(new T(function(){return B(_1w0(_1w3));}),_1w5);});},_1w6=function(_1w7){return function(_mc){return new F(function(){return _kO(new T(function(){return B(_1vl(new T(function(){return B(_1w0(_1w7));}),_lM));}),_mc);});};},_1w8=function(_1w9,_1wa){return function(_mc){return new F(function(){return _kO(new T(function(){return B(A(_1w0,[_1w9,_1wa,_lM]));}),_mc);});};},_1wb=function(_1wc){return [0,function(_1vU){return new F(function(){return _1w8(_1wc,_1vU);});},new T(function(){return B(_1w6(_1wc));}),new T(function(){return B(_1w0(_1wc));}),function(_1wd,_1vU){return new F(function(){return _1w2(_1wc,_1wd,_1vU);});}];},_1we=new T(function(){return B(_1wb(_1vZ));}),_1wf=function(_1wg,_1wh,_1wi){var _1wj=new T(function(){return B(_1v8(_1wg));}),_1wk=new T(function(){return B(_1s4(_1wi));}),_1wl=new T(function(){return B(_iK(_1wk));});return function(_1wm,_1wn){return new F(function(){return A(new T(function(){return B(_Ox(_1wk));}),[new T(function(){return B(A(new T(function(){return B(_Ox(_1wk));}),[new T(function(){return B(A(new T(function(){return B(_iK(_1wk));}),[[0,_1wn,_1wn]]));}),function(_1wo){var _1wp=new T(function(){return E(E(_1wo)[1]);}),_1wq=new T(function(){return E(E(_1wp)[2]);});return new F(function(){return A(new T(function(){return B(_Ox(_1wk));}),[new T(function(){return B(A(new T(function(){return B(_iK(_1wk));}),[[0,_5c,new T(function(){var _1wr=E(_1wp);return [0,_1wr[1],new T(function(){return [0,E(_1wq)[1]+1|0];}),_1wr[3],_1wr[4],_1wr[5],_1wr[6],_1wr[7]];})]]));}),function(_1ws){return new F(function(){return A(new T(function(){return B(_iK(_1wk));}),[[0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_1wq)[1],_9)),new T(function(){return E(E(_1wp)[1]);},1)));})],new T(function(){return E(E(_1ws)[2]);})]]);});}]);});}]));}),function(_1wt){var _1wu=new T(function(){return E(E(_1wt)[1]);});return new F(function(){return A(new T(function(){return B(_Ox(_1wk));}),[new T(function(){return B(A(_1uC,[new T(function(){return B(_1se(new T(function(){return B(_1sF(_1wk));}),_1wi));}),function(_1wv,_1oc,_1ww){return new F(function(){return _1si(_1wk,_1wv,_1oc,_1ww);});},function(_1wv,_1oc,_1ww){return new F(function(){return _1su(_1wk,_1wv,_1oc,_1ww);});},function(_1oc,_1ww){return new F(function(){return _1sJ(_1wk,_1oc,_1ww);});},function(_1ww){return new F(function(){return _1sB(_1wk,_1ww);});},_1uA,_1we,_1wg,_1wu,new T(function(){return E(E(_1wt)[2]);})]));}),function(_1wx){var _1wy=E(_1wx),_1wz=_1wy[2],_1wA=E(_1wy[1]);switch(_1wA[0]){case 0:return new F(function(){return A(_1wl,[[0,[0,new T(function(){return B(A(_1wj,[_1wu,_1wm]));}),_28],_1wz]]);});break;case 1:return new F(function(){return A(_1wl,[[0,[0,new T(function(){return B(A(_1wj,[_1wu,_1wA[1]]));}),_28],_1wz]]);});break;default:var _1wB=_1wA[1];return new F(function(){return A(_1wl,[[0,[0,new T(function(){return B(A(_1wj,[_1wu,_1wB]));}),[1,_1wB]],_1wz]]);});}}]);});}]);});};},_1wC=new T(function(){return B(_1wf(_1qk,_1qv,_1s3));}),_1wD=new T(function(){return B(_CX("w_s6k4{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv a5rp} [tv]"));}),_1wE=new T(function(){return B(_CX("w_s6k5{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv a5ro} [tv]"));}),_1wF=function(_1wG){return E(E(_1wG)[2]);},_1wH=function(_1wI){return E(E(_1wI)[1]);},_1wJ=function(_1wK,_1wL,_1wM){return function(_1wN,_){var _1wO=B(A(_1wL,[_1wN,_])),_1wP=_1wO,_1wQ=E(_1wP),_1wR=E(_1wQ[1]),_1wS=new T(function(){return B(A(new T(function(){return B(_1wF(_1wK));}),[_1wM,function(_){var _1wT=E(E(_1wN)[4]),_1wU=B(A(_1wT[1],[_])),_1wV=_1wU,_1wW=E(_1wV);if(!_1wW[0]){return _5c;}else{var _1wX=B(A(_1wT[2],[_1wW[1],_])),_1wY=_1wX;return _5c;}}]));});return [0,[0,function(_1wZ,_){var _1x0=B(A(_1wR[1],[_1wZ,_])),_1x1=_1x0,_1x2=E(_1x1),_1x3=E(_1wS),_1x4=jsSetCB(_1x2[1],toJSStr(E(new T(function(){return B(A(_1wH,[_1wK,_1wM]));}))),_1wS),_1x5=_1x4;return _1x2;},_1wR[2]],_1wQ[2]];};},_1x6=function(_1x7,_1x8,_1x9,_1xa,_1xb,_1xc,_1xd,_1xe,_1xf,_1xg,_1xh){return function(_1xi,_1xj){return function(_mc,_18e){return new F(function(){return _65(function(_1xk,_){var _1xl=B(A(new T(function(){return B(_1wJ(_55,new T(function(){return B(_1wJ(_55,new T(function(){return B(A(_1wC,[_1xj]));}),_1p));}),_1o));}),[_1xk,_])),_1xm=_1xl,_1xn=E(_1xm),_1xo=E(_1xn[1]);return [0,[0,function(_1xp,_){var _1xq=B(A(_1xo[1],[_1xp,_])),_1xr=_1xq,_1xs=B(A(_5d,[_5q,_1xr,_bP,_cf,_])),_1xt=_1xs;return _1xr;},_1xo[2]],_1xn[2]];},function(_1xu){var _1xv=new T(function(){var _1xw=B(_E9(_D1,_Ev,[0,new T(function(){return B(_e(_1xu,_1mq));}),E(_CU),E(_5c)]));if(!_1xw[0]){var _1xx=E(_1xw[1]);if(!_1xx[0]){var _1xy=E(E(_1xx[1])[1]);}else{var _1xy=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1xx[1]));})));})],_9],_9];}var _1xz=_1xy;}else{var _1xA=E(_1xw[1]);if(!_1xA[0]){var _1xB=E(E(_1xA[1])[1]);}else{var _1xB=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1xA[1]));})));})],_9],_9];}var _1xz=_1xB;}return _1xz;});return function(_mc,_18e){return new F(function(){return _65(_bA,function(_1xC,_1xD,_){return new F(function(){return _65(_bG,function(_1xE,_1xF,_){return new F(function(){return _65(_bL,function(_1xG,_1xH,_){return new F(function(){return _65(function(_1xI,_){return [0,[0,function(_1xJ,_){var _1xK=B(_bX(_56,_9,_1xJ,_)),_1xL=_1xK,_1xM=B(A(_5d,[_5q,_1xL,_5p,_1xC,_])),_1xN=_1xM,_1xO=B(A(_5d,[_5q,_1xL,_bP,_bM,_])),_1xP=_1xO;return _1xL;},_bS],_1xI];},function(_1xQ,_1xR,_){return new F(function(){return _65(function(_1xS,_){return [0,[0,function(_1xT,_){var _1xU=B(_5T(_63,new T(function(){return B(_1mg(_1xv));}),_1xT,_)),_1xV=_1xU,_1xW=B(A(_5d,[_5q,_1xV,_5p,_1xE,_])),_1xX=_1xW,_1xY=B(A(_5d,[_5q,_1xV,_bP,_bN,_])),_1xZ=_1xY;return _1xV;},_bS],_1xS];},function(_1y0){return E(new T(function(){var _1y1=E(new T(function(){var _1y2=B(_1k4(_1xv,new T(function(){return E(E(_1xi)[1]);})));return _1y2[0]==0?[0,_1y2[1]]:[1,new T(function(){return B(_1h5(_1x7,_1x8,_1x9,_1xa,_1xb,_1xc,_1xd,_1xe,_1xf,_1wD,_1wE,_1xg,_1xh,new T(function(){return E(E(_1xi)[2]);}),_1y2[1]));})];}));if(!_1y1[0]){var _1y3=function(_1y4,_){return [0,[0,function(_1y5,_){var _1y6=B(_bX(_63,function(_bB,_){return new F(function(){return _c7(new T(function(){return B(_db(_1y1[1],_9));}),_bB,_);});},_1y5,_)),_1y7=_1y6,_1y8=B(A(_5d,[_5q,_1y7,_5p,_1xG,_])),_1y9=_1y8,_1ya=B(A(_5d,[_5q,_1y7,_bP,_bO,_])),_1yb=_1ya;return _1y7;},_bS],_1y4];};}else{var _1yc=E(_1y1[1]);if(!_1yc[0]){var _1yd=function(_bB,_){return new F(function(){return _ch(_1xC,_bt,_bU,_bB,_);});};}else{var _1yd=function(_mc,_18e){return new F(function(){return _ch(_1xC,_bt,function(_1ye,_){return [0,[0,function(_bB,_){return new F(function(){return _5T(_56,new T(function(){var _1yf=E(_1yc[1]);return B(_bo(new T(function(){return B(_b9(_1xd,_1xc,_1xb,_1xa,_1x9,_1x7,_1x8));}),_1yf[1],_1yf[2]));}),_bB,_);});},_bS],_1ye];},_mc,_18e);});};}var _1y3=_1yd;}return _1y3;}));},_1xR,_);});},_1xH,_);});},_1xF,_);});},_1xD,_);});},_mc,_18e);});};},_mc,_18e);});};};},_1yg=function(_1yh,_1yi,_1yj,_1yk){return new F(function(){return A(_1yh,[function(_){var _1yl=jsSet(E(_1yi)[1],toJSStr(E(_1yj)),toJSStr(E(_1yk)));return _5c;}]);});},_1ym=new T(function(){return B(unCStr("innerHTML"));}),_1yn=new T(function(){return B(unCStr("textContent"));}),_1yo=function(_1yp,_1yq,_1yr,_1ys,_1yt,_1yu,_1yv,_1yw,_1yx,_1yy,_1yz,_1yA,_1yB,_){var _1yC=B(_1j(_1yB,_1yn,_)),_1yD=_1yC,_1yE=[0,_1yB],_1yF=B(A(_1yg,[_5q,_1yE,_1ym,_9,_])),_1yG=_1yF,_1yH=E(_2l)[1],_1yI=takeMVar(_1yH),_1yJ=_1yI,_1yK=B(A(_1x6,[_1yp,_1yq,_1yr,_1ys,_1yt,_1yu,_1yv,_1yw,_1yx,_1yy,_1yz,_1yA,_1yD,_1yJ,_])),_1yL=_1yK,_1yM=E(_1yL),_1yN=E(_1yM[1]),_=putMVar(_1yH,_1yM[2]),_1yO=B(A(_1yN[1],[_1yE,_])),_1yP=_1yO;return _1yN[2];},_1yQ=function(_){var _1yR=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1yS=_1yR;return _5c;},_1yT=new T(function(){return B(unCStr("proofbox"));}),_1yU=function(_1yV,_1yW,_1yX,_1yY,_1yZ,_1z0,_1z1,_1z2,_1z3,_1z4,_1z5,_1z6,_){var _1z7=jsElemsByClassName(toJSStr(E(_1yT))),_1z8=_1z7,_1z9=B((function(_1za,_){while(1){var _1zb=E(_1za);if(!_1zb[0]){return _5c;}else{var _1zc=B(_1yo(_1yV,_1yW,_1yX,_1yY,_1yZ,_1z0,_1z1,_1z2,_1z3,_1z4,_1z5,_1z6,E(_1zb[1])[1],_)),_1zd=_1zc;_1za=_1zb[2];continue;}}})(_1z8,_)),_1ze=_1z9,_1zf=jsSetTimeout(60,_1yQ);return _5c;},_1zg=new T(function(){return B(unCStr("ADD"));}),_1zh=new T(function(){return B(unCStr("ADJ"));}),_1zi=[0,1],_1zj=[1,_1zi],_1zk=[1,_1zj],_1zl=[0,_1zi],_1zm=[1,_1zl],_1zn=new T(function(){return B(unCStr("DN"));}),_1zo=new T(function(){return B(_lv(_9,_1zn));}),_1zp=new T(function(){return B(unCStr("MTP"));}),_1zq=new T(function(){return B(unCStr("MP"));}),_1zr=new T(function(){return B(unCStr("ID"));}),_1zs=new T(function(){return B(unCStr("CD"));}),_1zt=[0,2],_1zu=[1,_1zt],_1zv=[1,_1zu],_1zw=[0,_1zt],_1zx=[1,_1zw],_1zy=function(_1zz){if(!B(_lv(_1zz,_1zg))){if(!B(_lv(_1zz,_1zh))){if(!B(_lv(_1zz,_1zs))){if(!B(_lv(_1zz,_1zr))){if(!B(_lv(_1zz,_1zq))){if(!B(_lv(_1zz,_1zp))){var _1zA=E(_1zz);return _1zA[0]==0?!E(_1zo)?[0]:E(_1zm):E(E(_1zA[1])[1])==83?E(_1zA[2])[0]==0?E(_1zm):!B(_lv(_1zA,_1zn))?[0]:E(_1zm):!B(_lv(_1zA,_1zn))?[0]:E(_1zm);}else{return E(_1zx);}}else{return E(_1zx);}}else{return E(_1zv);}}else{return E(_1zk);}}else{return E(_1zx);}}else{return E(_1zm);}},_1zB=function(_1zC){return E(E(_1zC)[2]);},_1zD=function(_1zE,_1zF,_1zG){while(1){var _1zH=E(_1zF);if(!_1zH[0]){return E(_1zG)[0]==0?1:0;}else{var _1zI=E(_1zG);if(!_1zI[0]){return 2;}else{var _1zJ=B(A(_1zB,[_1zE,_1zH[1],_1zI[1]]));if(_1zJ==1){_1zF=_1zH[2];_1zG=_1zI[2];continue;}else{return E(_1zJ);}}}}},_1zK=function(_1zL){return E(E(_1zL)[3]);},_1zM=function(_1zN,_1zO,_1zP,_1zQ,_1zR){switch(B(_1zD(_1zN,_1zO,_1zQ))){case 0:return true;case 1:return new F(function(){return A(_1zK,[_1zN,_1zP,_1zR]);});break;default:return false;}},_1zS=function(_1zT,_1zU,_1zV,_1zW){var _1zX=E(_1zV),_1zY=E(_1zW);return new F(function(){return _1zM(_1zU,_1zX[1],_1zX[2],_1zY[1],_1zY[2]);});},_1zZ=function(_1A0){return E(E(_1A0)[6]);},_1A1=function(_1A2,_1A3,_1A4,_1A5,_1A6){switch(B(_1zD(_1A2,_1A3,_1A5))){case 0:return true;case 1:return new F(function(){return A(_1zZ,[_1A2,_1A4,_1A6]);});break;default:return false;}},_1A7=function(_1A8,_1A9,_1Aa,_1Ab){var _1Ac=E(_1Aa),_1Ad=E(_1Ab);return new F(function(){return _1A1(_1A9,_1Ac[1],_1Ac[2],_1Ad[1],_1Ad[2]);});},_1Ae=function(_1Af){return E(E(_1Af)[5]);},_1Ag=function(_1Ah,_1Ai,_1Aj,_1Ak,_1Al){switch(B(_1zD(_1Ah,_1Ai,_1Ak))){case 0:return false;case 1:return new F(function(){return A(_1Ae,[_1Ah,_1Aj,_1Al]);});break;default:return true;}},_1Am=function(_1An,_1Ao,_1Ap,_1Aq){var _1Ar=E(_1Ap),_1As=E(_1Aq);return new F(function(){return _1Ag(_1Ao,_1Ar[1],_1Ar[2],_1As[1],_1As[2]);});},_1At=function(_1Au){return E(E(_1Au)[4]);},_1Av=function(_1Aw,_1Ax,_1Ay,_1Az,_1AA){switch(B(_1zD(_1Aw,_1Ax,_1Az))){case 0:return false;case 1:return new F(function(){return A(_1At,[_1Aw,_1Ay,_1AA]);});break;default:return true;}},_1AB=function(_1AC,_1AD,_1AE,_1AF){var _1AG=E(_1AE),_1AH=E(_1AF);return new F(function(){return _1Av(_1AD,_1AG[1],_1AG[2],_1AH[1],_1AH[2]);});},_1AI=function(_1AJ,_1AK,_1AL,_1AM,_1AN){switch(B(_1zD(_1AJ,_1AK,_1AM))){case 0:return 0;case 1:return new F(function(){return A(_1zB,[_1AJ,_1AL,_1AN]);});break;default:return 2;}},_1AO=function(_1AP,_1AQ,_1AR,_1AS){var _1AT=E(_1AR),_1AU=E(_1AS);return new F(function(){return _1AI(_1AQ,_1AT[1],_1AT[2],_1AU[1],_1AU[2]);});},_1AV=function(_1AW,_1AX,_1AY,_1AZ){var _1B0=E(_1AY),_1B1=_1B0[1],_1B2=_1B0[2],_1B3=E(_1AZ),_1B4=_1B3[1],_1B5=_1B3[2];switch(B(_1zD(_1AX,_1B1,_1B4))){case 0:return [0,_1B4,_1B5];case 1:return !B(A(_1zZ,[_1AX,_1B2,_1B5]))?[0,_1B1,_1B2]:[0,_1B4,_1B5];default:return [0,_1B1,_1B2];}},_1B6=function(_1B7,_1B8,_1B9,_1Ba){var _1Bb=E(_1B9),_1Bc=_1Bb[1],_1Bd=_1Bb[2],_1Be=E(_1Ba),_1Bf=_1Be[1],_1Bg=_1Be[2];switch(B(_1zD(_1B8,_1Bc,_1Bf))){case 0:return [0,_1Bc,_1Bd];case 1:return !B(A(_1zZ,[_1B8,_1Bd,_1Bg]))?[0,_1Bf,_1Bg]:[0,_1Bc,_1Bd];default:return [0,_1Bf,_1Bg];}},_1Bh=function(_1Bi,_1Bj){return [0,_1Bi,function(_Yn,_Yo){return new F(function(){return _1AO(_1Bi,_1Bj,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1zS(_1Bi,_1Bj,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1AB(_1Bi,_1Bj,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Am(_1Bi,_1Bj,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1A7(_1Bi,_1Bj,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1AV(_1Bi,_1Bj,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1B6(_1Bi,_1Bj,_Yn,_Yo);});}];},_1Bk=function(_1Bl,_1Bm,_1Bn,_1Bo){return !B(A(_1Bl,[_1Bn,_1Bo]))?B(_cO(B(A(_1Bm,[_1Bn,_15i])),B(A(_1Bm,[_1Bo,_15i]))))==2?false:true:false;},_1Bp=function(_1Bq,_1Br,_1Bs,_1Bt){return new F(function(){return _1Bk(E(_1Bq)[1],_1Br,_1Bs,_1Bt);});},_1Bu=function(_1Bv,_1Bw,_1Bx,_1By){return B(_cO(B(A(_1Bw,[_1Bx,_15i])),B(A(_1Bw,[_1By,_15i]))))==2?false:true;},_1Bz=function(_1BA,_1BB,_1BC,_1BD){return !B(A(_1BA,[_1BC,_1BD]))?B(_cO(B(A(_1BB,[_1BC,_15i])),B(A(_1BB,[_1BD,_15i]))))==2?true:false:false;},_1BE=function(_1BF,_1BG,_1BH,_1BI){return new F(function(){return _1Bz(E(_1BF)[1],_1BG,_1BH,_1BI);});},_1BJ=function(_1BK,_1BL,_1BM,_1BN){return !B(A(_1BK,[_1BM,_1BN]))?B(_cO(B(A(_1BL,[_1BM,_15i])),B(A(_1BL,[_1BN,_15i]))))==2?true:false:true;},_1BO=function(_1BP,_1BQ,_1BR,_1BS){return new F(function(){return _1BJ(E(_1BP)[1],_1BQ,_1BR,_1BS);});},_1BT=function(_1BU,_1BV,_1BW,_1BX){return !B(A(_1BU,[_1BW,_1BX]))?B(_cO(B(A(_1BV,[_1BW,_15i])),B(A(_1BV,[_1BX,_15i]))))==2?2:0:1;},_1BY=function(_1BZ,_1C0,_1C1,_1C2){return new F(function(){return _1BT(E(_1BZ)[1],_1C0,_1C1,_1C2);});},_1C3=function(_1C4,_1C5,_1C6,_1C7){return B(_cO(B(A(_1C5,[_1C6,_15i])),B(A(_1C5,[_1C7,_15i]))))==2?E(_1C6):E(_1C7);},_1C8=function(_1C9,_1Ca,_1Cb,_1Cc){return B(_cO(B(A(_1Ca,[_1Cb,_15i])),B(A(_1Ca,[_1Cc,_15i]))))==2?E(_1Cc):E(_1Cb);},_1Cd=function(_1Ce,_1Cf){return [0,_1Ce,function(_bi,_bj){return new F(function(){return _1BY(_1Ce,_1Cf,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Bp(_1Ce,_1Cf,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1BO(_1Ce,_1Cf,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1BE(_1Ce,_1Cf,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Bu(_1Ce,_1Cf,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1C3(_1Ce,_1Cf,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1C8(_1Ce,_1Cf,_bi,_bj);});}];},_1Cg=function(_1Ch,_1Ci,_1Cj,_1Ck,_1Cl,_1Cm,_1Cn){var _1Co=function(_1Cp,_1Cq){return new F(function(){return _af(_1Ch,_1Ci,_1Cj,_1Cl,_1Ck,_1Cn,_1Cm,_1Cp);});};return function(_1Cr,_1Cs){var _1Ct=E(_1Cr);if(!_1Ct[0]){var _1Cu=E(_1Cs);return _1Cu[0]==0?B(_cO(B(_a1(_1Ct[1])),B(_a1(_1Cu[1]))))==2?false:true:true;}else{var _1Cv=E(_1Cs);return _1Cv[0]==0?false:B(_1zD(new T(function(){return B(_1Cd(new T(function(){return B(_15n(_1Co));}),_1Co));}),_1Ct[1],_1Cv[1]))==2?false:true;}};},_1Cw=function(_1Cx,_1Cy,_1Cz,_1CA,_1CB,_1CC,_1CD,_1CE,_1CF,_1CG){return !B(A(_1Cg,[_1Cy,_1Cz,_1CA,_1CB,_1CC,_1CD,_1CE,_1CF,_1CG]))?E(_1CF):E(_1CG);},_1CH=function(_1CI,_1CJ,_1CK,_1CL,_1CM,_1CN,_1CO,_1CP,_1CQ,_1CR){return !B(A(_1Cg,[_1CJ,_1CK,_1CL,_1CM,_1CN,_1CO,_1CP,_1CQ,_1CR]))?E(_1CR):E(_1CQ);},_1CS=function(_1CT,_1CU,_1CV,_1CW,_1CX,_1CY,_1CZ){var _1D0=function(_1D1,_1D2){return new F(function(){return _af(_1CT,_1CU,_1CV,_1CX,_1CW,_1CZ,_1CY,_1D1);});};return function(_1D3,_1D4){var _1D5=E(_1D3);if(!_1D5[0]){var _1D6=_1D5[1],_1D7=E(_1D4);if(!_1D7[0]){var _1D8=_1D7[1];return B(_Z5(_1D6,_1D8,_1))[0]==0?B(_cO(B(_a1(_1D6)),B(_a1(_1D8))))==2?false:true:false;}else{return true;}}else{var _1D9=E(_1D4);return _1D9[0]==0?false:B(_1zD(new T(function(){return B(_1Cd(new T(function(){return B(_15n(_1D0));}),_1D0));}),_1D5[1],_1D9[1]))==0?true:false;}};},_1Da=function(_1Db,_1Dc,_1Dd,_1De,_1Df,_1Dg,_1Dh){var _1Di=function(_1Dj,_1Dk){return new F(function(){return _af(_1Db,_1Dc,_1Dd,_1Df,_1De,_1Dh,_1Dg,_1Dj);});};return function(_1Dl,_1Dm){var _1Dn=E(_1Dl);if(!_1Dn[0]){var _1Do=_1Dn[1],_1Dp=E(_1Dm);if(!_1Dp[0]){var _1Dq=_1Dp[1];return B(_Z5(_1Do,_1Dq,_1))[0]==0?B(_cO(B(_a1(_1Do)),B(_a1(_1Dq))))==2?true:false:false;}else{return false;}}else{var _1Dr=E(_1Dm);return _1Dr[0]==0?true:B(_1zD(new T(function(){return B(_1Cd(new T(function(){return B(_15n(_1Di));}),_1Di));}),_1Dn[1],_1Dr[1]))==2?true:false;}};},_1Ds=function(_1Dt,_1Du,_1Dv,_1Dw,_1Dx,_1Dy,_1Dz){var _1DA=function(_1DB,_1DC){return new F(function(){return _af(_1Dt,_1Du,_1Dv,_1Dx,_1Dw,_1Dz,_1Dy,_1DB);});};return function(_1DD,_1DE){var _1DF=E(_1DD);if(!_1DF[0]){var _1DG=_1DF[1],_1DH=E(_1DE);if(!_1DH[0]){var _1DI=_1DH[1];return B(_Z5(_1DG,_1DI,_1))[0]==0?B(_cO(B(_a1(_1DG)),B(_a1(_1DI))))==2?true:false:true;}else{return false;}}else{var _1DJ=E(_1DE);return _1DJ[0]==0?true:B(_1zD(new T(function(){return B(_1Cd(new T(function(){return B(_15n(_1DA));}),_1DA));}),_1DF[1],_1DJ[1]))==0?false:true;}};},_1DK=function(_1DL,_1DM,_1DN,_1DO,_1DP,_1DQ,_1DR){var _1DS=function(_1DT,_1DU){return new F(function(){return _af(_1DL,_1DM,_1DN,_1DP,_1DO,_1DR,_1DQ,_1DT);});};return function(_1DV,_1DW){var _1DX=E(_1DV);if(!_1DX[0]){var _1DY=_1DX[1],_1DZ=E(_1DW);if(!_1DZ[0]){var _1E0=_1DZ[1];return B(_Z5(_1DY,_1E0,_1))[0]==0?B(_cO(B(_a1(_1DY)),B(_a1(_1E0))))==2?2:0:1;}else{return 0;}}else{var _1E1=E(_1DW);return _1E1[0]==0?2:B(_1zD(new T(function(){return B(_1Cd(new T(function(){return B(_15n(_1DS));}),_1DS));}),_1DX[1],_1E1[1]));}};},_1E2=function(_1E3,_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea){return [0,_1E3,new T(function(){return B(_1DK(_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea));}),new T(function(){return B(_1CS(_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea));}),new T(function(){return B(_1Ds(_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea));}),new T(function(){return B(_1Da(_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea));}),new T(function(){return B(_1Cg(_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea));}),function(_bi,_bj){return new F(function(){return _1Cw(_1E3,_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1CH(_1E3,_1E4,_1E5,_1E6,_1E7,_1E8,_1E9,_1Ea,_bi,_bj);});}];},_1Eb=new T(function(){return B(_YJ(_Q,_u,_Q,_Q,_N,_2,_15));}),_1Ec=new T(function(){return B(_1E2(_1Eb,_Q,_u,_Q,_Q,_N,_15,_2));}),_1Ed=new T(function(){return B(_Z3(_1Eb));}),_1Ee=new T(function(){return B(_1Bh(_1Ed,_1Ec));}),_1Ef=function(_1Eg,_1Eh,_1Ei,_1Ej){var _1Ek=E(_1Ei),_1El=E(_1Ej);return new F(function(){return _1zM(_1Eh,_1Ek[1],_1Ek[2],_1El[1],_1El[2]);});},_1Em=function(_1En,_1Eo,_1Ep,_1Eq){var _1Er=E(_1Ep),_1Es=E(_1Eq);return new F(function(){return _1A1(_1Eo,_1Er[1],_1Er[2],_1Es[1],_1Es[2]);});},_1Et=function(_1Eu,_1Ev,_1Ew,_1Ex){var _1Ey=E(_1Ew),_1Ez=E(_1Ex);return new F(function(){return _1Ag(_1Ev,_1Ey[1],_1Ey[2],_1Ez[1],_1Ez[2]);});},_1EA=function(_1EB,_1EC,_1ED,_1EE){var _1EF=E(_1ED),_1EG=E(_1EE);return new F(function(){return _1Av(_1EC,_1EF[1],_1EF[2],_1EG[1],_1EG[2]);});},_1EH=function(_1EI,_1EJ,_1EK,_1EL){var _1EM=E(_1EK),_1EN=E(_1EL);return new F(function(){return _1AI(_1EJ,_1EM[1],_1EM[2],_1EN[1],_1EN[2]);});},_1EO=function(_1EP,_1EQ,_1ER,_1ES){var _1ET=E(_1ER),_1EU=_1ET[1],_1EV=_1ET[2],_1EW=E(_1ES),_1EX=_1EW[1],_1EY=_1EW[2];switch(B(_1zD(_1EQ,_1EU,_1EX))){case 0:return [0,_1EX,_1EY];case 1:return !B(A(_1zZ,[_1EQ,_1EV,_1EY]))?[0,_1EU,_1EV]:[0,_1EX,_1EY];default:return [0,_1EU,_1EV];}},_1EZ=function(_1F0,_1F1,_1F2,_1F3){var _1F4=E(_1F2),_1F5=_1F4[1],_1F6=_1F4[2],_1F7=E(_1F3),_1F8=_1F7[1],_1F9=_1F7[2];switch(B(_1zD(_1F1,_1F5,_1F8))){case 0:return [0,_1F5,_1F6];case 1:return !B(A(_1zZ,[_1F1,_1F6,_1F9]))?[0,_1F8,_1F9]:[0,_1F5,_1F6];default:return [0,_1F8,_1F9];}},_1Fa=function(_1Fb,_1Fc){return [0,_1Fb,function(_Yn,_Yo){return new F(function(){return _1EH(_1Fb,_1Fc,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Ef(_1Fb,_1Fc,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1EA(_1Fb,_1Fc,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Et(_1Fb,_1Fc,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1Em(_1Fb,_1Fc,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1EO(_1Fb,_1Fc,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1EZ(_1Fb,_1Fc,_Yn,_Yo);});}];},_1Fd=function(_1Fe,_1Ff){return B(_cO(_1Fe,_1Ff))==0?false:true;},_1Fg=function(_1Fh){return E(E(_1Fh)[1]);},_1Fi=function(_1Fj,_1Fk){while(1){var _1Fl=(function(_1Fm,_1Fn){var _1Fo=E(_1Fn);if(!_1Fo[0]){_1Fj=[1,_1Fo[2],new T(function(){return B(_1Fi(_1Fm,_1Fo[4]));})];_1Fk=_1Fo[3];return null;}else{return E(_1Fm);}})(_1Fj,_1Fk);if(_1Fl!=null){return _1Fl;}}},_1Fp=function(_1Fq){return new F(function(){return _1Fi(_9,_1Fq);});},_1Fr=function(_1Fs){return function(_1Ft,_1Fu){var _1Fv=E(_1Ft),_1Fw=E(_1Fu);switch(B(_1zD(new T(function(){return B(_1Fa(new T(function(){return B(_Yl(new T(function(){return B(_1Fg(_1Fs));})));}),_1Fs));}),B(_1Fp(_1Fv[1])),B(_1Fp(_1Fw[1]))))){case 0:return false;case 1:return new F(function(){return _1Fd(_1Fv[2],_1Fw[2]);});break;default:return true;}};},_1Fx=new T(function(){return B(_1Fr(_1Ee));}),_1Fy=function(_1Fz,_1FA,_1FB){var _1FC=E(_1Fz);if(_1FC==1){var _1FD=E(_1FB);return _1FD[0]==0?[0,new T(function(){return [0,1,E(E(_1FA)),E(_1cv),E(_1cv)];}),_9,_9]:!B(A(_1Fx,[_1FA,_1FD[1]]))?[0,new T(function(){return [0,1,E(E(_1FA)),E(_1cv),E(_1cv)];}),_1FD,_9]:[0,new T(function(){return [0,1,E(E(_1FA)),E(_1cv),E(_1cv)];}),_9,_1FD];}else{var _1FE=B(_1Fy(_1FC>>1,_1FA,_1FB)),_1FF=_1FE[1],_1FG=_1FE[3],_1FH=E(_1FE[2]);if(!_1FH[0]){return [0,_1FF,_9,_1FG];}else{var _1FI=_1FH[1],_1FJ=E(_1FH[2]);if(!_1FJ[0]){return [0,new T(function(){return B(_1dS(_1FI,_1FF));}),_9,_1FG];}else{var _1FK=_1FJ[1];if(!B(A(_1Fx,[_1FI,_1FK]))){var _1FL=B(_1Fy(_1FC>>1,_1FK,_1FJ[2]));return [0,new T(function(){return B(_1ew(_1FI,_1FF,_1FL[1]));}),_1FL[2],_1FL[3]];}else{return [0,_1FF,_9,_1FH];}}}}},_1FM=function(_1FN,_1FO){return B(_cO(_1FN,_1FO))==2?false:true;},_1FP=function(_1FQ){return function(_1FR,_1FS){var _1FT=E(_1FR),_1FU=E(_1FS);switch(B(_1zD(new T(function(){return B(_1Fa(new T(function(){return B(_Yl(new T(function(){return B(_1Fg(_1FQ));})));}),_1FQ));}),B(_1Fp(_1FT[1])),B(_1Fp(_1FU[1]))))){case 0:return true;case 1:return new F(function(){return _1FM(_1FT[2],_1FU[2]);});break;default:return false;}};},_1FV=function(_1FW,_1FX,_1FY,_1FZ){return !B(A(_1FP,[_1FX,_1FY,_1FZ]))?E(_1FY):E(_1FZ);},_1G0=function(_1G1,_1G2,_1G3,_1G4){return !B(A(_1FP,[_1G2,_1G3,_1G4]))?E(_1G4):E(_1G3);},_1G5=function(_1G6,_1G7){return B(_cO(_1G6,_1G7))==0?true:false;},_1G8=function(_1G9){return function(_1Ga,_1Gb){var _1Gc=E(_1Ga),_1Gd=E(_1Gb);switch(B(_1zD(new T(function(){return B(_1Fa(new T(function(){return B(_Yl(new T(function(){return B(_1Fg(_1G9));})));}),_1G9));}),B(_1Fp(_1Gc[1])),B(_1Fp(_1Gd[1]))))){case 0:return true;case 1:return new F(function(){return _1G5(_1Gc[2],_1Gd[2]);});break;default:return false;}};},_1Ge=function(_1Gf,_1Gg){return B(_cO(_1Gf,_1Gg))==2?true:false;},_1Gh=function(_1Gi){return function(_1Gj,_1Gk){var _1Gl=E(_1Gj),_1Gm=E(_1Gk);switch(B(_1zD(new T(function(){return B(_1Fa(new T(function(){return B(_Yl(new T(function(){return B(_1Fg(_1Gi));})));}),_1Gi));}),B(_1Fp(_1Gl[1])),B(_1Fp(_1Gm[1]))))){case 0:return false;case 1:return new F(function(){return _1Ge(_1Gl[2],_1Gm[2]);});break;default:return true;}};},_1Gn=function(_1Go){return function(_1Gp,_1Gq){var _1Gr=E(_1Gp),_1Gs=E(_1Gq);switch(B(_1zD(new T(function(){return B(_1Fa(new T(function(){return B(_Yl(new T(function(){return B(_1Fg(_1Go));})));}),_1Go));}),B(_1Fp(_1Gr[1])),B(_1Fp(_1Gs[1]))))){case 0:return 0;case 1:return new F(function(){return _cO(_1Gr[2],_1Gs[2]);});break;default:return 2;}};},_1Gt=function(_1Gu,_1Gv){return [0,_1Gu,new T(function(){return B(_1Gn(_1Gv));}),new T(function(){return B(_1G8(_1Gv));}),new T(function(){return B(_1Fr(_1Gv));}),new T(function(){return B(_1Gh(_1Gv));}),new T(function(){return B(_1FP(_1Gv));}),function(_Yn,_Yo){return new F(function(){return _1FV(_1Gu,_1Gv,_Yn,_Yo);});},function(_Yn,_Yo){return new F(function(){return _1G0(_1Gu,_1Gv,_Yn,_Yo);});}];},_1Gw=function(_1Gx,_1Gy,_1Gz){var _1GA=function(_1GB){var _1GC=function(_1GD){if(_1GB!=_1GD){return false;}else{return new F(function(){return _XX(_1Gx,B(_1Fi(_9,_1Gy)),B(_1Fi(_9,_1Gz)));});}},_1GE=E(_1Gz);return _1GE[0]==0?B(_1GC(_1GE[1])):B(_1GC(0));},_1GF=E(_1Gy);return _1GF[0]==0?B(_1GA(_1GF[1])):B(_1GA(0));},_1GG=function(_1GH,_1GI,_1GJ,_1GK,_1GL){return !B(_1Gw(new T(function(){return B(_Yl(_1GH));}),_1GI,_1GK))?true:!B(_lv(_1GJ,_1GL))?true:false;},_1GM=function(_1GN,_1GO,_1GP){var _1GQ=E(_1GO),_1GR=E(_1GP);return new F(function(){return _1GG(_1GN,_1GQ[1],_1GQ[2],_1GR[1],_1GR[2]);});},_1GS=function(_1GT){return function(_1GU,_1GV){var _1GW=E(_1GU),_1GX=E(_1GV);return !B(_1Gw(new T(function(){return B(_Yl(_1GT));}),_1GW[1],_1GX[1]))?false:B(_lv(_1GW[2],_1GX[2]));};},_1GY=function(_1GZ){return [0,new T(function(){return B(_1GS(_1GZ));}),function(_Yn,_Yo){return new F(function(){return _1GM(_1GZ,_Yn,_Yo);});}];},_1H0=new T(function(){return B(_1GY(_1Ed));}),_1H1=new T(function(){return B(_1Gt(_1H0,_1Ee));}),_1H2=function(_1H3,_1H4,_1H5){var _1H6=E(_1H4),_1H7=E(_1H5);if(!_1H7[0]){var _1H8=_1H7[2],_1H9=_1H7[3],_1Ha=_1H7[4];switch(B(A(_1zB,[_1H3,_1H6,_1H8]))){case 0:return new F(function(){return _1cA(_1H8,B(_1H2(_1H3,_1H6,_1H9)),_1Ha);});break;case 1:return [0,_1H7[1],E(_1H6),E(_1H9),E(_1Ha)];default:return new F(function(){return _1dc(_1H8,_1H9,B(_1H2(_1H3,_1H6,_1Ha)));});}}else{return [0,1,E(_1H6),E(_1cv),E(_1cv)];}},_1Hb=function(_1Hc,_1Hd){while(1){var _1He=E(_1Hd);if(!_1He[0]){return E(_1Hc);}else{var _1Hf=B(_1H2(_1H1,_1He[1],_1Hc));_1Hd=_1He[2];_1Hc=_1Hf;continue;}}},_1Hg=function(_1Hh,_1Hi,_1Hj){return new F(function(){return _1Hb(B(_1H2(_1H1,_1Hi,_1Hh)),_1Hj);});},_1Hk=function(_1Hl,_1Hm,_1Hn){while(1){var _1Ho=E(_1Hn);if(!_1Ho[0]){return E(_1Hm);}else{var _1Hp=_1Ho[1],_1Hq=E(_1Ho[2]);if(!_1Hq[0]){return new F(function(){return _1dS(_1Hp,_1Hm);});}else{var _1Hr=_1Hq[1];if(!B(A(_1Fx,[_1Hp,_1Hr]))){var _1Hs=B(_1Fy(_1Hl,_1Hr,_1Hq[2])),_1Ht=_1Hs[1],_1Hu=E(_1Hs[3]);if(!_1Hu[0]){var _1Hv=_1Hl<<1,_1Hw=B(_1ew(_1Hp,_1Hm,_1Ht));_1Hn=_1Hs[2];_1Hl=_1Hv;_1Hm=_1Hw;continue;}else{return new F(function(){return _1Hg(B(_1ew(_1Hp,_1Hm,_1Ht)),_1Hu[1],_1Hu[2]);});}}else{return new F(function(){return _1Hg(_1Hm,_1Hp,_1Hq);});}}}}},_1Hx=function(_1Hy,_1Hz,_1HA,_1HB){var _1HC=E(_1HB);if(!_1HC[0]){return new F(function(){return _1dS(_1HA,_1Hz);});}else{var _1HD=_1HC[1];if(!B(A(_1Fx,[_1HA,_1HD]))){var _1HE=B(_1Fy(_1Hy,_1HD,_1HC[2])),_1HF=_1HE[1],_1HG=E(_1HE[3]);if(!_1HG[0]){return new F(function(){return _1Hk(_1Hy<<1,B(_1ew(_1HA,_1Hz,_1HF)),_1HE[2]);});}else{return new F(function(){return _1Hg(B(_1ew(_1HA,_1Hz,_1HF)),_1HG[1],_1HG[2]);});}}else{return new F(function(){return _1Hg(_1Hz,_1HA,_1HC);});}}},_1HH=function(_1HI){var _1HJ=E(_1HI);if(!_1HJ[0]){return [1];}else{var _1HK=_1HJ[1],_1HL=E(_1HJ[2]);if(!_1HL[0]){return [0,1,E(E(_1HK)),E(_1cv),E(_1cv)];}else{var _1HM=_1HL[1],_1HN=_1HL[2];if(!B(A(_1Fx,[_1HK,_1HM]))){return new F(function(){return _1Hx(1,[0,1,E(E(_1HK)),E(_1cv),E(_1cv)],_1HM,_1HN);});}else{return new F(function(){return _1Hg([0,1,E(E(_1HK)),E(_1cv),E(_1cv)],_1HM,_1HN);});}}}},_1HO=new T(function(){return B(_1Ds(_Q,_u,_Q,_Q,_N,_15,_2));}),_1HP=function(_1HQ,_1HR,_1HS,_1HT,_1HU){var _1HV=E(_1HQ);if(_1HV==1){var _1HW=E(_1HU);if(!_1HW[0]){return [0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_9,_9];}else{var _1HX=E(_1HW[1]);switch(B(_1zD(_1Ee,_1HR,_1HX[1]))){case 0:return [0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_1HW,_9];case 1:var _1HY=E(_1HX[2]);switch(B(_1zD(_1Ec,_1HS,_1HY[1]))){case 0:return [0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_1HW,_9];case 1:return !B(A(_1HO,[_1HT,_1HY[2]]))?[0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_1HW,_9]:[0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_9,_1HW];default:return [0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_9,_1HW];}break;default:return [0,[0,1,E([0,_1HR,[0,_1HS,_1HT]]),E(_1cv),E(_1cv)],_9,_1HW];}}}else{var _1HZ=B(_1HP(_1HV>>1,_1HR,_1HS,_1HT,_1HU)),_1I0=_1HZ[1],_1I1=_1HZ[3],_1I2=E(_1HZ[2]);if(!_1I2[0]){return [0,_1I0,_9,_1I1];}else{var _1I3=_1I2[1],_1I4=E(_1I2[2]);if(!_1I4[0]){return [0,new T(function(){return B(_1dS(_1I3,_1I0));}),_9,_1I1];}else{var _1I5=_1I4[2],_1I6=E(_1I3),_1I7=E(_1I4[1]),_1I8=_1I7[1],_1I9=_1I7[2];switch(B(_1zD(_1Ee,_1I6[1],_1I8))){case 0:var _1Ia=B(_1Ib(_1HV>>1,_1I8,_1I9,_1I5));return [0,new T(function(){return B(_1ew(_1I6,_1I0,_1Ia[1]));}),_1Ia[2],_1Ia[3]];case 1:var _1Ic=E(_1I6[2]),_1Id=E(_1I9),_1Ie=_1Id[1],_1If=_1Id[2];switch(B(_1zD(_1Ec,_1Ic[1],_1Ie))){case 0:var _1Ig=B(_1HP(_1HV>>1,_1I8,_1Ie,_1If,_1I5));return [0,new T(function(){return B(_1ew(_1I6,_1I0,_1Ig[1]));}),_1Ig[2],_1Ig[3]];case 1:if(!B(A(_1HO,[_1Ic[2],_1If]))){var _1Ih=B(_1HP(_1HV>>1,_1I8,_1Ie,_1If,_1I5));return [0,new T(function(){return B(_1ew(_1I6,_1I0,_1Ih[1]));}),_1Ih[2],_1Ih[3]];}else{return [0,_1I0,_9,_1I2];}break;default:return [0,_1I0,_9,_1I2];}break;default:return [0,_1I0,_9,_1I2];}}}}},_1Ib=function(_1Ii,_1Ij,_1Ik,_1Il){var _1Im=E(_1Ii);if(_1Im==1){var _1In=E(_1Il);if(!_1In[0]){return [0,[0,1,E([0,_1Ij,_1Ik]),E(_1cv),E(_1cv)],_9,_9];}else{var _1Io=E(_1In[1]);switch(B(_1zD(_1Ee,_1Ij,_1Io[1]))){case 0:return [0,[0,1,E([0,_1Ij,_1Ik]),E(_1cv),E(_1cv)],_1In,_9];case 1:var _1Ip=E(_1Ik),_1Iq=E(_1Io[2]);switch(B(_1zD(_1Ec,_1Ip[1],_1Iq[1]))){case 0:return [0,[0,1,E([0,_1Ij,_1Ip]),E(_1cv),E(_1cv)],_1In,_9];case 1:return !B(A(_1HO,[_1Ip[2],_1Iq[2]]))?[0,[0,1,E([0,_1Ij,_1Ip]),E(_1cv),E(_1cv)],_1In,_9]:[0,[0,1,E([0,_1Ij,_1Ip]),E(_1cv),E(_1cv)],_9,_1In];default:return [0,[0,1,E([0,_1Ij,_1Ip]),E(_1cv),E(_1cv)],_9,_1In];}break;default:return [0,[0,1,E([0,_1Ij,_1Ik]),E(_1cv),E(_1cv)],_9,_1In];}}}else{var _1Ir=B(_1Ib(_1Im>>1,_1Ij,_1Ik,_1Il)),_1Is=_1Ir[1],_1It=_1Ir[3],_1Iu=E(_1Ir[2]);if(!_1Iu[0]){return [0,_1Is,_9,_1It];}else{var _1Iv=_1Iu[1],_1Iw=E(_1Iu[2]);if(!_1Iw[0]){return [0,new T(function(){return B(_1dS(_1Iv,_1Is));}),_9,_1It];}else{var _1Ix=_1Iw[2],_1Iy=E(_1Iv),_1Iz=E(_1Iw[1]),_1IA=_1Iz[1],_1IB=_1Iz[2];switch(B(_1zD(_1Ee,_1Iy[1],_1IA))){case 0:var _1IC=B(_1Ib(_1Im>>1,_1IA,_1IB,_1Ix));return [0,new T(function(){return B(_1ew(_1Iy,_1Is,_1IC[1]));}),_1IC[2],_1IC[3]];case 1:var _1ID=E(_1Iy[2]),_1IE=E(_1IB),_1IF=_1IE[1],_1IG=_1IE[2];switch(B(_1zD(_1Ec,_1ID[1],_1IF))){case 0:var _1IH=B(_1HP(_1Im>>1,_1IA,_1IF,_1IG,_1Ix));return [0,new T(function(){return B(_1ew(_1Iy,_1Is,_1IH[1]));}),_1IH[2],_1IH[3]];case 1:if(!B(A(_1HO,[_1ID[2],_1IG]))){var _1II=B(_1HP(_1Im>>1,_1IA,_1IF,_1IG,_1Ix));return [0,new T(function(){return B(_1ew(_1Iy,_1Is,_1II[1]));}),_1II[2],_1II[3]];}else{return [0,_1Is,_9,_1Iu];}break;default:return [0,_1Is,_9,_1Iu];}break;default:return [0,_1Is,_9,_1Iu];}}}}},_1IJ=new T(function(){return B(_1DK(_Q,_u,_Q,_Q,_N,_15,_2));}),_1IK=function(_1IL,_1IM,_1IN,_1IO){var _1IP=E(_1IO);if(!_1IP[0]){var _1IQ=_1IP[3],_1IR=_1IP[4],_1IS=E(_1IP[2]);switch(B(_1zD(_1Ee,_1IL,_1IS[1]))){case 0:return new F(function(){return _1cA(_1IS,B(_1IK(_1IL,_1IM,_1IN,_1IQ)),_1IR);});break;case 1:var _1IT=E(_1IS[2]);switch(B(_1zD(_1Ec,_1IM,_1IT[1]))){case 0:return new F(function(){return _1cA(_1IS,B(_1IK(_1IL,_1IM,_1IN,_1IQ)),_1IR);});break;case 1:switch(B(A(_1IJ,[_1IN,_1IT[2]]))){case 0:return new F(function(){return _1cA(_1IS,B(_1IK(_1IL,_1IM,_1IN,_1IQ)),_1IR);});break;case 1:return [0,_1IP[1],E([0,_1IL,[0,_1IM,_1IN]]),E(_1IQ),E(_1IR)];default:return new F(function(){return _1dc(_1IS,_1IQ,B(_1IK(_1IL,_1IM,_1IN,_1IR)));});}break;default:return new F(function(){return _1dc(_1IS,_1IQ,B(_1IK(_1IL,_1IM,_1IN,_1IR)));});}break;default:return new F(function(){return _1dc(_1IS,_1IQ,B(_1IK(_1IL,_1IM,_1IN,_1IR)));});}}else{return [0,1,E([0,_1IL,[0,_1IM,_1IN]]),E(_1cv),E(_1cv)];}},_1IU=function(_1IV,_1IW,_1IX){var _1IY=E(_1IX);if(!_1IY[0]){var _1IZ=_1IY[3],_1J0=_1IY[4],_1J1=E(_1IY[2]);switch(B(_1zD(_1Ee,_1IV,_1J1[1]))){case 0:return new F(function(){return _1cA(_1J1,B(_1IU(_1IV,_1IW,_1IZ)),_1J0);});break;case 1:var _1J2=E(_1IW),_1J3=_1J2[1],_1J4=_1J2[2],_1J5=E(_1J1[2]);switch(B(_1zD(_1Ec,_1J3,_1J5[1]))){case 0:return new F(function(){return _1cA(_1J1,B(_1IK(_1IV,_1J3,_1J4,_1IZ)),_1J0);});break;case 1:switch(B(A(_1IJ,[_1J4,_1J5[2]]))){case 0:return new F(function(){return _1cA(_1J1,B(_1IK(_1IV,_1J3,_1J4,_1IZ)),_1J0);});break;case 1:return [0,_1IY[1],E([0,_1IV,_1J2]),E(_1IZ),E(_1J0)];default:return new F(function(){return _1dc(_1J1,_1IZ,B(_1IK(_1IV,_1J3,_1J4,_1J0)));});}break;default:return new F(function(){return _1dc(_1J1,_1IZ,B(_1IK(_1IV,_1J3,_1J4,_1J0)));});}break;default:return new F(function(){return _1dc(_1J1,_1IZ,B(_1IU(_1IV,_1IW,_1J0)));});}}else{return [0,1,E([0,_1IV,_1IW]),E(_1cv),E(_1cv)];}},_1J6=function(_1J7,_1J8){while(1){var _1J9=E(_1J8);if(!_1J9[0]){return E(_1J7);}else{var _1Ja=E(_1J9[1]),_1Jb=B(_1IU(_1Ja[1],_1Ja[2],_1J7));_1J8=_1J9[2];_1J7=_1Jb;continue;}}},_1Jc=function(_1Jd,_1Je,_1Jf,_1Jg){return new F(function(){return _1J6(B(_1IU(_1Je,_1Jf,_1Jd)),_1Jg);});},_1Jh=function(_1Ji,_1Jj,_1Jk){var _1Jl=E(_1Jj);return new F(function(){return _1J6(B(_1IU(_1Jl[1],_1Jl[2],_1Ji)),_1Jk);});},_1Jm=function(_1Jn,_1Jo,_1Jp){var _1Jq=E(_1Jp);if(!_1Jq[0]){return E(_1Jo);}else{var _1Jr=_1Jq[1],_1Js=E(_1Jq[2]);if(!_1Js[0]){return new F(function(){return _1dS(_1Jr,_1Jo);});}else{var _1Jt=E(_1Jr),_1Ju=_1Jt[1],_1Jv=_1Jt[2],_1Jw=E(_1Js[1]),_1Jx=_1Jw[1],_1Jy=_1Jw[2],_1Jz=function(_1JA){var _1JB=B(_1Ib(_1Jn,_1Jx,_1Jy,_1Js[2])),_1JC=_1JB[1],_1JD=E(_1JB[3]);if(!_1JD[0]){return new F(function(){return _1Jm(_1Jn<<1,B(_1ew(_1Jt,_1Jo,_1JC)),_1JB[2]);});}else{return new F(function(){return _1Jh(B(_1ew(_1Jt,_1Jo,_1JC)),_1JD[1],_1JD[2]);});}};switch(B(_1zD(_1Ee,_1Ju,_1Jx))){case 0:return new F(function(){return _1Jz(_);});break;case 1:var _1JE=E(_1Jv),_1JF=E(_1Jy);switch(B(_1zD(_1Ec,_1JE[1],_1JF[1]))){case 0:return new F(function(){return _1Jz(_);});break;case 1:return !B(A(_1HO,[_1JE[2],_1JF[2]]))?B(_1Jz(_)):B(_1Jc(_1Jo,_1Ju,_1JE,_1Js));default:return new F(function(){return _1Jc(_1Jo,_1Ju,_1JE,_1Js);});}break;default:return new F(function(){return _1Jc(_1Jo,_1Ju,_1Jv,_1Js);});}}}},_1JG=function(_1JH,_1JI,_1JJ,_1JK,_1JL,_1JM){var _1JN=E(_1JM);if(!_1JN[0]){return new F(function(){return _1dS([0,_1JJ,[0,_1JK,_1JL]],_1JI);});}else{var _1JO=E(_1JN[1]),_1JP=_1JO[1],_1JQ=_1JO[2],_1JR=function(_1JS){var _1JT=B(_1Ib(_1JH,_1JP,_1JQ,_1JN[2])),_1JU=_1JT[1],_1JV=E(_1JT[3]);if(!_1JV[0]){return new F(function(){return _1Jm(_1JH<<1,B(_1ew([0,_1JJ,[0,_1JK,_1JL]],_1JI,_1JU)),_1JT[2]);});}else{return new F(function(){return _1Jh(B(_1ew([0,_1JJ,[0,_1JK,_1JL]],_1JI,_1JU)),_1JV[1],_1JV[2]);});}};switch(B(_1zD(_1Ee,_1JJ,_1JP))){case 0:return new F(function(){return _1JR(_);});break;case 1:var _1JW=E(_1JQ);switch(B(_1zD(_1Ec,_1JK,_1JW[1]))){case 0:return new F(function(){return _1JR(_);});break;case 1:return !B(A(_1HO,[_1JL,_1JW[2]]))?B(_1JR(_)):B(_1Jc(_1JI,_1JJ,[0,_1JK,_1JL],_1JN));default:return new F(function(){return _1Jc(_1JI,_1JJ,[0,_1JK,_1JL],_1JN);});}break;default:return new F(function(){return _1Jc(_1JI,_1JJ,[0,_1JK,_1JL],_1JN);});}}},_1JX=function(_1JY,_1JZ,_1K0,_1K1,_1K2){var _1K3=E(_1K2);if(!_1K3[0]){return new F(function(){return _1dS([0,_1K0,_1K1],_1JZ);});}else{var _1K4=E(_1K3[1]),_1K5=_1K4[1],_1K6=_1K4[2],_1K7=function(_1K8){var _1K9=B(_1Ib(_1JY,_1K5,_1K6,_1K3[2])),_1Ka=_1K9[1],_1Kb=E(_1K9[3]);if(!_1Kb[0]){return new F(function(){return _1Jm(_1JY<<1,B(_1ew([0,_1K0,_1K1],_1JZ,_1Ka)),_1K9[2]);});}else{return new F(function(){return _1Jh(B(_1ew([0,_1K0,_1K1],_1JZ,_1Ka)),_1Kb[1],_1Kb[2]);});}};switch(B(_1zD(_1Ee,_1K0,_1K5))){case 0:return new F(function(){return _1K7(_);});break;case 1:var _1Kc=E(_1K1),_1Kd=E(_1K6);switch(B(_1zD(_1Ec,_1Kc[1],_1Kd[1]))){case 0:return new F(function(){return _1K7(_);});break;case 1:return !B(A(_1HO,[_1Kc[2],_1Kd[2]]))?B(_1K7(_)):B(_1Jc(_1JZ,_1K0,_1Kc,_1K3));default:return new F(function(){return _1Jc(_1JZ,_1K0,_1Kc,_1K3);});}break;default:return new F(function(){return _1Jc(_1JZ,_1K0,_1K1,_1K3);});}}},_1Ke=function(_1Kf){var _1Kg=E(_1Kf);if(!_1Kg[0]){return [1];}else{var _1Kh=_1Kg[1],_1Ki=E(_1Kg[2]);if(!_1Ki[0]){return [0,1,E(E(_1Kh)),E(_1cv),E(_1cv)];}else{var _1Kj=_1Ki[2],_1Kk=E(_1Kh),_1Kl=E(_1Ki[1]),_1Km=_1Kl[1],_1Kn=_1Kl[2];switch(B(_1zD(_1Ee,_1Kk[1],_1Km))){case 0:return new F(function(){return _1JX(1,[0,1,E(_1Kk),E(_1cv),E(_1cv)],_1Km,_1Kn,_1Kj);});break;case 1:var _1Ko=E(_1Kk[2]),_1Kp=E(_1Kn),_1Kq=_1Kp[1],_1Kr=_1Kp[2];switch(B(_1zD(_1Ec,_1Ko[1],_1Kq))){case 0:return new F(function(){return _1JG(1,[0,1,E(_1Kk),E(_1cv),E(_1cv)],_1Km,_1Kq,_1Kr,_1Kj);});break;case 1:return !B(A(_1HO,[_1Ko[2],_1Kr]))?B(_1JG(1,[0,1,E(_1Kk),E(_1cv),E(_1cv)],_1Km,_1Kq,_1Kr,_1Kj)):B(_1Jc([0,1,E(_1Kk),E(_1cv),E(_1cv)],_1Km,_1Kp,_1Kj));default:return new F(function(){return _1Jc([0,1,E(_1Kk),E(_1cv),E(_1cv)],_1Km,_1Kp,_1Kj);});}break;default:return new F(function(){return _1Jc([0,1,E(_1Kk),E(_1cv),E(_1cv)],_1Km,_1Kn,_1Kj);});}}}},_1Ks=new T(function(){return B(_F(0,1,_9));}),_1Kt=new T(function(){return B(unAppCStr("delta_",_1Ks));}),_1Ku=[9,_,_,_1Kt],_1Kv=[0,_1Ku],_1Kw=[1,_1Kv,_9],_1Kx=new T(function(){return B(unAppCStr("phi_",_1Ks));}),_1Ky=[3,_,_,_1Kx],_1Kz=[2,_,_1Ky],_1KA=[1,_1Kz,_9],_1KB=[1,_1KA],_1KC=[0,_1Kw,_1KB],_1KD=new T(function(){return B(_F(0,2,_9));}),_1KE=new T(function(){return B(unAppCStr("phi_",_1KD));}),_1KF=[3,_,_,_1KE],_1KG=[2,_,_1KF],_1KH=[1,_1KG,_9],_1KI=[1,_1KH],_1KJ=new T(function(){return B(unAppCStr("delta_",_1KD));}),_1KK=[9,_,_,_1KJ],_1KL=[0,_1KK],_1KM=[1,_1KL,_9],_1KN=[0,_1KM,_1KI],_1KO=[1,_1KN,_9],_1KP=[1,_1KC,_1KO],_1KQ=[9,_,_PR,_1Kz,_1KG],_1KR=[1,_1KQ,_9],_1KS=[1,_1KR],_1KT=[1,_1Kv,_1KM],_1KU=[0,_1KT,_1KS],_1KV=[0,_1KP,_1KU],_1KW=[0,_1KM,_1KB],_1KX=[1,_1KW,_9],_1KY=[0,_1Kw,_1KI],_1KZ=[1,_1KY,_1KX],_1L0=[0,_1KZ,_1KU],_1L1=[1,_1L0,_9],_1L2=[1,_1KV,_1L1],_1L3=new T(function(){return B(_1Ke(_1L2));}),_1L4=[0,_1L3,_1zh],_1L5=[1,_1KC,_9],_1L6=[9,_,_Pt,_1Kz,_1KG],_1L7=[1,_1L6,_9],_1L8=[1,_1L7],_1L9=[0,_1Kw,_1L8],_1La=[0,_1L5,_1L9],_1Lb=[9,_,_Pt,_1KG,_1Kz],_1Lc=[1,_1Lb,_9],_1Ld=[1,_1Lc],_1Le=[0,_1Kw,_1Ld],_1Lf=[0,_1L5,_1Le],_1Lg=[1,_1Lf,_9],_1Lh=[1,_1La,_1Lg],_1Li=new T(function(){return B(_1Ke(_1Lh));}),_1Lj=[0,_1Li,_1zg],_1Lk=[1,_1KB,_1KM],_1Ll=[7,_,_Qi,_1KG],_1Lm=[1,_1Ll,_9],_1Ln=[1,_1Lm],_1Lo=[0,_1Lk,_1Ln],_1Lp=[1,_1Lo,_9],_1Lq=[1,_1KB,_1Kw],_1Lr=[0,_1Lq,_1KI],_1Ls=[1,_1Lr,_1Lp],_1Lt=[7,_,_Qi,_1Kz],_1Lu=[1,_1Lt,_9],_1Lv=[1,_1Lu],_1Lw=[0,_1KT,_1Lv],_1Lx=[0,_1Ls,_1Lw],_1Ly=[1,_1KY,_1Lp],_1Lz=[0,_1Ly,_1Lw],_1LA=[0,_1KM,_1Ln],_1LB=[1,_1LA,_9],_1LC=[1,_1Lr,_1LB],_1LD=[0,_1LC,_1Lw],_1LE=[1,_1KY,_1LB],_1LF=[0,_1LE,_1Lw],_1LG=[1,_1Lr,_9],_1LH=[1,_1Lo,_1LG],_1LI=[0,_1LH,_1Lw],_1LJ=[1,_1LA,_1LG],_1LK=[0,_1LJ,_1Lw],_1LL=[1,_1KY,_9],_1LM=[1,_1Lo,_1LL],_1LN=[0,_1LM,_1Lw],_1LO=[1,_1LA,_1LL],_1LP=[0,_1LO,_1Lw],_1LQ=[1,_1Lv,_1KM],_1LR=[0,_1LQ,_1Ln],_1LS=[1,_1Lv,_1Kw],_1LT=[0,_1LS,_1KI],_1LU=[1,_1LT,_9],_1LV=[1,_1LR,_1LU],_1LW=[0,_1KT,_1KB],_1LX=[0,_1LV,_1LW],_1LY=[1,_1LA,_1LU],_1LZ=[0,_1LY,_1LW],_1M0=[1,_1LR,_1LL],_1M1=[0,_1M0,_1LW],_1M2=[0,_1LO,_1LW],_1M3=[1,_1M2,_9],_1M4=[1,_1M1,_1M3],_1M5=[1,_1LZ,_1M4],_1M6=[1,_1LX,_1M5],_1M7=[1,_1LP,_1M6],_1M8=[1,_1LN,_1M7],_1M9=[1,_1LK,_1M8],_1Ma=[1,_1LI,_1M9],_1Mb=[1,_1LF,_1Ma],_1Mc=[1,_1LD,_1Mb],_1Md=[1,_1Lz,_1Mc],_1Me=[1,_1Lx,_1Md],_1Mf=new T(function(){return B(_1Ke(_1Me));}),_1Mg=[0,_1Mf,_1zr],_1Mh=[1,_1Mg,_9],_1Mi=[1,_1Lj,_1Mh],_1Mj=[0,83],_1Mk=[1,_1Mj,_9],_1Ml=[0,_1Kw,_1KS],_1Mm=[1,_1Ml,_9],_1Mn=[0,_1Mm,_1KC],_1Mo=[0,_1Mm,_1KY],_1Mp=[1,_1Mo,_9],_1Mq=[1,_1Mn,_1Mp],_1Mr=new T(function(){return B(_1Ke(_1Mq));}),_1Ms=[0,_1Mr,_1Mk],_1Mt=[1,_1Ms,_1Mi],_1Mu=[0,_1KT,_1KI],_1Mv=[0,_1KM,_1Lv],_1Mw=[1,_1Mv,_9],_1Mx=[1,_1Le,_1Mw],_1My=[0,_1Mx,_1Mu],_1Mz=[1,_1Le,_9],_1MA=[1,_1Mv,_1Mz],_1MB=[0,_1MA,_1Mu],_1MC=[1,_1My,_9],_1MD=[1,_1MB,_1MC],_1ME=[1,_1My,_1MD],_1MF=[1,_1My,_1ME],_1MG=new T(function(){return B(_1Ke(_1MF));}),_1MH=[0,_1MG,_1zp],_1MI=[1,_1MH,_1Mt],_1MJ=[9,_,_Oh,_1Kz,_1KG],_1MK=[1,_1MJ,_9],_1ML=[1,_1MK],_1MM=[0,_1KM,_1ML],_1MN=[1,_1MM,_9],_1MO=[1,_1KC,_1MN],_1MP=[0,_1MO,_1Mu],_1MQ=[0,_1Kw,_1ML],_1MR=[1,_1MQ,_1KX],_1MS=[0,_1MR,_1Mu],_1MT=[1,_1MS,_9],_1MU=[1,_1MP,_1MT],_1MV=new T(function(){return B(_1Ke(_1MU));}),_1MW=[0,_1MV,_1zq],_1MX=[1,_1MW,_1MI],_1MY=[0,_1LL,_1MQ],_1MZ=[0,_1LG,_1MQ],_1N0=[1,_1MZ,_9],_1N1=[1,_1MY,_1N0],_1N2=new T(function(){return B(_1Ke(_1N1));}),_1N3=[0,_1N2,_1zs],_1N4=[1,_1N3,_1MX],_1N5=[1,_1L4,_1N4],_1N6=new T(function(){return B(_1HH(_1N5));}),_1N7=[0,_1zy,_1N6],_1N8=function(_){return new F(function(){return _1yU(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1N7,_);});},_1N9=function(_){return new F(function(){return _1N8(_);});};
var hasteMain = function() {B(A(_1N9, [0]));};window.onload = hasteMain;