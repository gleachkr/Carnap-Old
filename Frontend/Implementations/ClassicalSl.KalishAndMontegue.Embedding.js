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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr(" . "));}),_1r=function(_1s){var _1t=E(_1s);switch(_1t[0]){case 0:return E(_1t[3]);case 1:return E(_1t[3]);case 2:return E(_1t[3]);case 3:return E(_1t[3]);case 4:return E(_1t[3]);case 5:return E(_1t[3]);case 6:return E(_1t[3]);case 7:return E(_1t[3]);case 8:return E(_1t[3]);default:return E(_1t[3]);}},_1u=[0,41],_1v=[1,_1u,_9],_1w=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1x=new T(function(){return B(unCStr("base"));}),_1y=new T(function(){return B(unCStr("PatternMatchFail"));}),_1z=new T(function(){var _1A=hs_wordToWord64(18445595),_1B=_1A,_1C=hs_wordToWord64(52003073),_1D=_1C;return [0,_1B,_1D,[0,_1B,_1D,_1x,_1w,_1y],_9];}),_1E=function(_1F){return E(_1z);},_1G=function(_1H){return E(E(_1H)[1]);},_1I=function(_1J,_1K,_1L){var _1M=B(A(_1J,[_])),_1N=B(A(_1K,[_])),_1O=hs_eqWord64(_1M[1],_1N[1]),_1P=_1O;if(!E(_1P)){return [0];}else{var _1Q=hs_eqWord64(_1M[2],_1N[2]),_1R=_1Q;return E(_1R)==0?[0]:[1,_1L];}},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return _1I(B(_1G(_1U[1])),_1E,_1U[2]);});},_1V=function(_1W){return E(E(_1W)[1]);},_1X=function(_1Y,_1Z){return new F(function(){return _e(E(_1Y)[1],_1Z);});},_20=[0,44],_21=[0,93],_22=[0,91],_23=function(_24,_25,_26){var _27=E(_25);return _27[0]==0?B(unAppCStr("[]",_26)):[1,_22,new T(function(){return B(A(_24,[_27[1],new T(function(){var _28=function(_29){var _2a=E(_29);return _2a[0]==0?E([1,_21,_26]):[1,_20,new T(function(){return B(A(_24,[_2a[1],new T(function(){return B(_28(_2a[2]));})]));})];};return B(_28(_27[2]));})]));})];},_2b=function(_2c,_2d){return new F(function(){return _23(_1X,_2c,_2d);});},_2e=function(_2f,_2g,_2h){return new F(function(){return _e(E(_2g)[1],_2h);});},_2i=[0,_2e,_1V,_2b],_2j=new T(function(){return [0,_1E,_2i,_2k,_1S];}),_2k=function(_2l){return [0,_2j,_2l];},_2m=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_2n=function(_2o,_2p){return new F(function(){return die(new T(function(){return B(A(_2p,[_2o]));}));});},_2q=function(_2r,_2s){var _2t=E(_2s);if(!_2t[0]){return [0,_9,_9];}else{var _2u=_2t[1];if(!B(A(_2r,[_2u]))){return [0,_9,_2t];}else{var _2v=new T(function(){var _2w=B(_2q(_2r,_2t[2]));return [0,_2w[1],_2w[2]];});return [0,[1,_2u,new T(function(){return E(E(_2v)[1]);})],new T(function(){return E(E(_2v)[2]);})];}}},_2x=[0,32],_2y=[0,10],_2z=[1,_2y,_9],_2A=function(_2B){return E(E(_2B)[1])==124?false:true;},_2C=function(_2D,_2E){var _2F=B(_2q(_2A,B(unCStr(_2D)))),_2G=_2F[1],_2H=function(_2I,_2J){return new F(function(){return _e(_2I,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_2E,new T(function(){return B(_e(_2J,_2z));},1)));})));},1));});},_2K=E(_2F[2]);if(!_2K[0]){return new F(function(){return _2H(_2G,_9);});}else{return E(E(_2K[1])[1])==124?B(_2H(_2G,[1,_2x,_2K[2]])):B(_2H(_2G,_9));}},_2L=function(_2M){return new F(function(){return _2n([0,new T(function(){return B(_2C(_2M,_2m));})],_2k);});},_2N=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_2O=[0,44],_2P=[0,40],_2Q=function(_2R,_2S,_2T){var _2U=E(_2T);switch(_2U[0]){case 0:return E(_2N);case 1:return new F(function(){return A(_2R,[_2U[2],_9]);});break;case 2:return new F(function(){return _1r(_2U[2]);});break;case 3:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),[1,new T(function(){return B(_2Q(_2R,_2S,_2U[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[4])),_1v));})]));})]);});}},_2V=[0],_2W=function(_2X,_2Y,_2Z,_30,_31,_32,_33,_34){var _35=E(_34);switch(_35[0]){case 0:return [0];case 1:return new F(function(){return A(_30,[_35[2],_9]);});break;case 2:return new F(function(){return _1r(_35[2]);});break;case 3:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),[1,new T(function(){return B(_2Q(_30,_31,_35[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_30,_31,_35[4])),_1v));})]));})]);});break;case 7:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_1r(_35[2])),new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));},1));});break;case 9:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4]));}),_9]]]);});break;case 10:return [1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3])),new T(function(){return B(_e(B(_1r(_35[2])),new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4])),_1v));},1)));},1)));})];case 11:var _36=_35[2],_37=_35[3];return new F(function(){return A(_2Z,[_36,[1,new T(function(){return B(A(_32,[new T(function(){return B(A(_37,[_2V]));}),_36]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_37,[_2V]))));}),_9]]]);});break;default:var _38=_35[2],_39=_35[3];return new F(function(){return _e(B(_1r(_38)),new T(function(){return B(_e(B(A(_33,[new T(function(){return B(A(_39,[_2V]));}),_38])),[1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_39,[_2V])))),_1v));})]));},1));});}},_3a=function(_3b){var _3c=E(_3b);if(!_3c[0]){return [0];}else{return new F(function(){return _e(_3c[1],new T(function(){return B(_3a(_3c[2]));},1));});}},_3d=function(_3e,_3f){var _3g=E(_3f);return _3g[0]==0?[0]:[1,new T(function(){return B(A(_3e,[_3g[1]]));}),new T(function(){return B(_3d(_3e,_3g[2]));})];},_3h=function(_3i,_3j){var _3k=E(_3j);return _3k[0]==0?[0]:[1,_3i,[1,_3k[1],new T(function(){return B(_3h(_3i,_3k[2]));})]];},_3l=function(_3m,_3n,_3o,_3p,_3q,_3r,_3s,_3t){var _3u=E(_3t);if(!_3u[0]){return new F(function(){return _1r(_3u[1]);});}else{var _3v=B(_3d(function(_3w){return new F(function(){return _2W(_3m,_3n,_3o,_3q,_3p,_3r,_3s,_3w);});},_3u[1]));return _3v[0]==0?[0]:B(_3a([1,_3v[1],new T(function(){return B(_3h(_1q,_3v[2]));})]));}},_3x=function(_3y,_3z){while(1){var _3A=E(_3y);if(!_3A[0]){return E(_3z)[0]==0?true:false;}else{var _3B=E(_3z);if(!_3B[0]){return false;}else{if(E(_3A[1])[1]!=E(_3B[1])[1]){return false;}else{_3y=_3A[2];_3z=_3B[2];continue;}}}}},_3C=function(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K,_3L){return new F(function(){return _3x(B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K)),B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3L)));});},_3M=function(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V){return !B(_3C(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V))?true:false;},_3W=function(_3X,_3Y,_3Z,_40,_41,_42,_43){return [0,function(_44,_45){return new F(function(){return _3C(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});},function(_44,_45){return new F(function(){return _3M(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});}];},_46=new T(function(){return B(unCStr("wheel"));}),_47=new T(function(){return B(unCStr("mouseout"));}),_48=new T(function(){return B(unCStr("mouseover"));}),_49=new T(function(){return B(unCStr("mousemove"));}),_4a=new T(function(){return B(unCStr("blur"));}),_4b=new T(function(){return B(unCStr("focus"));}),_4c=new T(function(){return B(unCStr("change"));}),_4d=new T(function(){return B(unCStr("unload"));}),_4e=new T(function(){return B(unCStr("load"));}),_4f=new T(function(){return B(unCStr("submit"));}),_4g=new T(function(){return B(unCStr("keydown"));}),_4h=new T(function(){return B(unCStr("keyup"));}),_4i=new T(function(){return B(unCStr("keypress"));}),_4j=new T(function(){return B(unCStr("mouseup"));}),_4k=new T(function(){return B(unCStr("mousedown"));}),_4l=new T(function(){return B(unCStr("dblclick"));}),_4m=new T(function(){return B(unCStr("click"));}),_4n=function(_4o){switch(E(_4o)[0]){case 0:return E(_4e);case 1:return E(_4d);case 2:return E(_4c);case 3:return E(_4b);case 4:return E(_4a);case 5:return E(_49);case 6:return E(_48);case 7:return E(_47);case 8:return E(_4m);case 9:return E(_4l);case 10:return E(_4k);case 11:return E(_4j);case 12:return E(_4i);case 13:return E(_4h);case 14:return E(_4g);case 15:return E(_4f);default:return E(_46);}},_4p=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_4q=new T(function(){return B(unCStr("main"));}),_4r=new T(function(){return B(unCStr("EventData"));}),_4s=new T(function(){var _4t=hs_wordToWord64(3703396926),_4u=_4t,_4v=hs_wordToWord64(1660403598),_4w=_4v;return [0,_4u,_4w,[0,_4u,_4w,_4q,_4p,_4r],_9];}),_4x=[0,0],_4y=false,_4z=2,_4A=[1],_4B=new T(function(){return B(unCStr("Dynamic"));}),_4C=new T(function(){return B(unCStr("Data.Dynamic"));}),_4D=new T(function(){return B(unCStr("base"));}),_4E=new T(function(){var _4F=hs_wordToWord64(628307645),_4G=_4F,_4H=hs_wordToWord64(949574464),_4I=_4H;return [0,_4G,_4I,[0,_4G,_4I,_4D,_4C,_4B],_9];}),_4J=[0],_4K=new T(function(){return B(unCStr("OnLoad"));}),_4L=[0,_4K,_4J],_4M=[0,_4s,_4L],_4N=[0,_4E,_4M],_4O=[0],_4P=function(_){return _4O;},_4Q=function(_4R,_){return _4O;},_4S=[0,_4P,_4Q],_4T=[0,_9,_4x,_4z,_4S,_4y,_4N,_4A],_4U=function(_){var _=0,_4V=newMVar(),_4W=_4V,_=putMVar(_4W,_4T);return [0,_4W];},_4X=function(_4Y){var _4Z=B(A(_4Y,[_])),_50=_4Z;return E(_50);},_51=new T(function(){return B(_4X(_4U));}),_52=new T(function(){return B(_2L("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_53=[0,_4e,_4J],_54=[0,_4s,_53],_55=[0,_4d,_4J],_56=[0,_4s,_55],_57=[0,_4c,_4J],_58=[0,_4s,_57],_59=[0,_4b,_4J],_5a=[0,_4s,_59],_5b=[0,_4a,_4J],_5c=[0,_4s,_5b],_5d=[3],_5e=[0,_47,_5d],_5f=[0,_4s,_5e],_5g=function(_5h,_5i){switch(E(_5h)[0]){case 0:return function(_){var _5j=E(_51)[1],_5k=takeMVar(_5j),_5l=_5k,_=putMVar(_5j,new T(function(){var _5m=E(_5l);return [0,_5m[1],_5m[2],_5m[3],_5m[4],_5m[5],_54,_5m[7]];}));return new F(function(){return A(_5i,[_]);});};case 1:return function(_){var _5n=E(_51)[1],_5o=takeMVar(_5n),_5p=_5o,_=putMVar(_5n,new T(function(){var _5q=E(_5p);return [0,_5q[1],_5q[2],_5q[3],_5q[4],_5q[5],_56,_5q[7]];}));return new F(function(){return A(_5i,[_]);});};case 2:return function(_){var _5r=E(_51)[1],_5s=takeMVar(_5r),_5t=_5s,_=putMVar(_5r,new T(function(){var _5u=E(_5t);return [0,_5u[1],_5u[2],_5u[3],_5u[4],_5u[5],_58,_5u[7]];}));return new F(function(){return A(_5i,[_]);});};case 3:return function(_){var _5v=E(_51)[1],_5w=takeMVar(_5v),_5x=_5w,_=putMVar(_5v,new T(function(){var _5y=E(_5x);return [0,_5y[1],_5y[2],_5y[3],_5y[4],_5y[5],_5a,_5y[7]];}));return new F(function(){return A(_5i,[_]);});};case 4:return function(_){var _5z=E(_51)[1],_5A=takeMVar(_5z),_5B=_5A,_=putMVar(_5z,new T(function(){var _5C=E(_5B);return [0,_5C[1],_5C[2],_5C[3],_5C[4],_5C[5],_5c,_5C[7]];}));return new F(function(){return A(_5i,[_]);});};case 5:return function(_5D){return function(_){var _5E=E(_51)[1],_5F=takeMVar(_5E),_5G=_5F,_=putMVar(_5E,new T(function(){var _5H=E(_5G);return [0,_5H[1],_5H[2],_5H[3],_5H[4],_5H[5],[0,_4s,[0,_49,[2,E(_5D)]]],_5H[7]];}));return new F(function(){return A(_5i,[_]);});};};case 6:return function(_5I){return function(_){var _5J=E(_51)[1],_5K=takeMVar(_5J),_5L=_5K,_=putMVar(_5J,new T(function(){var _5M=E(_5L);return [0,_5M[1],_5M[2],_5M[3],_5M[4],_5M[5],[0,_4s,[0,_48,[2,E(_5I)]]],_5M[7]];}));return new F(function(){return A(_5i,[_]);});};};case 7:return function(_){var _5N=E(_51)[1],_5O=takeMVar(_5N),_5P=_5O,_=putMVar(_5N,new T(function(){var _5Q=E(_5P);return [0,_5Q[1],_5Q[2],_5Q[3],_5Q[4],_5Q[5],_5f,_5Q[7]];}));return new F(function(){return A(_5i,[_]);});};case 8:return function(_5R,_5S){return function(_){var _5T=E(_51)[1],_5U=takeMVar(_5T),_5V=_5U,_=putMVar(_5T,new T(function(){var _5W=E(_5V);return [0,_5W[1],_5W[2],_5W[3],_5W[4],_5W[5],[0,_4s,[0,_4m,[1,_5R,E(_5S)]]],_5W[7]];}));return new F(function(){return A(_5i,[_]);});};};case 9:return function(_5X,_5Y){return function(_){var _5Z=E(_51)[1],_60=takeMVar(_5Z),_61=_60,_=putMVar(_5Z,new T(function(){var _62=E(_61);return [0,_62[1],_62[2],_62[3],_62[4],_62[5],[0,_4s,[0,_4l,[1,_5X,E(_5Y)]]],_62[7]];}));return new F(function(){return A(_5i,[_]);});};};case 10:return function(_63,_64){return function(_){var _65=E(_51)[1],_66=takeMVar(_65),_67=_66,_=putMVar(_65,new T(function(){var _68=E(_67);return [0,_68[1],_68[2],_68[3],_68[4],_68[5],[0,_4s,[0,_4k,[1,_63,E(_64)]]],_68[7]];}));return new F(function(){return A(_5i,[_]);});};};case 11:return function(_69,_6a){return function(_){var _6b=E(_51)[1],_6c=takeMVar(_6b),_6d=_6c,_=putMVar(_6b,new T(function(){var _6e=E(_6d);return [0,_6e[1],_6e[2],_6e[3],_6e[4],_6e[5],[0,_4s,[0,_4j,[1,_69,E(_6a)]]],_6e[7]];}));return new F(function(){return A(_5i,[_]);});};};case 12:return function(_6f,_){var _6g=E(_51)[1],_6h=takeMVar(_6g),_6i=_6h,_=putMVar(_6g,new T(function(){var _6j=E(_6i);return [0,_6j[1],_6j[2],_6j[3],_6j[4],_6j[5],[0,_4s,[0,_4i,[4,_6f]]],_6j[7]];}));return new F(function(){return A(_5i,[_]);});};case 13:return function(_6k,_){var _6l=E(_51)[1],_6m=takeMVar(_6l),_6n=_6m,_=putMVar(_6l,new T(function(){var _6o=E(_6n);return [0,_6o[1],_6o[2],_6o[3],_6o[4],_6o[5],[0,_4s,[0,_4h,[4,_6k]]],_6o[7]];}));return new F(function(){return A(_5i,[_]);});};case 14:return function(_6p,_){var _6q=E(_51)[1],_6r=takeMVar(_6q),_6s=_6r,_=putMVar(_6q,new T(function(){var _6t=E(_6s);return [0,_6t[1],_6t[2],_6t[3],_6t[4],_6t[5],[0,_4s,[0,_4g,[4,_6p]]],_6t[7]];}));return new F(function(){return A(_5i,[_]);});};default:return E(_52);}},_6u=[0,_4n,_5g],_6v=function(_6w,_6x,_){var _6y=jsCreateTextNode(toJSStr(E(_6w))),_6z=_6y,_6A=jsAppendChild(_6z,E(_6x)[1]);return [0,_6z];},_6B=0,_6C=function(_6D,_6E,_6F,_6G){return new F(function(){return A(_6D,[function(_){var _6H=jsSetAttr(E(_6E)[1],toJSStr(E(_6F)),toJSStr(E(_6G)));return _6B;}]);});},_6I=[0,112],_6J=function(_6K){var _6L=new T(function(){return E(E(_6K)[2]);});return function(_6M,_){return [0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_6L)[1],_9)),new T(function(){return E(E(_6K)[1]);},1)));})],new T(function(){var _6N=E(_6K);return [0,_6N[1],new T(function(){return [0,E(_6L)[1]+1|0];}),_6N[3],_6N[4],_6N[5],_6N[6],_6N[7]];})];};},_6O=new T(function(){return B(unCStr("id"));}),_6P=function(_6Q){return E(_6Q);},_6R=new T(function(){return B(unCStr("noid"));}),_6S=function(_6T,_){return _6T;},_6U=function(_6V,_6W,_){var _6X=jsFind(toJSStr(E(_6W))),_6Y=_6X,_6Z=E(_6Y);if(!_6Z[0]){var _70=E(_51)[1],_71=takeMVar(_70),_72=_71,_73=B(A(_6V,[_72,_])),_74=_73,_75=E(_74),_=putMVar(_70,_75[2]);return E(_75[1])[2];}else{var _76=E(_6Z[1]),_77=jsClearChildren(_76[1]),_78=E(_51)[1],_79=takeMVar(_78),_7a=_79,_7b=B(A(_6V,[_7a,_])),_7c=_7b,_7d=E(_7c),_7e=E(_7d[1]),_=putMVar(_78,_7d[2]),_7f=B(A(_7e[1],[_76,_])),_7g=_7f;return _7e[2];}},_7h=new T(function(){return B(unCStr("span"));}),_7i=function(_7j,_7k,_7l,_){var _7m=jsCreateElem(toJSStr(E(_7h))),_7n=_7m,_7o=jsAppendChild(_7n,E(_7l)[1]),_7p=[0,_7n],_7q=B(A(_7j,[_7k,_7p,_])),_7r=_7q;return _7p;},_7s=function(_7t){return E(_7t);},_7u=function(_7v,_7w,_7x,_){var _7y=B(A(_6J,[_7x,_7x,_])),_7z=_7y,_7A=E(_7z),_7B=_7A[1],_7C=E(_7A[2]),_7D=_7C[2],_7E=E(_7C[4]),_7F=B(A(_7v,[[0,_7C[1],_7D,_7C[3],[0,function(_){return new F(function(){return _6U(function(_7G,_){var _7H=B(A(_7v,[new T(function(){var _7I=E(_7G);return [0,_7I[1],_7D,_7I[3],_7I[4],_7I[5],_7I[6],_7I[7]];}),_])),_7J=_7H;return [0,[0,_6S,E(E(_7J)[1])[2]],_7G];},_6R,_);});},function(_7K,_){var _7L=B(_6U(new T(function(){return B(A(_7w,[_7K]));},1),_7B,_)),_7M=_7L,_7N=E(_7M);return _7N[0]==0?_4O:B(A(_7E[2],[_7N[1],_]));}],_7C[5],_7C[6],_7C[7]],_])),_7O=_7F,_7P=E(_7O),_7Q=_7P[2],_7R=E(_7P[1]),_7S=_7R[1],_7T=E(_7R[2]);if(!_7T[0]){return [0,[0,function(_7U,_){var _7V=B(A(_7S,[_7U,_])),_7W=_7V;if(!E(E(_7x)[5])){var _7X=B(_7i(_7s,_6S,_7U,_)),_7Y=_7X,_7Z=B(A(_6C,[_6P,_7Y,_6O,_7B,_])),_80=_7Z;return _7U;}else{return _7U;}},_4O],new T(function(){var _81=E(_7Q);return [0,_81[1],_81[2],_81[3],_7E,_81[5],_81[6],_81[7]];})];}else{var _82=B(A(_7w,[_7T[1],new T(function(){var _83=E(_7Q);return [0,_83[1],_83[2],_83[3],_7E,_83[5],_83[6],_83[7]];}),_])),_84=_82,_85=E(_84),_86=E(_85[1]),_87=_86[1];return [0,[0,function(_88,_){var _89=B(A(_7S,[_88,_])),_8a=_89;if(!E(E(_7x)[5])){var _8b=B(_7i(_7s,_87,_88,_)),_8c=_8b,_8d=B(A(_6C,[_6P,_8c,_6O,_7B,_])),_8e=_8d;return _88;}else{var _8f=B(A(_87,[_88,_])),_8g=_8f;return _88;}},_86[2]],_85[2]];}},_8h=function(_8i,_8j){switch(E(_8i)[0]){case 0:switch(E(_8j)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_8j)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_8j)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_8j)[0]==3?1:2;}},_8k=new T(function(){return B(unCStr("end of input"));}),_8l=new T(function(){return B(unCStr("unexpected"));}),_8m=new T(function(){return B(unCStr("expecting"));}),_8n=new T(function(){return B(unCStr("unknown parse error"));}),_8o=new T(function(){return B(unCStr("or"));}),_8p=[0,58],_8q=[0,34],_8r=[0,41],_8s=[1,_8r,_9],_8t=function(_8u,_8v,_8w){var _8x=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_8v,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_8w,_9)),_8s));})));},1)));})));}),_8y=E(_8u);return _8y[0]==0?E(_8x):[1,_8q,new T(function(){return B(_e(_8y,new T(function(){return B(unAppCStr("\" ",_8x));},1)));})];},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C[0]){return E(_8B)[0]==0?true:false;}else{var _8D=E(_8B);if(!_8D[0]){return false;}else{if(E(_8C[1])[1]!=E(_8D[1])[1]){return false;}else{_8A=_8C[2];_8B=_8D[2];continue;}}}}},_8E=function(_8F,_8G){return !B(_8z(_8F,_8G))?true:false;},_8H=[0,_8z,_8E],_8I=function(_8J,_8K,_8L){var _8M=E(_8L);if(!_8M[0]){return E(_8K);}else{return new F(function(){return _e(_8K,new T(function(){return B(_e(_8J,new T(function(){return B(_8I(_8J,_8M[1],_8M[2]));},1)));},1));});}},_8N=function(_8O){return E(_8O)[0]==0?false:true;},_8P=new T(function(){return B(unCStr(", "));}),_8Q=function(_8R){var _8S=E(_8R);if(!_8S[0]){return [0];}else{return new F(function(){return _e(_8S[1],new T(function(){return B(_8Q(_8S[2]));},1));});}},_8T=function(_8U,_8V){while(1){var _8W=(function(_8X,_8Y){var _8Z=E(_8Y);if(!_8Z[0]){return [0];}else{var _90=_8Z[1],_91=_8Z[2];if(!B(A(_8X,[_90]))){var _92=_8X;_8V=_91;_8U=_92;return null;}else{return [1,_90,new T(function(){return B(_8T(_8X,_91));})];}}})(_8U,_8V);if(_8W!=null){return _8W;}}},_93=function(_94,_95){var _96=E(_95);return _96[0]==0?[0]:[1,_94,new T(function(){return B(_93(_96[1],_96[2]));})];},_97=function(_98,_99){while(1){var _9a=E(_99);if(!_9a[0]){return E(_98);}else{_98=_9a[1];_99=_9a[2];continue;}}},_9b=function(_9c){switch(E(_9c)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_9d=function(_9e){return E(_9e)[0]==1?true:false;},_9f=function(_9g){return E(_9g)[0]==2?true:false;},_9h=[0,10],_9i=[1,_9h,_9],_9j=function(_9k){return new F(function(){return _e(_9i,_9k);});},_9l=[0,32],_9m=function(_9n){var _9o=E(_9n);switch(_9o[0]){case 0:return E(_9o[1]);case 1:return E(_9o[1]);case 2:return E(_9o[1]);default:return E(_9o[1]);}},_9p=function(_9q){return E(E(_9q)[1]);},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v[0]){return false;}else{if(!B(A(_9p,[_9s,_9t,_9v[1]]))){_9u=_9v[2];continue;}else{return true;}}}},_9w=function(_9x,_9y){var _9z=function(_9A,_9B){while(1){var _9C=(function(_9D,_9E){var _9F=E(_9D);if(!_9F[0]){return [0];}else{var _9G=_9F[1],_9H=_9F[2];if(!B(_9r(_9x,_9G,_9E))){return [1,_9G,new T(function(){return B(_9z(_9H,[1,_9G,_9E]));})];}else{_9A=_9H;var _9I=_9E;_9B=_9I;return null;}}})(_9A,_9B);if(_9C!=null){return _9C;}}};return new F(function(){return _9z(_9y,_9);});},_9J=function(_9K,_9L,_9M,_9N,_9O,_9P){var _9Q=E(_9P);if(!_9Q[0]){return E(_9L);}else{var _9R=new T(function(){var _9S=B(_2q(_9b,_9Q));return [0,_9S[1],_9S[2]];}),_9T=new T(function(){var _9U=B(_2q(_9d,E(_9R)[2]));return [0,_9U[1],_9U[2]];}),_9V=new T(function(){return E(E(_9T)[1]);}),_9W=function(_9X,_9Y){var _9Z=E(_9Y);if(!_9Z[0]){return E(_9X);}else{var _a0=new T(function(){return B(_e(_9K,[1,_9l,new T(function(){return B(_97(_9X,_9Z));})]));}),_a1=B(_9w(_8H,B(_8T(_8N,B(_93(_9X,_9Z))))));if(!_a1[0]){return new F(function(){return _e(_9,[1,_9l,_a0]);});}else{var _a2=_a1[1],_a3=E(_a1[2]);if(!_a3[0]){return new F(function(){return _e(_a2,[1,_9l,_a0]);});}else{return new F(function(){return _e(B(_e(_a2,new T(function(){return B(_e(_8P,new T(function(){return B(_8I(_8P,_a3[1],_a3[2]));},1)));},1))),[1,_9l,_a0]);});}}}},_a4=function(_a5,_a6){var _a7=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_a6))))));if(!_a7[0]){return [0];}else{var _a8=_a7[1],_a9=_a7[2],_aa=E(_a5);return _aa[0]==0?B(_9W(_a8,_a9)):B(_e(_aa,[1,_9l,new T(function(){return B(_9W(_a8,_a9));})]));}},_ab=new T(function(){var _ac=B(_2q(_9f,E(_9T)[2]));return [0,_ac[1],_ac[2]];});return new F(function(){return _8Q(B(_3d(_9j,B(_9w(_8H,B(_8T(_8N,[1,new T(function(){if(!E(_9V)[0]){var _ad=E(E(_9R)[1]);if(!_ad[0]){var _ae=[0];}else{var _af=E(_ad[1]);switch(_af[0]){case 0:var _ag=E(_af[1]),_ah=_ag[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ag]));break;case 1:var _ai=E(_af[1]),_ah=_ai[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ai]));break;case 2:var _aj=E(_af[1]),_ah=_aj[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_aj]));break;default:var _ak=E(_af[1]),_ah=_ak[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ak]));}var _ae=_ah;}var _al=_ae,_am=_al;}else{var _am=[0];}return _am;}),[1,new T(function(){return B(_a4(_9N,_9V));}),[1,new T(function(){return B(_a4(_9M,E(_ab)[1]));}),[1,new T(function(){return B((function(_an){var _ao=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_an))))));return _ao[0]==0?[0]:B(_9W(_ao[1],_ao[2]));})(E(_ab)[2]));}),_9]]]])))))));});}},_ap=[1,_9,_9],_aq=function(_ar,_as){var _at=function(_au,_av){var _aw=E(_au);if(!_aw[0]){return E(_av);}else{var _ax=_aw[1],_ay=E(_av);if(!_ay[0]){return E(_aw);}else{var _az=_ay[1];return B(A(_ar,[_ax,_az]))==2?[1,_az,new T(function(){return B(_at(_aw,_ay[2]));})]:[1,_ax,new T(function(){return B(_at(_aw[2],_ay));})];}}},_aA=function(_aB){var _aC=E(_aB);if(!_aC[0]){return [0];}else{var _aD=E(_aC[2]);return _aD[0]==0?E(_aC):[1,new T(function(){return B(_at(_aC[1],_aD[1]));}),new T(function(){return B(_aA(_aD[2]));})];}},_aE=function(_aF){while(1){var _aG=E(_aF);if(!_aG[0]){return E(new T(function(){return B(_aE(B(_aA(_9))));}));}else{if(!E(_aG[2])[0]){return E(_aG[1]);}else{_aF=B(_aA(_aG));continue;}}}},_aH=new T(function(){return B(_aI(_9));}),_aI=function(_aJ){var _aK=E(_aJ);if(!_aK[0]){return E(_ap);}else{var _aL=_aK[1],_aM=E(_aK[2]);if(!_aM[0]){return [1,_aK,_9];}else{var _aN=_aM[1],_aO=_aM[2];if(B(A(_ar,[_aL,_aN]))==2){return new F(function(){return (function(_aP,_aQ,_aR){while(1){var _aS=(function(_aT,_aU,_aV){var _aW=E(_aV);if(!_aW[0]){return [1,[1,_aT,_aU],_aH];}else{var _aX=_aW[1];if(B(A(_ar,[_aT,_aX]))==2){_aP=_aX;var _aY=[1,_aT,_aU];_aR=_aW[2];_aQ=_aY;return null;}else{return [1,[1,_aT,_aU],new T(function(){return B(_aI(_aW));})];}}})(_aP,_aQ,_aR);if(_aS!=null){return _aS;}}})(_aN,[1,_aL,_9],_aO);});}else{return new F(function(){return (function(_aZ,_b0,_b1){while(1){var _b2=(function(_b3,_b4,_b5){var _b6=E(_b5);if(!_b6[0]){return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),_aH];}else{var _b7=_b6[1],_b8=_b6[2];switch(B(A(_ar,[_b3,_b7]))){case 0:_aZ=_b7;_b0=function(_b9){return new F(function(){return A(_b4,[[1,_b3,_b9]]);});};_b1=_b8;return null;case 1:_aZ=_b7;_b0=function(_ba){return new F(function(){return A(_b4,[[1,_b3,_ba]]);});};_b1=_b8;return null;default:return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),new T(function(){return B(_aI(_b6));})];}}})(_aZ,_b0,_b1);if(_b2!=null){return _b2;}}})(_aN,function(_bb){return [1,_aL,_bb];},_aO);});}}}};return new F(function(){return _aE(B(_aI(_as)));});},_bc=function(_bd,_be,_bf,_bg){return new F(function(){return _e(B(_8t(_bd,_be,_bf)),[1,_8p,new T(function(){return B(_9J(_8o,_8n,_8m,_8l,_8k,B(_aq(_8h,_bg))));})]);});},_bh=function(_bi){var _bj=E(_bi),_bk=E(_bj[1]);return new F(function(){return _bc(_bk[1],_bk[2],_bk[3],_bj[2]);});},_bl=function(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bt,_bu){return new F(function(){return _23(function(_bv,_bw){return new F(function(){return _e(B(_3l(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bv)),_bw);});},_bt,_bu);});},_bx=function(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bF,_bG,_bH){return new F(function(){return _e(B(_3l(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bG)),_bH);});},_bI=function(_bJ,_bK,_bL,_bM,_bN,_bO,_bP){return [0,function(_bQ,_44,_45){return new F(function(){return _bx(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_bQ,_44,_45);});},function(_45){return new F(function(){return _3l(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_45);});},function(_44,_45){return new F(function(){return _bl(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_44,_45);});}];},_bR=new T(function(){return B(unCStr(" . "));}),_bS=new T(function(){return B(unCStr(" \u2234 "));}),_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW,_bX,_bY,_bZ){var _c0=B(_3d(new T(function(){return B(_bT(_bW));}),B(_9w(_bX,_bY))));if(!_c0[0]){return new F(function(){return _e(_bS,new T(function(){return B(A(_bT,[_bW,_bZ]));},1));});}else{return new F(function(){return _e(B(_3a([1,_c0[1],new T(function(){return B(_3h(_bR,_c0[2]));})])),new T(function(){return B(_e(_bS,new T(function(){return B(A(_bT,[_bW,_bZ]));},1)));},1));});}},_c1=2,_c2=function(_c3,_){return [0,[0,_6S,[1,_c3]],_c3];},_c4=function(_c5){return function(_c6,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _c7=E(_c5);return B(_e(B(_F(0,E(_c7[2])[1],_9)),_c7[1]));})]]],_c6];};},_c8=function(_c9,_){return new F(function(){return _7u(_c2,_c4,_c9,_);});},_ca=function(_cb){return function(_cc,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _cd=E(_cb);return B(_e(B(_F(0,E(_cd[2])[1],_9)),_cd[1]));})]]],_cc];};},_ce=function(_c9,_){return new F(function(){return _7u(_c2,_ca,_c9,_);});},_cf=function(_cg){return function(_ch,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _ci=E(_cg);return B(_e(B(_F(0,E(_ci[2])[1],_9)),_ci[1]));})]]],_ch];};},_cj=function(_c9,_){return new F(function(){return _7u(_c2,_cf,_c9,_);});},_ck=new T(function(){return B(unCStr("rslt"));}),_cl=new T(function(){return B(unCStr("root"));}),_cm=new T(function(){return B(unCStr("analysis"));}),_cn=new T(function(){return B(unCStr("class"));}),_co=new T(function(){return B(unCStr("invalid"));}),_cp=function(_c9,_){return new F(function(){return _7i(_6v,_co,_c9,_);});},_cq=[1,_6B],_cr=[0,_cp,_cq],_cs=function(_ct,_){return [0,_cr,_ct];},_cu=new T(function(){return B(unCStr("lined"));}),_cv=new T(function(){return B(unCStr("span"));}),_cw=function(_cx,_cy,_cz,_cA,_){var _cB=B(A(_cz,[_cA,_])),_cC=_cB,_cD=E(_cC),_cE=E(_cD[1]),_cF=_cE[1];return [0,[0,function(_cG,_){var _cH=jsFind(toJSStr(E(_cx))),_cI=_cH,_cJ=E(_cI);if(!_cJ[0]){return _cG;}else{var _cK=_cJ[1];switch(E(_cy)){case 0:var _cL=B(A(_cF,[_cK,_])),_cM=_cL;return _cG;case 1:var _cN=E(_cK),_cO=_cN[1],_cP=jsGetChildren(_cO),_cQ=_cP,_cR=E(_cQ);if(!_cR[0]){var _cS=B(A(_cF,[_cN,_])),_cT=_cS;return _cG;}else{var _cU=jsCreateElem(toJSStr(E(_cv))),_cV=_cU,_cW=jsAddChildBefore(_cV,_cO,E(_cR[1])[1]),_cX=B(A(_cF,[[0,_cV],_])),_cY=_cX;return _cG;}break;default:var _cZ=E(_cK),_d0=jsClearChildren(_cZ[1]),_d1=B(A(_cF,[_cZ,_])),_d2=_d1;return _cG;}}},_cE[2]],_cD[2]];},_d3=function(_d4,_d5){while(1){var _d6=E(_d4);if(!_d6[0]){return E(_d5)[0]==0?1:0;}else{var _d7=E(_d5);if(!_d7[0]){return 2;}else{var _d8=E(_d6[1])[1],_d9=E(_d7[1])[1];if(_d8!=_d9){return _d8>_d9?2:0;}else{_d4=_d6[2];_d5=_d7[2];continue;}}}}},_da=new T(function(){return B(_e(_9,_9));}),_db=function(_dc,_dd,_de,_df,_dg,_dh,_di,_dj){var _dk=[0,_dc,_dd,_de],_dl=function(_dm){var _dn=E(_df);if(!_dn[0]){var _do=E(_dj);if(!_do[0]){switch(B(_d3(_dc,_dg))){case 0:return [0,[0,_dg,_dh,_di],_9];case 1:return _dd>=_dh?_dd!=_dh?[0,_dk,_9]:_de>=_di?_de!=_di?[0,_dk,_9]:[0,_dk,_da]:[0,[0,_dg,_dh,_di],_9]:[0,[0,_dg,_dh,_di],_9];default:return [0,_dk,_9];}}else{return [0,[0,_dg,_dh,_di],_do];}}else{switch(B(_d3(_dc,_dg))){case 0:return [0,[0,_dg,_dh,_di],_dj];case 1:return _dd>=_dh?_dd!=_dh?[0,_dk,_dn]:_de>=_di?_de!=_di?[0,_dk,_dn]:[0,_dk,new T(function(){return B(_e(_dn,_dj));})]:[0,[0,_dg,_dh,_di],_dj]:[0,[0,_dg,_dh,_di],_dj];default:return [0,_dk,_dn];}}};if(!E(_dj)[0]){var _dp=E(_df);return _dp[0]==0?B(_dl(_)):[0,_dk,_dp];}else{return new F(function(){return _dl(_);});}},_dq=function(_dr,_ds){while(1){var _dt=E(_dr);if(!_dt[0]){return E(_ds);}else{_dr=_dt[2];var _du=[1,_dt[1],_ds];_ds=_du;continue;}}},_dv=new T(function(){return B(_dq(_9,_9));}),_dw=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_dx=new T(function(){return B(err(_dw));}),_dy=function(_dz,_dA,_dB,_dC,_dD){var _dE=function(_dF,_dG,_dH){var _dI=[1,_dG,_dF];return new F(function(){return A(_dz,[_dH,new T(function(){var _dJ=E(_dF);return function(_dK,_dL,_dM){return new F(function(){return _dE(_dI,_dK,_dL);});};}),_dC,_dx,function(_dN){return new F(function(){return A(_dB,[new T(function(){return B(_dq(_dI,_9));}),_dH,new T(function(){var _dO=E(E(_dH)[2]),_dP=E(_dN),_dQ=E(_dP[1]),_dR=B(_db(_dQ[1],_dQ[2],_dQ[3],_dP[2],_dO[1],_dO[2],_dO[3],_9));return [0,E(_dR[1]),_dR[2]];})]);});}]);});};return new F(function(){return A(_dz,[_dA,function(_dS,_dT,_dU){return new F(function(){return _dE(_9,_dS,_dT);});},_dC,_dx,function(_dV){return new F(function(){return A(_dD,[_dv,_dA,new T(function(){var _dW=E(E(_dA)[2]),_dX=E(_dV),_dY=E(_dX[1]),_dZ=B(_db(_dY[1],_dY[2],_dY[3],_dX[2],_dW[1],_dW[2],_dW[3],_9));return [0,E(_dZ[1]),_dZ[2]];})]);});}]);});},_e0=function(_e1,_e2){var _e3=E(_e1),_e4=E(_e3[1]),_e5=E(_e2),_e6=E(_e5[1]),_e7=B(_db(_e4[1],_e4[2],_e4[3],_e3[2],_e6[1],_e6[2],_e6[3],_e5[2]));return [0,E(_e7[1]),_e7[2]];},_e8=function(_e9,_ea,_eb,_ec,_ed,_ee){var _ef=function(_eg,_eh,_ei,_ej,_ek){return new F(function(){return _dy(_e9,_eh,function(_el,_em,_en){return new F(function(){return A(_ei,[[1,_eg,_el],_em,new T(function(){var _eo=E(E(_em)[2]),_ep=E(_en),_eq=E(_ep[1]),_er=B(_db(_eq[1],_eq[2],_eq[3],_ep[2],_eo[1],_eo[2],_eo[3],_9));return [0,E(_er[1]),_er[2]];})]);});},_ej,function(_es,_et,_eu){return new F(function(){return A(_ek,[[1,_eg,_es],_et,new T(function(){var _ev=E(E(_et)[2]),_ew=E(_eu),_ex=E(_ew[1]),_ey=B(_db(_ex[1],_ex[2],_ex[3],_ew[2],_ev[1],_ev[2],_ev[3],_9));return [0,E(_ey[1]),_ey[2]];})]);});});});};return new F(function(){return A(_e9,[_ea,function(_ez,_eA,_eB){return new F(function(){return _ef(_ez,_eA,_eb,_ec,function(_eC,_eD,_eE){return new F(function(){return A(_eb,[_eC,_eD,new T(function(){return B(_e0(_eB,_eE));})]);});});});},_ec,function(_eF,_eG,_eH){return new F(function(){return _ef(_eF,_eG,_eb,_ec,function(_eI,_eJ,_eK){return new F(function(){return A(_ed,[_eI,_eJ,new T(function(){return B(_e0(_eH,_eK));})]);});});});},_ee]);});},_eL=function(_eM,_eN,_eO,_eP,_eQ){var _eR=function(_eS,_eT){return new F(function(){return A(_eM,[_eT,new T(function(){var _eU=E(_eS);return function(_eV,_eW,_eX){return new F(function(){return _eR(_9,_eW);});};}),_eP,_dx,function(_eY){return new F(function(){return A(_eO,[_6B,_eT,new T(function(){var _eZ=E(E(_eT)[2]),_f0=E(_eY),_f1=E(_f0[1]),_f2=B(_db(_f1[1],_f1[2],_f1[3],_f0[2],_eZ[1],_eZ[2],_eZ[3],_9));return [0,E(_f2[1]),_f2[2]];})]);});}]);});};return new F(function(){return A(_eM,[_eN,function(_f3,_f4,_f5){return new F(function(){return _eR(_9,_f4);});},_eP,_dx,function(_f6){return new F(function(){return A(_eQ,[_6B,_eN,new T(function(){var _f7=E(E(_eN)[2]),_f8=E(_f6),_f9=E(_f8[1]),_fa=B(_db(_f9[1],_f9[2],_f9[3],_f8[2],_f7[1],_f7[2],_f7[3],_9));return [0,E(_fa[1]),_fa[2]];})]);});}]);});},_fb=function(_fc,_fd,_fe,_ff,_fg,_fh,_fi){var _fj=function(_fk,_fl,_fm,_fn,_fo){var _fp=[1,_fk,_9],_fq=function(_fr,_fs,_ft,_fu){return new F(function(){return _fb(_fc,_fd,_fr,function(_fv,_fw,_fx){return new F(function(){return A(_fs,[[1,_fk,_fv],_fw,new T(function(){var _fy=E(E(_fw)[2]),_fz=E(_fx),_fA=E(_fz[1]),_fB=B(_db(_fA[1],_fA[2],_fA[3],_fz[2],_fy[1],_fy[2],_fy[3],_9));return [0,E(_fB[1]),_fB[2]];})]);});},_ft,function(_fC,_fD,_fE){return new F(function(){return A(_fu,[[1,_fk,_fC],_fD,new T(function(){var _fF=E(E(_fD)[2]),_fG=E(_fE),_fH=E(_fG[1]),_fI=B(_db(_fH[1],_fH[2],_fH[3],_fG[2],_fF[1],_fF[2],_fF[3],_9));return [0,E(_fI[1]),_fI[2]];})]);});},function(_fJ){return new F(function(){return A(_fu,[_fp,_fr,new T(function(){var _fK=E(E(_fr)[2]),_fL=_fK[1],_fM=_fK[2],_fN=_fK[3],_fO=E(_fJ),_fP=E(_fO[1]),_fQ=B(_db(_fP[1],_fP[2],_fP[3],_fO[2],_fL,_fM,_fN,_9)),_fR=E(_fQ[1]),_fS=B(_db(_fR[1],_fR[2],_fR[3],_fQ[2],_fL,_fM,_fN,_9));return [0,E(_fS[1]),_fS[2]];})]);});});});};return new F(function(){return A(_fd,[_fl,function(_fT,_fU,_fV){return new F(function(){return _fq(_fU,_fm,_fn,function(_fW,_fX,_fY){return new F(function(){return A(_fm,[_fW,_fX,new T(function(){return B(_e0(_fV,_fY));})]);});});});},_fn,function(_fZ,_g0,_g1){return new F(function(){return _fq(_g0,_fm,_fn,function(_g2,_g3,_g4){return new F(function(){return A(_fo,[_g2,_g3,new T(function(){return B(_e0(_g1,_g4));})]);});});});},function(_g5){return new F(function(){return A(_fo,[_fp,_fl,new T(function(){var _g6=E(E(_fl)[2]),_g7=E(_g5),_g8=E(_g7[1]),_g9=B(_db(_g8[1],_g8[2],_g8[3],_g7[2],_g6[1],_g6[2],_g6[3],_9));return [0,E(_g9[1]),_g9[2]];})]);});}]);});};return new F(function(){return A(_fc,[_fe,function(_ga,_gb,_gc){return new F(function(){return _fj(_ga,_gb,_ff,_fg,function(_gd,_ge,_gf){return new F(function(){return A(_ff,[_gd,_ge,new T(function(){return B(_e0(_gc,_gf));})]);});});});},_fg,function(_gg,_gh,_gi){return new F(function(){return _fj(_gg,_gh,_ff,_fg,function(_gj,_gk,_gl){return new F(function(){return A(_fh,[_gj,_gk,new T(function(){return B(_e0(_gi,_gl));})]);});});});},_fi]);});},_gm=function(_gn,_go){return new F(function(){return A(_go,[_gn]);});},_gp=[0,34],_gq=[1,_gp,_9],_gr=[0,E(_9)],_gs=[1,_gr,_9],_gt=function(_gu,_gv){var _gw=_gu%_gv;if(_gu<=0){if(_gu>=0){return E(_gw);}else{if(_gv<=0){return E(_gw);}else{var _gx=E(_gw);return _gx==0?0:_gx+_gv|0;}}}else{if(_gv>=0){if(_gu>=0){return E(_gw);}else{if(_gv<=0){return E(_gw);}else{var _gy=E(_gw);return _gy==0?0:_gy+_gv|0;}}}else{var _gz=E(_gw);return _gz==0?0:_gz+_gv|0;}}},_gA=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_gB=new T(function(){return B(err(_gA));}),_gC=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_gD=new T(function(){return B(err(_gC));}),_gE=function(_gF,_gG){while(1){var _gH=E(_gF);if(!_gH[0]){return E(_gD);}else{var _gI=E(_gG);if(!_gI){return E(_gH[1]);}else{_gF=_gH[2];_gG=_gI-1|0;continue;}}}},_gJ=new T(function(){return B(unCStr("ACK"));}),_gK=new T(function(){return B(unCStr("BEL"));}),_gL=new T(function(){return B(unCStr("BS"));}),_gM=new T(function(){return B(unCStr("SP"));}),_gN=[1,_gM,_9],_gO=new T(function(){return B(unCStr("US"));}),_gP=[1,_gO,_gN],_gQ=new T(function(){return B(unCStr("RS"));}),_gR=[1,_gQ,_gP],_gS=new T(function(){return B(unCStr("GS"));}),_gT=[1,_gS,_gR],_gU=new T(function(){return B(unCStr("FS"));}),_gV=[1,_gU,_gT],_gW=new T(function(){return B(unCStr("ESC"));}),_gX=[1,_gW,_gV],_gY=new T(function(){return B(unCStr("SUB"));}),_gZ=[1,_gY,_gX],_h0=new T(function(){return B(unCStr("EM"));}),_h1=[1,_h0,_gZ],_h2=new T(function(){return B(unCStr("CAN"));}),_h3=[1,_h2,_h1],_h4=new T(function(){return B(unCStr("ETB"));}),_h5=[1,_h4,_h3],_h6=new T(function(){return B(unCStr("SYN"));}),_h7=[1,_h6,_h5],_h8=new T(function(){return B(unCStr("NAK"));}),_h9=[1,_h8,_h7],_ha=new T(function(){return B(unCStr("DC4"));}),_hb=[1,_ha,_h9],_hc=new T(function(){return B(unCStr("DC3"));}),_hd=[1,_hc,_hb],_he=new T(function(){return B(unCStr("DC2"));}),_hf=[1,_he,_hd],_hg=new T(function(){return B(unCStr("DC1"));}),_hh=[1,_hg,_hf],_hi=new T(function(){return B(unCStr("DLE"));}),_hj=[1,_hi,_hh],_hk=new T(function(){return B(unCStr("SI"));}),_hl=[1,_hk,_hj],_hm=new T(function(){return B(unCStr("SO"));}),_hn=[1,_hm,_hl],_ho=new T(function(){return B(unCStr("CR"));}),_hp=[1,_ho,_hn],_hq=new T(function(){return B(unCStr("FF"));}),_hr=[1,_hq,_hp],_hs=new T(function(){return B(unCStr("VT"));}),_ht=[1,_hs,_hr],_hu=new T(function(){return B(unCStr("LF"));}),_hv=[1,_hu,_ht],_hw=new T(function(){return B(unCStr("HT"));}),_hx=[1,_hw,_hv],_hy=[1,_gL,_hx],_hz=[1,_gK,_hy],_hA=[1,_gJ,_hz],_hB=new T(function(){return B(unCStr("ENQ"));}),_hC=[1,_hB,_hA],_hD=new T(function(){return B(unCStr("EOT"));}),_hE=[1,_hD,_hC],_hF=new T(function(){return B(unCStr("ETX"));}),_hG=[1,_hF,_hE],_hH=new T(function(){return B(unCStr("STX"));}),_hI=[1,_hH,_hG],_hJ=new T(function(){return B(unCStr("SOH"));}),_hK=[1,_hJ,_hI],_hL=new T(function(){return B(unCStr("NUL"));}),_hM=[1,_hL,_hK],_hN=[0,92],_hO=new T(function(){return B(unCStr("\\DEL"));}),_hP=new T(function(){return B(unCStr("\\a"));}),_hQ=new T(function(){return B(unCStr("\\\\"));}),_hR=new T(function(){return B(unCStr("\\SO"));}),_hS=new T(function(){return B(unCStr("\\r"));}),_hT=new T(function(){return B(unCStr("\\f"));}),_hU=new T(function(){return B(unCStr("\\v"));}),_hV=new T(function(){return B(unCStr("\\n"));}),_hW=new T(function(){return B(unCStr("\\t"));}),_hX=new T(function(){return B(unCStr("\\b"));}),_hY=function(_hZ,_i0){if(_hZ<=127){var _i1=E(_hZ);switch(_i1){case 92:return new F(function(){return _e(_hQ,_i0);});break;case 127:return new F(function(){return _e(_hO,_i0);});break;default:if(_i1<32){var _i2=E(_i1);switch(_i2){case 7:return new F(function(){return _e(_hP,_i0);});break;case 8:return new F(function(){return _e(_hX,_i0);});break;case 9:return new F(function(){return _e(_hW,_i0);});break;case 10:return new F(function(){return _e(_hV,_i0);});break;case 11:return new F(function(){return _e(_hU,_i0);});break;case 12:return new F(function(){return _e(_hT,_i0);});break;case 13:return new F(function(){return _e(_hS,_i0);});break;case 14:return new F(function(){return _e(_hR,new T(function(){var _i3=E(_i0);if(!_i3[0]){var _i4=[0];}else{var _i4=E(E(_i3[1])[1])==72?B(unAppCStr("\\&",_i3)):E(_i3);}return _i4;},1));});break;default:return new F(function(){return _e([1,_hN,new T(function(){var _i5=_i2;return _i5>=0?B(_gE(_hM,_i5)):E(_gB);})],_i0);});}}else{return [1,[0,_i1],_i0];}}}else{return [1,_hN,new T(function(){var _i6=jsShowI(_hZ),_i7=_i6;return B(_e(fromJSStr(_i7),new T(function(){var _i8=E(_i0);if(!_i8[0]){var _i9=[0];}else{var _ia=E(_i8[1])[1];if(_ia<48){var _ib=E(_i8);}else{var _ib=_ia>57?E(_i8):B(unAppCStr("\\&",_i8));}var _ic=_ib,_id=_ic,_i9=_id;}return _i9;},1)));})];}},_ie=new T(function(){return B(unCStr("\\\""));}),_if=function(_ig,_ih){var _ii=E(_ig);if(!_ii[0]){return E(_ih);}else{var _ij=_ii[2],_ik=E(E(_ii[1])[1]);if(_ik==34){return new F(function(){return _e(_ie,new T(function(){return B(_if(_ij,_ih));},1));});}else{return new F(function(){return _hY(_ik,new T(function(){return B(_if(_ij,_ih));}));});}}},_il=function(_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv){var _iw=[0,_iq,_ir,_is];return new F(function(){return A(_im,[new T(function(){return B(A(_in,[_ip]));}),function(_ix){var _iy=E(_ix);if(!_iy[0]){return E(new T(function(){return B(A(_iv,[[0,E(_iw),_gs]]));}));}else{var _iz=E(_iy[1]),_iA=_iz[1],_iB=_iz[2];if(!B(A(_io,[_iA]))){return new F(function(){return A(_iv,[[0,E(_iw),[1,[0,E([1,_gp,new T(function(){return B(_if([1,_iA,_9],_gq));})])],_9]]]);});}else{var _iC=E(_iA);switch(E(_iC[1])){case 9:var _iD=[0,_iq,_ir,(_is+8|0)-B(_gt(_is-1|0,8))|0];break;case 10:var _iD=E([0,_iq,_ir+1|0,1]);break;default:var _iD=E([0,_iq,_ir,_is+1|0]);}var _iE=_iD,_iF=[0,E(_iE),_9],_iG=[0,_iB,E(_iE),E(_it)];return new F(function(){return A(_iu,[_iC,_iG,_iF]);});}}}]);});},_iH=function(_iI,_iJ){return E(_iI)[1]!=E(_iJ)[1];},_iK=function(_iL,_iM){return E(_iL)[1]==E(_iM)[1];},_iN=[0,_iK,_iH],_iO=new T(function(){return B(unCStr(" 	"));}),_iP=function(_iQ){return new F(function(){return _9r(_iN,_iQ,_iO);});},_iR=function(_iS,_iT){return E(_iT);},_iU=function(_iV){return new F(function(){return err(_iV);});},_iW=function(_iX){return E(_iX);},_iY=[0,_gm,_iR,_iW,_iU],_iZ=function(_j0){return E(E(_j0)[3]);},_j1=function(_j2,_j3){var _j4=E(_j3);return _j4[0]==0?B(A(_iZ,[_j2,_4O])):B(A(_iZ,[_j2,[1,[0,_j4[1],_j4[2]]]]));},_j5=function(_j6){return new F(function(){return _j1(_iY,_j6);});},_j7=function(_j8,_j9,_ja,_jb,_jc){var _jd=E(_j8),_je=E(_jd[2]);return new F(function(){return _il(_gm,_j5,_iP,_jd[1],_je[1],_je[2],_je[3],_jd[3],_j9,_jc);});},_jf=function(_jg){return [2,E(E(_jg))];},_jh=function(_ji,_jj){switch(E(_ji)[0]){case 0:switch(E(_jj)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_jj)[0]==1?false:true;case 2:return E(_jj)[0]==2?false:true;default:return E(_jj)[0]==3?false:true;}},_jk=[2,E(_9)],_jl=function(_jm){return new F(function(){return _jh(_jk,_jm);});},_jn=function(_jo,_jp,_jq){var _jr=E(_jq);if(!_jr[0]){return [0,_jo,[1,_jk,new T(function(){return B(_8T(_jl,_jp));})]];}else{var _js=_jr[1],_jt=E(_jr[2]);if(!_jt[0]){var _ju=new T(function(){return [2,E(E(_js))];});return [0,_jo,[1,_ju,new T(function(){return B(_8T(function(_jm){return new F(function(){return _jh(_ju,_jm);});},_jp));})]];}else{var _jv=new T(function(){return [2,E(E(_js))];}),_jw=function(_jx){var _jy=E(_jx);if(!_jy[0]){return [0,_jo,[1,_jv,new T(function(){return B(_8T(function(_jm){return new F(function(){return _jh(_jv,_jm);});},_jp));})]];}else{var _jz=B(_jw(_jy[2]));return [0,_jz[1],[1,new T(function(){return B(_jf(_jy[1]));}),_jz[2]]];}};return new F(function(){return (function(_jA,_jB){var _jC=B(_jw(_jB));return [0,_jC[1],[1,new T(function(){return B(_jf(_jA));}),_jC[2]]];})(_jt[1],_jt[2]);});}}},_jD=function(_jE,_jF){var _jG=E(_jE),_jH=B(_jn(_jG[1],_jG[2],_jF));return [0,E(_jH[1]),_jH[2]];},_jI=function(_jJ,_jK,_jL,_jM,_jN,_jO,_jP){return new F(function(){return A(_jJ,[_jL,_jM,_jN,function(_jQ,_jR,_jS){return new F(function(){return A(_jO,[_jQ,_jR,new T(function(){var _jT=E(_jS),_jU=E(_jT[2]);if(!_jU[0]){var _jV=E(_jT);}else{var _jW=B(_jn(_jT[1],_jU,_jK)),_jV=[0,E(_jW[1]),_jW[2]];}var _jX=_jV;return _jX;})]);});},function(_jY){return new F(function(){return A(_jP,[new T(function(){return B(_jD(_jY,_jK));})]);});}]);});},_jZ=new T(function(){return B(unCStr("digit"));}),_k0=[1,_jZ,_9],_k1=function(_k2){return new F(function(){return _j1(_iY,_k2);});},_k3=function(_k4){var _k5=E(_k4)[1];return _k5<48?false:_k5<=57;},_k6=function(_k7,_k8,_k9,_ka,_kb){var _kc=E(_k7),_kd=E(_kc[2]);return new F(function(){return _il(_gm,_k1,_k3,_kc[1],_kd[1],_kd[2],_kd[3],_kc[3],_k8,_kb);});},_ke=function(_kf,_kg,_kh,_ki,_kj){return new F(function(){return _jI(_k6,_k0,_kf,_kg,_kh,_ki,_kj);});},_kk=function(_kl,_km,_kn,_ko,_kp){return new F(function(){return _e8(_ke,_kl,_km,_kn,_ko,_kp);});},_kq=function(_kr){return [0,_kr,function(_jm){return new F(function(){return _j1(_kr,_jm);});}];},_ks=new T(function(){return B(_kq(_iY));}),_kt=function(_ku,_kv){return function(_kw,_kx,_ky,_kz,_kA){return new F(function(){return _jI(function(_kB,_kC,_kD,_kE,_kF){var _kG=E(_ku),_kH=E(_kB),_kI=E(_kH[2]);return new F(function(){return _il(E(_kG[1])[1],_kG[2],function(_kJ){return new F(function(){return _iK(_kJ,_kv);});},_kH[1],_kI[1],_kI[2],_kI[3],_kH[3],_kC,_kF);});},[1,[1,_gp,new T(function(){return B(_if([1,_kv,_9],_gq));})],_9],_kw,_kx,_ky,_kz,_kA);});};},_kK=[0,44],_kL=new T(function(){return B(_kt(_ks,_kK));}),_kM=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_kN=new T(function(){return B(err(_kM));}),_kO=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kP=new T(function(){return B(err(_kO));}),_kQ=new T(function(){return B(_2L("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_kR=function(_kS,_kT){while(1){var _kU=(function(_kV,_kW){var _kX=E(_kV);switch(_kX[0]){case 0:var _kY=E(_kW);if(!_kY[0]){return [0];}else{_kS=B(A(_kX[1],[_kY[1]]));_kT=_kY[2];return null;}break;case 1:var _kZ=B(A(_kX[1],[_kW])),_l0=_kW;_kS=_kZ;_kT=_l0;return null;case 2:return [0];case 3:return [1,[0,_kX[1],_kW],new T(function(){return B(_kR(_kX[2],_kW));})];default:return E(_kX[1]);}})(_kS,_kT);if(_kU!=null){return _kU;}}},_l1=function(_l2,_l3){var _l4=function(_l5){var _l6=E(_l3);if(_l6[0]==3){return [3,_l6[1],new T(function(){return B(_l1(_l2,_l6[2]));})];}else{var _l7=E(_l2);if(_l7[0]==2){return E(_l6);}else{var _l8=E(_l6);if(_l8[0]==2){return E(_l7);}else{var _l9=function(_la){var _lb=E(_l8);if(_lb[0]==4){return [1,function(_lc){return [4,new T(function(){return B(_e(B(_kR(_l7,_lc)),_lb[1]));})];}];}else{var _ld=E(_l7);if(_ld[0]==1){var _le=_ld[1],_lf=E(_lb);return _lf[0]==0?[1,function(_lg){return new F(function(){return _l1(B(A(_le,[_lg])),_lf);});}]:[1,function(_lh){return new F(function(){return _l1(B(A(_le,[_lh])),new T(function(){return B(A(_lf[1],[_lh]));}));});}];}else{var _li=E(_lb);return _li[0]==0?E(_kQ):[1,function(_lj){return new F(function(){return _l1(_ld,new T(function(){return B(A(_li[1],[_lj]));}));});}];}}},_lk=E(_l7);switch(_lk[0]){case 1:var _ll=E(_l8);if(_ll[0]==4){return [1,function(_lm){return [4,new T(function(){return B(_e(B(_kR(B(A(_lk[1],[_lm])),_lm)),_ll[1]));})];}];}else{return new F(function(){return _l9(_);});}break;case 4:var _ln=_lk[1],_lo=E(_l8);switch(_lo[0]){case 0:return [1,function(_lp){return [4,new T(function(){return B(_e(_ln,new T(function(){return B(_kR(_lo,_lp));},1)));})];}];case 1:return [1,function(_lq){return [4,new T(function(){return B(_e(_ln,new T(function(){return B(_kR(B(A(_lo[1],[_lq])),_lq));},1)));})];}];default:return [4,new T(function(){return B(_e(_ln,_lo[1]));})];}break;default:return new F(function(){return _l9(_);});}}}}},_lr=E(_l2);switch(_lr[0]){case 0:var _ls=E(_l3);if(!_ls[0]){return [0,function(_lt){return new F(function(){return _l1(B(A(_lr[1],[_lt])),new T(function(){return B(A(_ls[1],[_lt]));}));});}];}else{return new F(function(){return _l4(_);});}break;case 3:return [3,_lr[1],new T(function(){return B(_l1(_lr[2],_l3));})];default:return new F(function(){return _l4(_);});}},_lu=[0,41],_lv=[1,_lu,_9],_lw=[0,40],_lx=[1,_lw,_9],_ly=function(_lz,_lA){var _lB=E(_lz);switch(_lB[0]){case 0:return [0,function(_lC){return new F(function(){return _ly(B(A(_lB[1],[_lC])),_lA);});}];case 1:return [1,function(_lD){return new F(function(){return _ly(B(A(_lB[1],[_lD])),_lA);});}];case 2:return [2];case 3:return new F(function(){return _l1(B(A(_lA,[_lB[1]])),new T(function(){return B(_ly(_lB[2],_lA));}));});break;default:var _lE=function(_lF){var _lG=E(_lF);if(!_lG[0]){return [0];}else{var _lH=E(_lG[1]);return new F(function(){return _e(B(_kR(B(A(_lA,[_lH[1]])),_lH[2])),new T(function(){return B(_lE(_lG[2]));},1));});}},_lI=B(_lE(_lB[1]));return _lI[0]==0?[2]:[4,_lI];}},_lJ=[2],_lK=function(_lL){return [3,_lL,_lJ];},_lM=function(_lN,_lO){var _lP=E(_lN);if(!_lP){return new F(function(){return A(_lO,[_6B]);});}else{return [0,function(_lQ){return E(new T(function(){return B(_lM(_lP-1|0,_lO));}));}];}},_lR=function(_lS,_lT,_lU){return function(_lV){return new F(function(){return A(function(_lW,_lX,_lY){while(1){var _lZ=(function(_m0,_m1,_m2){var _m3=E(_m0);switch(_m3[0]){case 0:var _m4=E(_m1);if(!_m4[0]){return E(_lT);}else{_lW=B(A(_m3[1],[_m4[1]]));_lX=_m4[2];var _m5=_m2+1|0;_lY=_m5;return null;}break;case 1:var _m6=B(A(_m3[1],[_m1])),_m7=_m1,_m5=_m2;_lW=_m6;_lX=_m7;_lY=_m5;return null;case 2:return E(_lT);case 3:return function(_m8){return new F(function(){return _lM(_m2,function(_m9){return E(new T(function(){return B(_ly(_m3,_m8));}));});});};default:return function(_ma){return new F(function(){return _ly(_m3,_ma);});};}})(_lW,_lX,_lY);if(_lZ!=null){return _lZ;}}},[new T(function(){return B(A(_lS,[_lK]));}),_lV,0,_lU]);});};},_mb=function(_mc){return new F(function(){return A(_mc,[_9]);});},_md=function(_me,_mf){var _mg=function(_mh){var _mi=E(_mh);if(!_mi[0]){return E(_mb);}else{var _mj=_mi[1];return !B(A(_me,[_mj]))?E(_mb):function(_mk){return [0,function(_ml){return E(new T(function(){return B(A(new T(function(){return B(_mg(_mi[2]));}),[function(_mm){return new F(function(){return A(_mk,[[1,_mj,_mm]]);});}]));}));}];};}};return function(_mn){return new F(function(){return A(_mg,[_mn,_mf]);});};},_mo=[6],_mp=new T(function(){return B(unCStr("valDig: Bad base"));}),_mq=new T(function(){return B(err(_mp));}),_mr=function(_ms,_mt){var _mu=function(_mv,_mw){var _mx=E(_mv);if(!_mx[0]){return function(_my){return new F(function(){return A(_my,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{var _mz=E(_mx[1])[1],_mA=function(_mB){return function(_mC){return [0,function(_mD){return E(new T(function(){return B(A(new T(function(){return B(_mu(_mx[2],function(_mE){return new F(function(){return A(_mw,[[1,_mB,_mE]]);});}));}),[_mC]));}));}];};};switch(E(E(_ms)[1])){case 8:if(48>_mz){return function(_mF){return new F(function(){return A(_mF,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>55){return function(_mG){return new F(function(){return A(_mG,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,_mz-48|0]);});}}break;case 10:if(48>_mz){return function(_mH){return new F(function(){return A(_mH,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>57){return function(_mI){return new F(function(){return A(_mI,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,_mz-48|0]);});}}break;case 16:if(48>_mz){if(97>_mz){if(65>_mz){return function(_mJ){return new F(function(){return A(_mJ,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mK){return new F(function(){return A(_mK,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{if(_mz>102){if(65>_mz){return function(_mL){return new F(function(){return A(_mL,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mM){return new F(function(){return A(_mM,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{return new F(function(){return _mA([0,(_mz-97|0)+10|0]);});}}}else{if(_mz>57){if(97>_mz){if(65>_mz){return function(_mN){return new F(function(){return A(_mN,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mO){return new F(function(){return A(_mO,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{if(_mz>102){if(65>_mz){return function(_mP){return new F(function(){return A(_mP,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{if(_mz>70){return function(_mQ){return new F(function(){return A(_mQ,[new T(function(){return B(A(_mw,[_9]));})]);});};}else{return new F(function(){return _mA([0,(_mz-65|0)+10|0]);});}}}else{return new F(function(){return _mA([0,(_mz-97|0)+10|0]);});}}}else{return new F(function(){return _mA([0,_mz-48|0]);});}}break;default:return E(_mq);}}};return function(_mR){return new F(function(){return A(_mu,[_mR,_6P,function(_mS){var _mT=E(_mS);return _mT[0]==0?[2]:B(A(_mt,[_mT]));}]);});};},_mU=[0,10],_mV=[0,1],_mW=[0,2147483647],_mX=function(_mY,_mZ){while(1){var _n0=E(_mY);if(!_n0[0]){var _n1=_n0[1],_n2=E(_mZ);if(!_n2[0]){var _n3=_n2[1],_n4=addC(_n1,_n3);if(!E(_n4[2])){return [0,_n4[1]];}else{_mY=[1,I_fromInt(_n1)];_mZ=[1,I_fromInt(_n3)];continue;}}else{_mY=[1,I_fromInt(_n1)];_mZ=_n2;continue;}}else{var _n5=E(_mZ);if(!_n5[0]){_mY=_n0;_mZ=[1,I_fromInt(_n5[1])];continue;}else{return [1,I_add(_n0[1],_n5[1])];}}}},_n6=new T(function(){return B(_mX(_mW,_mV));}),_n7=function(_n8){var _n9=E(_n8);if(!_n9[0]){var _na=E(_n9[1]);return _na==(-2147483648)?E(_n6):[0, -_na];}else{return [1,I_negate(_n9[1])];}},_nb=[0,10],_nc=[0,0],_nd=function(_ne){return [0,_ne];},_nf=function(_ng,_nh){while(1){var _ni=E(_ng);if(!_ni[0]){var _nj=_ni[1],_nk=E(_nh);if(!_nk[0]){var _nl=_nk[1];if(!(imul(_nj,_nl)|0)){return [0,imul(_nj,_nl)|0];}else{_ng=[1,I_fromInt(_nj)];_nh=[1,I_fromInt(_nl)];continue;}}else{_ng=[1,I_fromInt(_nj)];_nh=_nk;continue;}}else{var _nm=E(_nh);if(!_nm[0]){_ng=_ni;_nh=[1,I_fromInt(_nm[1])];continue;}else{return [1,I_mul(_ni[1],_nm[1])];}}}},_nn=function(_no,_np,_nq){while(1){var _nr=E(_nq);if(!_nr[0]){return E(_np);}else{var _ns=B(_mX(B(_nf(_np,_no)),B(_nd(E(_nr[1])[1]))));_nq=_nr[2];_np=_ns;continue;}}},_nt=function(_nu){var _nv=new T(function(){return B(_l1(B(_l1([0,function(_nw){return E(E(_nw)[1])==45?[1,B(_mr(_mU,function(_nx){return new F(function(){return A(_nu,[[1,new T(function(){return B(_n7(B(_nn(_nb,_nc,_nx))));})]]);});}))]:[2];}],[0,function(_ny){return E(E(_ny)[1])==43?[1,B(_mr(_mU,function(_nz){return new F(function(){return A(_nu,[[1,new T(function(){return B(_nn(_nb,_nc,_nz));})]]);});}))]:[2];}])),new T(function(){return [1,B(_mr(_mU,function(_nA){return new F(function(){return A(_nu,[[1,new T(function(){return B(_nn(_nb,_nc,_nA));})]]);});}))];})));});return new F(function(){return _l1([0,function(_nB){return E(E(_nB)[1])==101?E(_nv):[2];}],[0,function(_nC){return E(E(_nC)[1])==69?E(_nv):[2];}]);});},_nD=function(_nE){return new F(function(){return A(_nE,[_4O]);});},_nF=function(_nG){return new F(function(){return A(_nG,[_4O]);});},_nH=function(_nI){return function(_nJ){return E(E(_nJ)[1])==46?[1,B(_mr(_mU,function(_nK){return new F(function(){return A(_nI,[[1,_nK]]);});}))]:[2];};},_nL=function(_nM){return [0,B(_nH(_nM))];},_nN=function(_nO){return new F(function(){return _mr(_mU,function(_nP){return [1,B(_lR(_nL,_nD,function(_nQ){return [1,B(_lR(_nt,_nF,function(_nR){return new F(function(){return A(_nO,[[5,[1,_nP,_nQ,_nR]]]);});}))];}))];});});},_nS=function(_nT){return [1,B(_nN(_nT))];},_nU=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_nV=function(_nW){return new F(function(){return _9r(_iN,_nW,_nU);});},_nX=[0,8],_nY=[0,16],_nZ=function(_o0){var _o1=function(_o2){return new F(function(){return A(_o0,[[5,[0,_nX,_o2]]]);});},_o3=function(_o4){return new F(function(){return A(_o0,[[5,[0,_nY,_o4]]]);});};return function(_o5){return E(E(_o5)[1])==48?E([0,function(_o6){switch(E(E(_o6)[1])){case 79:return [1,B(_mr(_nX,_o1))];case 88:return [1,B(_mr(_nY,_o3))];case 111:return [1,B(_mr(_nX,_o1))];case 120:return [1,B(_mr(_nY,_o3))];default:return [2];}}]):[2];};},_o7=function(_o8){return [0,B(_nZ(_o8))];},_o9=true,_oa=function(_ob){var _oc=new T(function(){return B(A(_ob,[_nX]));}),_od=new T(function(){return B(A(_ob,[_nY]));});return function(_oe){switch(E(E(_oe)[1])){case 79:return E(_oc);case 88:return E(_od);case 111:return E(_oc);case 120:return E(_od);default:return [2];}};},_of=function(_og){return [0,B(_oa(_og))];},_oh=[0,92],_oi=function(_oj){return new F(function(){return A(_oj,[_mU]);});},_ok=function(_ol){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_ol,_9));}))));});},_om=function(_on){var _oo=E(_on);return _oo[0]==0?E(_oo[1]):I_toInt(_oo[1]);},_op=function(_oq,_or){var _os=E(_oq);if(!_os[0]){var _ot=_os[1],_ou=E(_or);return _ou[0]==0?_ot<=_ou[1]:I_compareInt(_ou[1],_ot)>=0;}else{var _ov=_os[1],_ow=E(_or);return _ow[0]==0?I_compareInt(_ov,_ow[1])<=0:I_compare(_ov,_ow[1])<=0;}},_ox=function(_oy){return [2];},_oz=function(_oA){var _oB=E(_oA);if(!_oB[0]){return E(_ox);}else{var _oC=_oB[1],_oD=E(_oB[2]);return _oD[0]==0?E(_oC):function(_oE){return new F(function(){return _l1(B(A(_oC,[_oE])),new T(function(){return B(A(new T(function(){return B(_oz(_oD));}),[_oE]));}));});};}},_oF=function(_oG){return [2];},_oH=function(_oI,_oJ){var _oK=function(_oL,_oM){var _oN=E(_oL);if(!_oN[0]){return function(_oO){return new F(function(){return A(_oO,[_oI]);});};}else{var _oP=E(_oM);return _oP[0]==0?E(_oF):E(_oN[1])[1]!=E(_oP[1])[1]?E(_oF):function(_oQ){return [0,function(_oR){return E(new T(function(){return B(A(new T(function(){return B(_oK(_oN[2],_oP[2]));}),[_oQ]));}));}];};}};return function(_oS){return new F(function(){return A(_oK,[_oI,_oS,_oJ]);});};},_oT=new T(function(){return B(unCStr("SOH"));}),_oU=[0,1],_oV=function(_oW){return [1,B(_oH(_oT,function(_oX){return E(new T(function(){return B(A(_oW,[_oU]));}));}))];},_oY=new T(function(){return B(unCStr("SO"));}),_oZ=[0,14],_p0=function(_p1){return [1,B(_oH(_oY,function(_p2){return E(new T(function(){return B(A(_p1,[_oZ]));}));}))];},_p3=function(_p4){return [1,B(_lR(_oV,_p0,_p4))];},_p5=new T(function(){return B(unCStr("NUL"));}),_p6=[0,0],_p7=function(_p8){return [1,B(_oH(_p5,function(_p9){return E(new T(function(){return B(A(_p8,[_p6]));}));}))];},_pa=new T(function(){return B(unCStr("STX"));}),_pb=[0,2],_pc=function(_pd){return [1,B(_oH(_pa,function(_pe){return E(new T(function(){return B(A(_pd,[_pb]));}));}))];},_pf=new T(function(){return B(unCStr("ETX"));}),_pg=[0,3],_ph=function(_pi){return [1,B(_oH(_pf,function(_pj){return E(new T(function(){return B(A(_pi,[_pg]));}));}))];},_pk=new T(function(){return B(unCStr("EOT"));}),_pl=[0,4],_pm=function(_pn){return [1,B(_oH(_pk,function(_po){return E(new T(function(){return B(A(_pn,[_pl]));}));}))];},_pp=new T(function(){return B(unCStr("ENQ"));}),_pq=[0,5],_pr=function(_ps){return [1,B(_oH(_pp,function(_pt){return E(new T(function(){return B(A(_ps,[_pq]));}));}))];},_pu=new T(function(){return B(unCStr("ACK"));}),_pv=[0,6],_pw=function(_px){return [1,B(_oH(_pu,function(_py){return E(new T(function(){return B(A(_px,[_pv]));}));}))];},_pz=new T(function(){return B(unCStr("BEL"));}),_pA=[0,7],_pB=function(_pC){return [1,B(_oH(_pz,function(_pD){return E(new T(function(){return B(A(_pC,[_pA]));}));}))];},_pE=new T(function(){return B(unCStr("BS"));}),_pF=[0,8],_pG=function(_pH){return [1,B(_oH(_pE,function(_pI){return E(new T(function(){return B(A(_pH,[_pF]));}));}))];},_pJ=new T(function(){return B(unCStr("HT"));}),_pK=[0,9],_pL=function(_pM){return [1,B(_oH(_pJ,function(_pN){return E(new T(function(){return B(A(_pM,[_pK]));}));}))];},_pO=new T(function(){return B(unCStr("LF"));}),_pP=[0,10],_pQ=function(_pR){return [1,B(_oH(_pO,function(_pS){return E(new T(function(){return B(A(_pR,[_pP]));}));}))];},_pT=new T(function(){return B(unCStr("VT"));}),_pU=[0,11],_pV=function(_pW){return [1,B(_oH(_pT,function(_pX){return E(new T(function(){return B(A(_pW,[_pU]));}));}))];},_pY=new T(function(){return B(unCStr("FF"));}),_pZ=[0,12],_q0=function(_q1){return [1,B(_oH(_pY,function(_q2){return E(new T(function(){return B(A(_q1,[_pZ]));}));}))];},_q3=new T(function(){return B(unCStr("CR"));}),_q4=[0,13],_q5=function(_q6){return [1,B(_oH(_q3,function(_q7){return E(new T(function(){return B(A(_q6,[_q4]));}));}))];},_q8=new T(function(){return B(unCStr("SI"));}),_q9=[0,15],_qa=function(_qb){return [1,B(_oH(_q8,function(_qc){return E(new T(function(){return B(A(_qb,[_q9]));}));}))];},_qd=new T(function(){return B(unCStr("DLE"));}),_qe=[0,16],_qf=function(_qg){return [1,B(_oH(_qd,function(_qh){return E(new T(function(){return B(A(_qg,[_qe]));}));}))];},_qi=new T(function(){return B(unCStr("DC1"));}),_qj=[0,17],_qk=function(_ql){return [1,B(_oH(_qi,function(_qm){return E(new T(function(){return B(A(_ql,[_qj]));}));}))];},_qn=new T(function(){return B(unCStr("DC2"));}),_qo=[0,18],_qp=function(_qq){return [1,B(_oH(_qn,function(_qr){return E(new T(function(){return B(A(_qq,[_qo]));}));}))];},_qs=new T(function(){return B(unCStr("DC3"));}),_qt=[0,19],_qu=function(_qv){return [1,B(_oH(_qs,function(_qw){return E(new T(function(){return B(A(_qv,[_qt]));}));}))];},_qx=new T(function(){return B(unCStr("DC4"));}),_qy=[0,20],_qz=function(_qA){return [1,B(_oH(_qx,function(_qB){return E(new T(function(){return B(A(_qA,[_qy]));}));}))];},_qC=new T(function(){return B(unCStr("NAK"));}),_qD=[0,21],_qE=function(_qF){return [1,B(_oH(_qC,function(_qG){return E(new T(function(){return B(A(_qF,[_qD]));}));}))];},_qH=new T(function(){return B(unCStr("SYN"));}),_qI=[0,22],_qJ=function(_qK){return [1,B(_oH(_qH,function(_qL){return E(new T(function(){return B(A(_qK,[_qI]));}));}))];},_qM=new T(function(){return B(unCStr("ETB"));}),_qN=[0,23],_qO=function(_qP){return [1,B(_oH(_qM,function(_qQ){return E(new T(function(){return B(A(_qP,[_qN]));}));}))];},_qR=new T(function(){return B(unCStr("CAN"));}),_qS=[0,24],_qT=function(_qU){return [1,B(_oH(_qR,function(_qV){return E(new T(function(){return B(A(_qU,[_qS]));}));}))];},_qW=new T(function(){return B(unCStr("EM"));}),_qX=[0,25],_qY=function(_qZ){return [1,B(_oH(_qW,function(_r0){return E(new T(function(){return B(A(_qZ,[_qX]));}));}))];},_r1=new T(function(){return B(unCStr("SUB"));}),_r2=[0,26],_r3=function(_r4){return [1,B(_oH(_r1,function(_r5){return E(new T(function(){return B(A(_r4,[_r2]));}));}))];},_r6=new T(function(){return B(unCStr("ESC"));}),_r7=[0,27],_r8=function(_r9){return [1,B(_oH(_r6,function(_ra){return E(new T(function(){return B(A(_r9,[_r7]));}));}))];},_rb=new T(function(){return B(unCStr("FS"));}),_rc=[0,28],_rd=function(_re){return [1,B(_oH(_rb,function(_rf){return E(new T(function(){return B(A(_re,[_rc]));}));}))];},_rg=new T(function(){return B(unCStr("GS"));}),_rh=[0,29],_ri=function(_rj){return [1,B(_oH(_rg,function(_rk){return E(new T(function(){return B(A(_rj,[_rh]));}));}))];},_rl=new T(function(){return B(unCStr("RS"));}),_rm=[0,30],_rn=function(_ro){return [1,B(_oH(_rl,function(_rp){return E(new T(function(){return B(A(_ro,[_rm]));}));}))];},_rq=new T(function(){return B(unCStr("US"));}),_rr=[0,31],_rs=function(_rt){return [1,B(_oH(_rq,function(_ru){return E(new T(function(){return B(A(_rt,[_rr]));}));}))];},_rv=new T(function(){return B(unCStr("SP"));}),_rw=[0,32],_rx=function(_ry){return [1,B(_oH(_rv,function(_rz){return E(new T(function(){return B(A(_ry,[_rw]));}));}))];},_rA=new T(function(){return B(unCStr("DEL"));}),_rB=[0,127],_rC=function(_rD){return [1,B(_oH(_rA,function(_rE){return E(new T(function(){return B(A(_rD,[_rB]));}));}))];},_rF=[1,_rC,_9],_rG=[1,_rx,_rF],_rH=[1,_rs,_rG],_rI=[1,_rn,_rH],_rJ=[1,_ri,_rI],_rK=[1,_rd,_rJ],_rL=[1,_r8,_rK],_rM=[1,_r3,_rL],_rN=[1,_qY,_rM],_rO=[1,_qT,_rN],_rP=[1,_qO,_rO],_rQ=[1,_qJ,_rP],_rR=[1,_qE,_rQ],_rS=[1,_qz,_rR],_rT=[1,_qu,_rS],_rU=[1,_qp,_rT],_rV=[1,_qk,_rU],_rW=[1,_qf,_rV],_rX=[1,_qa,_rW],_rY=[1,_q5,_rX],_rZ=[1,_q0,_rY],_s0=[1,_pV,_rZ],_s1=[1,_pQ,_s0],_s2=[1,_pL,_s1],_s3=[1,_pG,_s2],_s4=[1,_pB,_s3],_s5=[1,_pw,_s4],_s6=[1,_pr,_s5],_s7=[1,_pm,_s6],_s8=[1,_ph,_s7],_s9=[1,_pc,_s8],_sa=[1,_p7,_s9],_sb=[1,_p3,_sa],_sc=new T(function(){return B(_oz(_sb));}),_sd=[0,1114111],_se=[0,34],_sf=[0,39],_sg=function(_sh){var _si=new T(function(){return B(A(_sh,[_pA]));}),_sj=new T(function(){return B(A(_sh,[_pF]));}),_sk=new T(function(){return B(A(_sh,[_pK]));}),_sl=new T(function(){return B(A(_sh,[_pP]));}),_sm=new T(function(){return B(A(_sh,[_pU]));}),_sn=new T(function(){return B(A(_sh,[_pZ]));}),_so=new T(function(){return B(A(_sh,[_q4]));});return new F(function(){return _l1([0,function(_sp){switch(E(E(_sp)[1])){case 34:return E(new T(function(){return B(A(_sh,[_se]));}));case 39:return E(new T(function(){return B(A(_sh,[_sf]));}));case 92:return E(new T(function(){return B(A(_sh,[_oh]));}));case 97:return E(_si);case 98:return E(_sj);case 102:return E(_sn);case 110:return E(_sl);case 114:return E(_so);case 116:return E(_sk);case 118:return E(_sm);default:return [2];}}],new T(function(){return B(_l1([1,B(_lR(_of,_oi,function(_sq){return [1,B(_mr(_sq,function(_sr){var _ss=B(_nn(new T(function(){return B(_nd(E(_sq)[1]));}),_nc,_sr));return !B(_op(_ss,_sd))?[2]:B(A(_sh,[new T(function(){var _st=B(_om(_ss));if(_st>>>0>1114111){var _su=B(_ok(_st));}else{var _su=[0,_st];}var _sv=_su,_sw=_sv,_sx=_sw;return _sx;})]));}))];}))],new T(function(){return B(_l1([0,function(_sy){return E(E(_sy)[1])==94?E([0,function(_sz){switch(E(E(_sz)[1])){case 64:return E(new T(function(){return B(A(_sh,[_p6]));}));case 65:return E(new T(function(){return B(A(_sh,[_oU]));}));case 66:return E(new T(function(){return B(A(_sh,[_pb]));}));case 67:return E(new T(function(){return B(A(_sh,[_pg]));}));case 68:return E(new T(function(){return B(A(_sh,[_pl]));}));case 69:return E(new T(function(){return B(A(_sh,[_pq]));}));case 70:return E(new T(function(){return B(A(_sh,[_pv]));}));case 71:return E(_si);case 72:return E(_sj);case 73:return E(_sk);case 74:return E(_sl);case 75:return E(_sm);case 76:return E(_sn);case 77:return E(_so);case 78:return E(new T(function(){return B(A(_sh,[_oZ]));}));case 79:return E(new T(function(){return B(A(_sh,[_q9]));}));case 80:return E(new T(function(){return B(A(_sh,[_qe]));}));case 81:return E(new T(function(){return B(A(_sh,[_qj]));}));case 82:return E(new T(function(){return B(A(_sh,[_qo]));}));case 83:return E(new T(function(){return B(A(_sh,[_qt]));}));case 84:return E(new T(function(){return B(A(_sh,[_qy]));}));case 85:return E(new T(function(){return B(A(_sh,[_qD]));}));case 86:return E(new T(function(){return B(A(_sh,[_qI]));}));case 87:return E(new T(function(){return B(A(_sh,[_qN]));}));case 88:return E(new T(function(){return B(A(_sh,[_qS]));}));case 89:return E(new T(function(){return B(A(_sh,[_qX]));}));case 90:return E(new T(function(){return B(A(_sh,[_r2]));}));case 91:return E(new T(function(){return B(A(_sh,[_r7]));}));case 92:return E(new T(function(){return B(A(_sh,[_rc]));}));case 93:return E(new T(function(){return B(A(_sh,[_rh]));}));case 94:return E(new T(function(){return B(A(_sh,[_rm]));}));case 95:return E(new T(function(){return B(A(_sh,[_rr]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_sc,[_sh]));})));})));}));});},_sA=function(_sB){return new F(function(){return A(_sB,[_6B]);});},_sC=function(_sD){var _sE=E(_sD);if(!_sE[0]){return E(_sA);}else{var _sF=_sE[2],_sG=E(E(_sE[1])[1]);switch(_sG){case 9:return function(_sH){return [0,function(_sI){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sH]));}));}];};case 10:return function(_sJ){return [0,function(_sK){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sJ]));}));}];};case 11:return function(_sL){return [0,function(_sM){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sL]));}));}];};case 12:return function(_sN){return [0,function(_sO){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sN]));}));}];};case 13:return function(_sP){return [0,function(_sQ){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sP]));}));}];};case 32:return function(_sR){return [0,function(_sS){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sR]));}));}];};case 160:return function(_sT){return [0,function(_sU){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sT]));}));}];};default:var _sV=u_iswspace(_sG),_sW=_sV;return E(_sW)==0?E(_sA):function(_sX){return [0,function(_sY){return E(new T(function(){return B(A(new T(function(){return B(_sC(_sF));}),[_sX]));}));}];};}}},_sZ=function(_t0){var _t1=new T(function(){return B(_sZ(_t0));}),_t2=[1,function(_t3){return new F(function(){return A(_sC,[_t3,function(_t4){return E([0,function(_t5){return E(E(_t5)[1])==92?E(_t1):[2];}]);}]);});}];return new F(function(){return _l1([0,function(_t6){return E(E(_t6)[1])==92?E([0,function(_t7){var _t8=E(E(_t7)[1]);switch(_t8){case 9:return E(_t2);case 10:return E(_t2);case 11:return E(_t2);case 12:return E(_t2);case 13:return E(_t2);case 32:return E(_t2);case 38:return E(_t1);case 160:return E(_t2);default:var _t9=u_iswspace(_t8),_ta=_t9;return E(_ta)==0?[2]:E(_t2);}}]):[2];}],[0,function(_tb){var _tc=E(_tb);return E(_tc[1])==92?E(new T(function(){return B(_sg(function(_td){return new F(function(){return A(_t0,[[0,_td,_o9]]);});}));})):B(A(_t0,[[0,_tc,_4y]]));}]);});},_te=function(_tf,_tg){return new F(function(){return _sZ(function(_th){var _ti=E(_th),_tj=E(_ti[1]);if(E(_tj[1])==34){if(!E(_ti[2])){return E(new T(function(){return B(A(_tg,[[1,new T(function(){return B(A(_tf,[_9]));})]]));}));}else{return new F(function(){return _te(function(_tk){return new F(function(){return A(_tf,[[1,_tj,_tk]]);});},_tg);});}}else{return new F(function(){return _te(function(_tl){return new F(function(){return A(_tf,[[1,_tj,_tl]]);});},_tg);});}});});},_tm=new T(function(){return B(unCStr("_\'"));}),_tn=function(_to){var _tp=u_iswalnum(_to),_tq=_tp;return E(_tq)==0?B(_9r(_iN,[0,_to],_tm)):true;},_tr=function(_ts){return new F(function(){return _tn(E(_ts)[1]);});},_tt=new T(function(){return B(unCStr(",;()[]{}`"));}),_tu=new T(function(){return B(unCStr(".."));}),_tv=new T(function(){return B(unCStr("::"));}),_tw=new T(function(){return B(unCStr("->"));}),_tx=[0,64],_ty=[1,_tx,_9],_tz=[0,126],_tA=[1,_tz,_9],_tB=new T(function(){return B(unCStr("=>"));}),_tC=[1,_tB,_9],_tD=[1,_tA,_tC],_tE=[1,_ty,_tD],_tF=[1,_tw,_tE],_tG=new T(function(){return B(unCStr("<-"));}),_tH=[1,_tG,_tF],_tI=[0,124],_tJ=[1,_tI,_9],_tK=[1,_tJ,_tH],_tL=[1,_oh,_9],_tM=[1,_tL,_tK],_tN=[0,61],_tO=[1,_tN,_9],_tP=[1,_tO,_tM],_tQ=[1,_tv,_tP],_tR=[1,_tu,_tQ],_tS=function(_tT){return new F(function(){return _l1([1,function(_tU){return E(_tU)[0]==0?E(new T(function(){return B(A(_tT,[_mo]));})):[2];}],new T(function(){return B(_l1([0,function(_tV){return E(E(_tV)[1])==39?E([0,function(_tW){var _tX=E(_tW);switch(E(_tX[1])){case 39:return [2];case 92:return E(new T(function(){return B(_sg(function(_tY){return [0,function(_tZ){return E(E(_tZ)[1])==39?E(new T(function(){return B(A(_tT,[[0,_tY]]));})):[2];}];}));}));default:return [0,function(_u0){return E(E(_u0)[1])==39?E(new T(function(){return B(A(_tT,[[0,_tX]]));})):[2];}];}}]):[2];}],new T(function(){return B(_l1([0,function(_u1){return E(E(_u1)[1])==34?E(new T(function(){return B(_te(_6P,_tT));})):[2];}],new T(function(){return B(_l1([0,function(_u2){return !B(_9r(_iN,_u2,_tt))?[2]:B(A(_tT,[[2,[1,_u2,_9]]]));}],new T(function(){return B(_l1([0,function(_u3){return !B(_9r(_iN,_u3,_nU))?[2]:[1,B(_md(_nV,function(_u4){var _u5=[1,_u3,_u4];return !B(_9r(_8H,_u5,_tR))?B(A(_tT,[[4,_u5]])):B(A(_tT,[[2,_u5]]));}))];}],new T(function(){return B(_l1([0,function(_u6){var _u7=E(_u6),_u8=_u7[1],_u9=u_iswalpha(_u8),_ua=_u9;return E(_ua)==0?E(_u8)==95?[1,B(_md(_tr,function(_ub){return new F(function(){return A(_tT,[[3,[1,_u7,_ub]]]);});}))]:[2]:[1,B(_md(_tr,function(_uc){return new F(function(){return A(_tT,[[3,[1,_u7,_uc]]]);});}))];}],new T(function(){return [1,B(_lR(_o7,_nS,_tT))];})));})));})));})));})));}));});},_ud=[0,0],_ue=function(_uf,_ug){return function(_uh){return new F(function(){return A(_sC,[_uh,function(_ui){return E(new T(function(){return B(_tS(function(_uj){var _uk=E(_uj);return _uk[0]==2?!B(_3x(_uk[1],_lx))?[2]:E(new T(function(){return B(A(_uf,[_ud,function(_ul){return [1,function(_um){return new F(function(){return A(_sC,[_um,function(_un){return E(new T(function(){return B(_tS(function(_uo){var _up=E(_uo);return _up[0]==2?!B(_3x(_up[1],_lv))?[2]:E(new T(function(){return B(A(_ug,[_ul]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_uq=function(_ur,_us,_ut){var _uu=function(_uv,_uw){return new F(function(){return _l1([1,function(_ux){return new F(function(){return A(_sC,[_ux,function(_uy){return E(new T(function(){return B(_tS(function(_uz){var _uA=E(_uz);if(_uA[0]==4){var _uB=E(_uA[1]);if(!_uB[0]){return new F(function(){return A(_ur,[_uA,_uv,_uw]);});}else{return E(E(_uB[1])[1])==45?E(_uB[2])[0]==0?E([1,function(_uC){return new F(function(){return A(_sC,[_uC,function(_uD){return E(new T(function(){return B(_tS(function(_uE){return new F(function(){return A(_ur,[_uE,_uv,function(_uF){return new F(function(){return A(_uw,[new T(function(){return [0, -E(_uF)[1]];})]);});}]);});}));}));}]);});}]):B(A(_ur,[_uA,_uv,_uw])):B(A(_ur,[_uA,_uv,_uw]));}}else{return new F(function(){return A(_ur,[_uA,_uv,_uw]);});}}));}));}]);});}],new T(function(){return [1,B(_ue(_uu,_uw))];}));});};return new F(function(){return _uu(_us,_ut);});},_uG=function(_uH,_uI){return [2];},_uJ=function(_uK){var _uL=E(_uK);return _uL[0]==0?[1,new T(function(){return B(_nn(new T(function(){return B(_nd(E(_uL[1])[1]));}),_nc,_uL[2]));})]:E(_uL[2])[0]==0?E(_uL[3])[0]==0?[1,new T(function(){return B(_nn(_nb,_nc,_uL[1]));})]:[0]:[0];},_uM=function(_uN){var _uO=E(_uN);if(_uO[0]==5){var _uP=B(_uJ(_uO[1]));return _uP[0]==0?E(_uG):function(_uQ,_uR){return new F(function(){return A(_uR,[new T(function(){return [0,B(_om(_uP[1]))];})]);});};}else{return E(_uG);}},_uS=function(_uT){return [1,function(_uU){return new F(function(){return A(_sC,[_uU,function(_uV){return E([3,_uT,_lJ]);}]);});}];},_uW=new T(function(){return B(_uq(_uM,_ud,_uS));}),_uX=function(_uY){while(1){var _uZ=(function(_v0){var _v1=E(_v0);if(!_v1[0]){return [0];}else{var _v2=_v1[2],_v3=E(_v1[1]);if(!E(_v3[2])[0]){return [1,_v3[1],new T(function(){return B(_uX(_v2));})];}else{_uY=_v2;return null;}}})(_uY);if(_uZ!=null){return _uZ;}}},_v4=function(_v5){var _v6=B(_uX(B(_kR(_uW,_v5))));return _v6[0]==0?E(_kN):E(_v6[2])[0]==0?E(_v6[1]):E(_kP);},_v7=function(_v8,_v9,_va,_vb,_vc){var _vd=function(_ve,_vf,_vg){var _vh=function(_vi,_vj,_vk){return new F(function(){return A(_vg,[[0,_v8,new T(function(){return B(_3d(_v4,_vi));})],_vj,new T(function(){var _vl=E(E(_vj)[2]),_vm=E(_vk),_vn=E(_vm[1]),_vo=B(_db(_vn[1],_vn[2],_vn[3],_vm[2],_vl[1],_vl[2],_vl[3],_9));return [0,E(_vo[1]),_vo[2]];})]);});},_vp=function(_vq){return new F(function(){return _vh(_9,_ve,new T(function(){var _vr=E(E(_ve)[2]),_vs=E(_vq),_vt=E(_vs[1]),_vu=B(_db(_vt[1],_vt[2],_vt[3],_vs[2],_vr[1],_vr[2],_vr[3],_9));return [0,E(_vu[1]),_vu[2]];},1));});};return new F(function(){return _fb(_kk,_kL,_ve,function(_vv,_vw,_vx){return new F(function(){return A(_vf,[[0,_v8,new T(function(){return B(_3d(_v4,_vv));})],_vw,new T(function(){var _vy=E(E(_vw)[2]),_vz=E(_vx),_vA=E(_vz[1]),_vB=B(_db(_vA[1],_vA[2],_vA[3],_vz[2],_vy[1],_vy[2],_vy[3],_9));return [0,E(_vB[1]),_vB[2]];})]);});},_vp,_vh,_vp);});};return new F(function(){return _eL(_j7,_v9,function(_vC,_vD,_vE){return new F(function(){return _vd(_vD,_va,function(_vF,_vG,_vH){return new F(function(){return A(_va,[_vF,_vG,new T(function(){return B(_e0(_vE,_vH));})]);});});});},_vb,function(_vI,_vJ,_vK){return new F(function(){return _vd(_vJ,_va,function(_vL,_vM,_vN){return new F(function(){return A(_vc,[_vL,_vM,new T(function(){return B(_e0(_vK,_vN));})]);});});});});});},_vO=new T(function(){return B(unCStr("letter or digit"));}),_vP=[1,_vO,_9],_vQ=function(_vR){var _vS=u_iswalnum(E(_vR)[1]),_vT=_vS;return E(_vT)==0?false:true;},_vU=function(_vV,_vW,_vX,_vY,_vZ){var _w0=E(_vV),_w1=E(_w0[2]);return new F(function(){return _il(_gm,_k1,_vQ,_w0[1],_w1[1],_w1[2],_w1[3],_w0[3],_vW,_vZ);});},_w2=function(_w3,_w4,_w5,_w6,_w7){return new F(function(){return _jI(_vU,_vP,_w3,_w4,_w5,_w6,_w7);});},_w8=function(_w9,_wa,_wb,_wc,_wd){return new F(function(){return _e8(_w2,_w9,function(_we,_wf,_wg){return new F(function(){return _v7(_we,_wf,_wa,_wb,function(_wh,_wi,_wj){return new F(function(){return A(_wa,[_wh,_wi,new T(function(){return B(_e0(_wg,_wj));})]);});});});},_wd,function(_wk,_wl,_wm){return new F(function(){return _v7(_wk,_wl,_wa,_wb,function(_wn,_wo,_wp){return new F(function(){return A(_wc,[_wn,_wo,new T(function(){return B(_e0(_wm,_wp));})]);});});});},_wd);});},_wq=new T(function(){return B(unCStr("SHOW"));}),_wr=[0,_wq,_9],_ws=function(_wt,_wu,_wv,_ww){var _wx=function(_wy){return new F(function(){return A(_ww,[[0,_wt,_wr],_wu,new T(function(){var _wz=E(E(_wu)[2]),_wA=_wz[1],_wB=_wz[2],_wC=_wz[3],_wD=E(_wy),_wE=E(_wD[1]),_wF=B(_db(_wE[1],_wE[2],_wE[3],_wD[2],_wA,_wB,_wC,_9)),_wG=E(_wF[1]),_wH=B(_db(_wG[1],_wG[2],_wG[3],_wF[2],_wA,_wB,_wC,_9));return [0,E(_wH[1]),_wH[2]];})]);});};return new F(function(){return _w8(_wu,function(_wI,_wJ,_wK){return new F(function(){return A(_wv,[[0,_wt,_wI],_wJ,new T(function(){var _wL=E(E(_wJ)[2]),_wM=E(_wK),_wN=E(_wM[1]),_wO=B(_db(_wN[1],_wN[2],_wN[3],_wM[2],_wL[1],_wL[2],_wL[3],_9));return [0,E(_wO[1]),_wO[2]];})]);});},_wx,function(_wP,_wQ,_wR){return new F(function(){return A(_ww,[[0,_wt,_wP],_wQ,new T(function(){var _wS=E(E(_wQ)[2]),_wT=E(_wR),_wU=E(_wT[1]),_wV=B(_db(_wU[1],_wU[2],_wU[3],_wT[2],_wS[1],_wS[2],_wS[3],_9));return [0,E(_wV[1]),_wV[2]];})]);});},_wx);});},_wW=new T(function(){return B(unCStr("sS"));}),_wX=new T(function(){return B(_kq(_iY));}),_wY=[0,58],_wZ=new T(function(){return B(_kt(_wX,_wY));}),_x0=[1,_vO,_9],_x1=function(_x2,_x3,_x4,_x5,_x6,_x7,_x8,_x9,_xa){var _xb=function(_xc){var _xd=new T(function(){var _xe=E(_xc),_xf=B(_jn(_xe[1],_xe[2],_x0));return [0,E(_xf[1]),_xf[2]];});return new F(function(){return A(_wZ,[[0,_x2,E([0,_x3,_x4,_x5]),E(_x6)],_x7,_x8,function(_xg,_xh,_xi){return new F(function(){return A(_x9,[_xg,_xh,new T(function(){return B(_e0(_xd,_xi));})]);});},function(_xj){return new F(function(){return A(_xa,[new T(function(){return B(_e0(_xd,_xj));})]);});}]);});},_xk=E(_x2);if(!_xk[0]){return new F(function(){return _xb([0,E([0,_x3,_x4,_x5]),_gs]);});}else{var _xl=_xk[2],_xm=E(_xk[1]),_xn=_xm[1],_xo=u_iswalnum(_xn),_xp=_xo;if(!E(_xp)){return new F(function(){return _xb([0,E([0,_x3,_x4,_x5]),[1,[0,E([1,_gp,new T(function(){return B(_if([1,_xm,_9],_gq));})])],_9]]);});}else{switch(E(_xn)){case 9:var _xq=[0,_x3,_x4,(_x5+8|0)-B(_gt(_x5-1|0,8))|0];break;case 10:var _xq=[0,_x3,_x4+1|0,1];break;default:var _xq=[0,_x3,_x4,_x5+1|0];}var _xr=_xq,_xs=[0,E(_xr),_9],_xt=[0,_xl,E(_xr),E(_x6)];return new F(function(){return A(_x7,[_xm,_xt,_xs]);});}}},_xu=function(_xv,_xw,_xx,_xy,_xz){var _xA=E(_xv),_xB=E(_xA[2]);return new F(function(){return _x1(_xA[1],_xB[1],_xB[2],_xB[3],_xA[3],_xw,_xx,_xy,_xz);});},_xC=[0,10],_xD=new T(function(){return B(unCStr("lf new-line"));}),_xE=[1,_xD,_9],_xF=function(_xG){return function(_xH,_xI,_xJ,_xK,_xL){return new F(function(){return _jI(new T(function(){return B(_kt(_xG,_xC));}),_xE,_xH,_xI,_xJ,_xK,_xL);});};},_xM=new T(function(){return B(_xF(_wX));}),_xN=function(_xO,_xP,_xQ,_xR,_xS,_xT,_xU){var _xV=function(_xW,_xX,_xY,_xZ,_y0,_y1){return new F(function(){return _y2(_xX,function(_y3,_y4,_y5){return new F(function(){return A(_xY,[[1,_xW,_y3],_y4,new T(function(){var _y6=E(E(_y4)[2]),_y7=E(_y5),_y8=E(_y7[1]),_y9=B(_db(_y8[1],_y8[2],_y8[3],_y7[2],_y6[1],_y6[2],_y6[3],_9));return [0,E(_y9[1]),_y9[2]];})]);});},_xZ,function(_ya,_yb,_yc){return new F(function(){return A(_y0,[[1,_xW,_ya],_yb,new T(function(){var _yd=E(E(_yb)[2]),_ye=E(_yc),_yf=E(_ye[1]),_yg=B(_db(_yf[1],_yf[2],_yf[3],_ye[2],_yd[1],_yd[2],_yd[3],_9));return [0,E(_yg[1]),_yg[2]];})]);});},_y1);});},_y2=function(_yh,_yi,_yj,_yk,_yl){return new F(function(){return A(_xP,[_yh,function(_ym,_yn,_yo){return new F(function(){return A(_yi,[_9,_yn,new T(function(){var _yp=E(E(_yn)[2]),_yq=E(_yo),_yr=E(_yq[1]),_ys=B(_db(_yr[1],_yr[2],_yr[3],_yq[2],_yp[1],_yp[2],_yp[3],_9));return [0,E(_ys[1]),_ys[2]];})]);});},_yj,function(_yt,_yu,_yv){return new F(function(){return A(_yk,[_9,_yu,new T(function(){var _yw=E(E(_yu)[2]),_yx=E(_yv),_yy=E(_yx[1]),_yz=B(_db(_yy[1],_yy[2],_yy[3],_yx[2],_yw[1],_yw[2],_yw[3],_9));return [0,E(_yz[1]),_yz[2]];})]);});},function(_yA){return new F(function(){return A(_xO,[_yh,function(_yB,_yC,_yD){return new F(function(){return _xV(_yB,_yC,_yi,_yj,function(_yE,_yF,_yG){return new F(function(){return A(_yi,[_yE,_yF,new T(function(){return B(_e0(_yD,_yG));})]);});},function(_yH){return new F(function(){return A(_yj,[new T(function(){return B(_e0(_yD,_yH));})]);});});});},_yj,function(_yI,_yJ,_yK){return new F(function(){return _xV(_yI,_yJ,_yi,_yj,function(_yL,_yM,_yN){return new F(function(){return A(_yk,[_yL,_yM,new T(function(){var _yO=E(_yA),_yP=E(_yO[1]),_yQ=E(_yK),_yR=E(_yQ[1]),_yS=E(_yN),_yT=E(_yS[1]),_yU=B(_db(_yR[1],_yR[2],_yR[3],_yQ[2],_yT[1],_yT[2],_yT[3],_yS[2])),_yV=E(_yU[1]),_yW=B(_db(_yP[1],_yP[2],_yP[3],_yO[2],_yV[1],_yV[2],_yV[3],_yU[2]));return [0,E(_yW[1]),_yW[2]];})]);});},function(_yX){return new F(function(){return A(_yl,[new T(function(){var _yY=E(_yA),_yZ=E(_yY[1]),_z0=E(_yK),_z1=E(_z0[1]),_z2=E(_yX),_z3=E(_z2[1]),_z4=B(_db(_z1[1],_z1[2],_z1[3],_z0[2],_z3[1],_z3[2],_z3[3],_z2[2])),_z5=E(_z4[1]),_z6=B(_db(_yZ[1],_yZ[2],_yZ[3],_yY[2],_z5[1],_z5[2],_z5[3],_z4[2]));return [0,E(_z6[1]),_z6[2]];})]);});});});},function(_z7){return new F(function(){return A(_yl,[new T(function(){return B(_e0(_yA,_z7));})]);});}]);});}]);});};return new F(function(){return _y2(_xQ,_xR,_xS,_xT,_xU);});},_z8=new T(function(){return B(unCStr("tab"));}),_z9=[1,_z8,_9],_za=[0,9],_zb=function(_zc){return function(_zd,_ze,_zf,_zg,_zh){return new F(function(){return _jI(new T(function(){return B(_kt(_zc,_za));}),_z9,_zd,_ze,_zf,_zg,_zh);});};},_zi=new T(function(){return B(_zb(_wX));}),_zj=[0,39],_zk=[1,_zj,_9],_zl=new T(function(){return B(unCStr("\'\\\'\'"));}),_zm=function(_zn){var _zo=E(E(_zn)[1]);return _zo==39?E(_zl):[1,_zj,new T(function(){return B(_hY(_zo,_zk));})];},_zp=function(_zq,_zr){return [1,_gp,new T(function(){return B(_if(_zq,[1,_gp,_zr]));})];},_zs=function(_zt){return new F(function(){return _e(_zl,_zt);});},_zu=function(_zv,_zw){var _zx=E(E(_zw)[1]);return _zx==39?E(_zs):function(_zy){return [1,_zj,new T(function(){return B(_hY(_zx,[1,_zj,_zy]));})];};},_zz=[0,_zu,_zm,_zp],_zA=function(_zB,_zC,_zD,_zE,_zF){var _zG=new T(function(){return B(_bT(_zB));}),_zH=function(_zI){return new F(function(){return A(_zE,[_6B,_zD,new T(function(){var _zJ=E(E(_zD)[2]),_zK=E(_zI),_zL=E(_zK[1]),_zM=B(_db(_zL[1],_zL[2],_zL[3],_zK[2],_zJ[1],_zJ[2],_zJ[3],_9));return [0,E(_zM[1]),_zM[2]];})]);});};return new F(function(){return A(_zC,[_zD,function(_zN,_zO,_zP){return new F(function(){return A(_zF,[new T(function(){var _zQ=E(E(_zO)[2]),_zR=E(_zP),_zS=E(_zR[1]),_zT=B(_db(_zS[1],_zS[2],_zS[3],_zR[2],_zQ[1],_zQ[2],_zQ[3],[1,new T(function(){return [1,E(B(A(_zG,[_zN])))];}),_9]));return [0,E(_zT[1]),_zT[2]];})]);});},_zH,function(_zU,_zV,_zW){return new F(function(){return A(_zE,[_6B,_zD,new T(function(){var _zX=E(E(_zD)[2]),_zY=E(E(_zV)[2]),_zZ=E(_zW),_A0=E(_zZ[1]),_A1=B(_db(_A0[1],_A0[2],_A0[3],_zZ[2],_zY[1],_zY[2],_zY[3],[1,new T(function(){return [1,E(B(A(_zG,[_zU])))];}),_9])),_A2=E(_A1[1]),_A3=B(_db(_A2[1],_A2[2],_A2[3],_A1[2],_zX[1],_zX[2],_zX[3],_9));return [0,E(_A3[1]),_A3[2]];})]);});},_zH]);});},_A4=function(_A5,_A6,_A7){return new F(function(){return _zA(_zz,_zi,_A5,function(_A8,_A9,_Aa){return new F(function(){return A(_A6,[_6B,_A9,new T(function(){var _Ab=E(E(_A9)[2]),_Ac=E(_Aa),_Ad=E(_Ac[1]),_Ae=B(_db(_Ad[1],_Ad[2],_Ad[3],_Ac[2],_Ab[1],_Ab[2],_Ab[3],_9));return [0,E(_Ae[1]),_Ae[2]];})]);});},_A7);});},_Af=function(_Ag,_Ah,_Ai,_Aj,_Ak){return new F(function(){return A(_xM,[_Ag,function(_Al,_Am,_An){return new F(function(){return _A4(_Am,function(_Ao,_Ap,_Aq){return new F(function(){return A(_Ah,[_Ao,_Ap,new T(function(){return B(_e0(_An,_Aq));})]);});},function(_Ar){return new F(function(){return A(_Ai,[new T(function(){return B(_e0(_An,_Ar));})]);});});});},_Ai,function(_As,_At,_Au){return new F(function(){return _A4(_At,function(_Av,_Aw,_Ax){return new F(function(){return A(_Aj,[_Av,_Aw,new T(function(){return B(_e0(_Au,_Ax));})]);});},function(_Ay){return new F(function(){return A(_Ak,[new T(function(){return B(_e0(_Au,_Ay));})]);});});});},_Ak]);});},_Az=[0,E(_9)],_AA=[1,_Az,_9],_AB=function(_AC,_AD,_AE,_AF,_AG,_AH,_AI){return new F(function(){return A(_AC,[new T(function(){return B(A(_AD,[_AE]));}),function(_AJ){var _AK=E(_AJ);if(!_AK[0]){return E(new T(function(){return B(A(_AI,[[0,E(_AF),_AA]]));}));}else{var _AL=E(_AK[1]);return new F(function(){return A(_AH,[_AL[1],[0,_AL[2],E(_AF),E(_AG)],[0,E(_AF),_9]]);});}}]);});},_AM=new T(function(){return B(unCStr("end of input"));}),_AN=[1,_AM,_9],_AO=function(_AP,_AQ,_AR,_AS,_AT,_AU,_AV,_AW){return new F(function(){return _jI(function(_AX,_AY,_AZ,_B0,_B1){return new F(function(){return _zA(_AR,function(_B2,_B3,_B4,_B5,_B6){var _B7=E(_B2);return new F(function(){return _AB(_AP,_AQ,_B7[1],_B7[2],_B7[3],_B3,_B6);});},_AX,_B0,_B1);});},_AN,_AS,_AT,_AU,_AV,_AW);});},_B8=function(_B9,_Ba,_Bb,_Bc,_Bd){return new F(function(){return _dy(_xM,_B9,function(_Be,_Bf,_Bg){return new F(function(){return _AO(_gm,_j5,_zz,_Bf,_Ba,_Bb,function(_Bh,_Bi,_Bj){return new F(function(){return A(_Ba,[_Bh,_Bi,new T(function(){return B(_e0(_Bg,_Bj));})]);});},function(_Bk){return new F(function(){return A(_Bb,[new T(function(){return B(_e0(_Bg,_Bk));})]);});});});},_Bb,function(_Bl,_Bm,_Bn){return new F(function(){return _AO(_gm,_j5,_zz,_Bm,_Ba,_Bb,function(_Bo,_Bp,_Bq){return new F(function(){return A(_Bc,[_Bo,_Bp,new T(function(){return B(_e0(_Bn,_Bq));})]);});},function(_Br){return new F(function(){return A(_Bd,[new T(function(){return B(_e0(_Bn,_Br));})]);});});});});});},_Bs=function(_Bt,_Bu,_Bv,_Bw){var _Bx=function(_By){var _Bz=function(_BA){return new F(function(){return A(_Bw,[new T(function(){return B(_e0(_By,_BA));})]);});};return new F(function(){return _Af(_Bt,_Bu,_Bz,function(_BB,_BC,_BD){return new F(function(){return A(_Bv,[_BB,_BC,new T(function(){return B(_e0(_By,_BD));})]);});},_Bz);});};return new F(function(){return _B8(_Bt,_Bu,_Bx,_Bv,_Bx);});},_BE=function(_BF,_BG,_BH,_BI,_BJ){return new F(function(){return _Bs(_BF,_BG,_BI,_BJ);});},_BK=function(_BL){return true;},_BM=function(_BN,_BO,_BP,_BQ,_BR){var _BS=E(_BN),_BT=E(_BS[2]);return new F(function(){return _il(_gm,_j5,_BK,_BS[1],_BT[1],_BT[2],_BT[3],_BS[3],_BO,_BR);});},_BU=function(_BV,_BW,_BX,_BY,_BZ){return new F(function(){return A(_zi,[_BV,function(_C0,_C1,_C2){return new F(function(){return _xN(_BM,_BE,_C1,_BW,_BX,function(_C3,_C4,_C5){return new F(function(){return A(_BW,[_C3,_C4,new T(function(){return B(_e0(_C2,_C5));})]);});},function(_C6){return new F(function(){return A(_BX,[new T(function(){return B(_e0(_C2,_C6));})]);});});});},_BX,function(_C7,_C8,_C9){return new F(function(){return _xN(_BM,_BE,_C8,_BW,_BX,function(_Ca,_Cb,_Cc){return new F(function(){return A(_BY,[_Ca,_Cb,new T(function(){return B(_e0(_C9,_Cc));})]);});},function(_Cd){return new F(function(){return A(_BZ,[new T(function(){return B(_e0(_C9,_Cd));})]);});});});},_BZ]);});},_Ce=[0,_wq,_9],_Cf=[0,_9,1,1],_Cg=function(_Ch){return E(_Ch);},_Ci=function(_Cj){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_Cj));}))));});},_Ck=new T(function(){return B(_Ci("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_Cl=new T(function(){return B(_Ci("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_Cm=[0,_gm,_Cl,_Cg,_Ck],_Cn=function(_Co){return new F(function(){return unAppCStr("string error",new T(function(){return B(_bh(_Co));}));});},_Cp=function(_Cq,_Cr,_Cs,_Ct,_Cu){return new F(function(){return A(_zi,[_Cr,function(_Cv,_Cw,_Cx){return new F(function(){return A(_Cs,[_Cq,_Cw,new T(function(){var _Cy=E(E(_Cw)[2]),_Cz=E(_Cx),_CA=E(_Cz[1]),_CB=B(_db(_CA[1],_CA[2],_CA[3],_Cz[2],_Cy[1],_Cy[2],_Cy[3],_9));return [0,E(_CB[1]),_CB[2]];})]);});},_Cu,function(_CC,_CD,_CE){return new F(function(){return A(_Ct,[_Cq,_CD,new T(function(){var _CF=E(E(_CD)[2]),_CG=E(_CE),_CH=E(_CG[1]),_CI=B(_db(_CH[1],_CH[2],_CH[3],_CG[2],_CF[1],_CF[2],_CF[3],_9));return [0,E(_CI[1]),_CI[2]];})]);});},_Cu]);});},_CJ=function(_CK,_CL,_CM,_CN,_CO){return new F(function(){return A(_xM,[_CK,function(_CP,_CQ,_CR){return new F(function(){return _Cp(_CP,_CQ,_CL,function(_CS,_CT,_CU){return new F(function(){return A(_CL,[_CS,_CT,new T(function(){return B(_e0(_CR,_CU));})]);});},function(_CV){return new F(function(){return A(_CM,[new T(function(){return B(_e0(_CR,_CV));})]);});});});},_CM,function(_CW,_CX,_CY){return new F(function(){return _Cp(_CW,_CX,_CL,function(_CZ,_D0,_D1){return new F(function(){return A(_CN,[_CZ,_D0,new T(function(){return B(_e0(_CY,_D1));})]);});},function(_D2){return new F(function(){return A(_CO,[new T(function(){return B(_e0(_CY,_D2));})]);});});});},_CO]);});},_D3=function(_D4,_D5,_D6,_D7,_D8){return new F(function(){return _CJ(_D4,_D5,_D6,_D7,function(_D9){var _Da=E(_D4),_Db=E(_Da[2]),_Dc=E(_Da[1]);return _Dc[0]==0?B(A(_D8,[new T(function(){var _Dd=E(_D9),_De=E(_Dd[1]),_Df=B(_db(_De[1],_De[2],_De[3],_Dd[2],_Db[1],_Db[2],_Db[3],_AA));return [0,E(_Df[1]),_Df[2]];})])):B(A(_D5,[_Dc[1],[0,_Dc[2],E(_Db),E(_Da[3])],[0,E(_Db),_9]]));});});},_Dg=function(_Dh,_Di,_Dj,_Dk,_Dl){return new F(function(){return _dy(_D3,_Dh,_Di,_Dj,_Dk);});},_Dm=function(_Dn,_Do,_Dp){return [0,_Dn,E(E(_Do)),_Dp];},_Dq=function(_Dr,_Ds,_Dt){var _Du=new T(function(){return B(_iZ(_Dr));}),_Dv=new T(function(){return B(_iZ(_Dr));});return new F(function(){return A(_Ds,[_Dt,function(_Dw,_Dx,_Dy){return new F(function(){return A(_Du,[[0,new T(function(){return B(A(_Dv,[new T(function(){return B(_Dm(_Dw,_Dx,_Dy));})]));})]]);});},function(_Dz){return new F(function(){return A(_Du,[[0,new T(function(){return B(A(_Dv,[[1,_Dz]]));})]]);});},function(_DA,_DB,_DC){return new F(function(){return A(_Du,[new T(function(){return [1,E(B(A(_Dv,[new T(function(){return B(_Dm(_DA,_DB,_DC));})])))];})]);});},function(_DD){return new F(function(){return A(_Du,[new T(function(){return [1,E(B(A(_Dv,[[1,_DD]])))];})]);});}]);});},_DE=function(_DF){return function(_DG,_DH,_DI,_DJ,_DK){return new F(function(){return A(_DJ,[new T(function(){var _DL=B(_Dq(_Cm,_DM,[0,new T(function(){var _DN=B(_Dq(_Cm,_Dg,[0,_DF,E(_Cf),E(_6B)]));if(!_DN[0]){var _DO=E(_DN[1]),_DP=_DO[0]==0?E(_DO[1]):B(_Cn(_DO[1]));}else{var _DQ=E(_DN[1]),_DP=_DQ[0]==0?E(_DQ[1]):B(_Cn(_DQ[1]));}return _DP;}),E(_Cf),E(_6B)]));if(!_DL[0]){var _DR=E(_DL[1]),_DS=_DR[0]==0?E(_DR[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_DR[1]));})));})],_9],_9],_Ce];}else{var _DT=E(_DL[1]),_DS=_DT[0]==0?E(_DT[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_DT[1]));})));})],_9],_9],_Ce];}return _DS;}),_DG,new T(function(){return [0,E(E(_DG)[2]),_9];})]);});};},_DU=function(_DV,_DW,_DX,_DY,_DZ){return new F(function(){return _BU(_DV,function(_E0,_E1,_E2){return new F(function(){return A(_DE,[_E0,_E1,_DW,_DX,function(_E3,_E4,_E5){return new F(function(){return A(_DW,[_E3,_E4,new T(function(){return B(_e0(_E2,_E5));})]);});},function(_E6){return new F(function(){return A(_DX,[new T(function(){return B(_e0(_E2,_E6));})]);});}]);});},_DX,function(_E7,_E8,_E9){return new F(function(){return A(_DE,[_E7,_E8,_DW,_DX,function(_Ea,_Eb,_Ec){return new F(function(){return A(_DY,[_Ea,_Eb,new T(function(){return B(_e0(_E9,_Ec));})]);});},function(_Ed){return new F(function(){return A(_DZ,[new T(function(){return B(_e0(_E9,_Ed));})]);});}]);});},_DZ);});},_Ee=function(_Ef,_Eg,_Eh,_Ei,_Ej,_Ek){var _El=function(_Em,_En,_Eo,_Ep,_Eq){var _Er=function(_Es,_Et,_Eu,_Ev,_Ew){return new F(function(){return A(_Ep,[[0,[1,[0,_Ef,_Et,_Eu]],_Es],_Ev,new T(function(){var _Ex=E(_Ew),_Ey=E(_Ex[1]),_Ez=E(E(_Ev)[2]),_EA=B(_db(_Ey[1],_Ey[2],_Ey[3],_Ex[2],_Ez[1],_Ez[2],_Ez[3],_9));return [0,E(_EA[1]),_EA[2]];})]);});},_EB=function(_EC){return new F(function(){return _Er(_9,_wq,_9,_Em,new T(function(){var _ED=E(E(_Em)[2]),_EE=E(_EC),_EF=E(_EE[1]),_EG=B(_db(_EF[1],_EF[2],_EF[3],_EE[2],_ED[1],_ED[2],_ED[3],_9));return [0,E(_EG[1]),_EG[2]];}));});};return new F(function(){return _DU(_Em,function(_EH,_EI,_EJ){var _EK=E(_EH),_EL=E(_EK[2]);return new F(function(){return A(_En,[[0,[1,[0,_Ef,_EL[1],_EL[2]]],_EK[1]],_EI,new T(function(){var _EM=E(_EJ),_EN=E(_EM[1]),_EO=E(E(_EI)[2]),_EP=B(_db(_EN[1],_EN[2],_EN[3],_EM[2],_EO[1],_EO[2],_EO[3],_9));return [0,E(_EP[1]),_EP[2]];})]);});},_EB,function(_EQ,_ER,_ES){var _ET=E(_EQ),_EU=E(_ET[2]);return new F(function(){return _Er(_ET[1],_EU[1],_EU[2],_ER,_ES);});},_EB);});};return new F(function(){return A(_xM,[_Eg,function(_EV,_EW,_EX){return new F(function(){return _El(_EW,_Eh,_Ei,function(_EY,_EZ,_F0){return new F(function(){return A(_Eh,[_EY,_EZ,new T(function(){return B(_e0(_EX,_F0));})]);});},function(_F1){return new F(function(){return A(_Ei,[new T(function(){return B(_e0(_EX,_F1));})]);});});});},_Ei,function(_F2,_F3,_F4){return new F(function(){return _El(_F3,_Eh,_Ei,function(_F5,_F6,_F7){return new F(function(){return A(_Ej,[_F5,_F6,new T(function(){return B(_e0(_F4,_F7));})]);});},function(_F8){return new F(function(){return A(_Ek,[new T(function(){return B(_e0(_F4,_F8));})]);});});});},_Ek]);});},_F9=new T(function(){return B(unCStr(" associative operator"));}),_Fa=function(_Fb,_Fc){var _Fd=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_Fb,_F9));}))))];}),_9];return function(_Fe,_Ff,_Fg,_Fh,_Fi){return new F(function(){return A(_Fc,[_Fe,function(_Fj,_Fk,_Fl){return new F(function(){return A(_Fi,[new T(function(){var _Fm=E(E(_Fk)[2]),_Fn=E(_Fl),_Fo=E(_Fn[1]),_Fp=B(_db(_Fo[1],_Fo[2],_Fo[3],_Fn[2],_Fm[1],_Fm[2],_Fm[3],_Fd));return [0,E(_Fp[1]),_Fp[2]];})]);});},_Fi,function(_Fq,_Fr,_Fs){return new F(function(){return A(_Fi,[new T(function(){var _Ft=E(E(_Fr)[2]),_Fu=E(_Fs),_Fv=E(_Fu[1]),_Fw=B(_db(_Fv[1],_Fv[2],_Fv[3],_Fu[2],_Ft[1],_Ft[2],_Ft[3],_Fd));return [0,E(_Fw[1]),_Fw[2]];})]);});},_Fi]);});};},_Fx=function(_Fy,_Fz,_FA,_FB,_FC,_FD){var _FE=E(_Fy);if(!_FE[0]){return new F(function(){return A(_FD,[new T(function(){return [0,E(E(_Fz)[2]),_9];})]);});}else{return new F(function(){return A(_FE[1],[_Fz,_FA,_FB,_FC,function(_FF){return new F(function(){return _Fx(_FE[2],_Fz,_FA,_FB,function(_FG,_FH,_FI){return new F(function(){return A(_FC,[_FG,_FH,new T(function(){return B(_e0(_FF,_FI));})]);});},function(_FJ){return new F(function(){return A(_FD,[new T(function(){return B(_e0(_FF,_FJ));})]);});});});}]);});}},_FK=new T(function(){return B(unCStr("right"));}),_FL=new T(function(){return B(unCStr("left"));}),_FM=new T(function(){return B(unCStr("non"));}),_FN=new T(function(){return B(unCStr("operator"));}),_FO=[1,_FN,_9],_FP=[1,_9,_9],_FQ=function(_FR){var _FS=E(_FR);if(!_FS[0]){return [0,_9,_9,_9,_9,_9];}else{var _FT=_FS[2],_FU=E(_FS[1]);switch(_FU[0]){case 0:var _FV=_FU[1],_FW=B(_FQ(_FT)),_FX=_FW[1],_FY=_FW[2],_FZ=_FW[3],_G0=_FW[4],_G1=_FW[5];switch(E(_FU[2])){case 0:return [0,_FX,_FY,[1,_FV,_FZ],_G0,_G1];case 1:return [0,_FX,[1,_FV,_FY],_FZ,_G0,_G1];default:return [0,[1,_FV,_FX],_FY,_FZ,_G0,_G1];}break;case 1:var _G2=B(_FQ(_FT));return [0,_G2[1],_G2[2],_G2[3],[1,_FU[1],_G2[4]],_G2[5]];default:var _G3=B(_FQ(_FT));return [0,_G3[1],_G3[2],_G3[3],_G3[4],[1,_FU[1],_G3[5]]];}}},_G4=function(_G5,_G6){while(1){var _G7=(function(_G8,_G9){var _Ga=E(_G9);if(!_Ga[0]){return E(_G8);}else{var _Gb=new T(function(){var _Gc=B(_FQ(_Ga[1]));return [0,_Gc[1],_Gc[2],_Gc[3],_Gc[4],_Gc[5]];}),_Gd=new T(function(){return E(E(_Gb)[2]);}),_Ge=new T(function(){return B(_Fa(_FL,function(_Gf,_Gg,_Gh,_Gi,_Gj){return new F(function(){return _Fx(_Gd,_Gf,_Gg,_Gh,_Gi,_Gj);});}));}),_Gk=new T(function(){return E(E(_Gb)[1]);}),_Gl=new T(function(){return E(E(_Gb)[3]);}),_Gm=new T(function(){return B(_Fa(_FM,function(_Gn,_Go,_Gp,_Gq,_Gr){return new F(function(){return _Fx(_Gl,_Gn,_Go,_Gp,_Gq,_Gr);});}));}),_Gs=function(_Gt,_Gu,_Gv,_Gw,_Gx,_Gy){var _Gz=function(_GA,_GB,_GC,_GD,_GE){var _GF=new T(function(){return B(A(_Gt,[_GA]));});return new F(function(){return _Fx(new T(function(){return E(E(_Gb)[5]);}),_GB,function(_GG,_GH,_GI){return new F(function(){return A(_GC,[new T(function(){return B(A(_GG,[_GF]));}),_GH,new T(function(){var _GJ=E(E(_GH)[2]),_GK=E(_GI),_GL=E(_GK[1]),_GM=B(_db(_GL[1],_GL[2],_GL[3],_GK[2],_GJ[1],_GJ[2],_GJ[3],_9));return [0,E(_GM[1]),_GM[2]];})]);});},_GD,function(_GN,_GO,_GP){return new F(function(){return A(_GE,[new T(function(){return B(A(_GN,[_GF]));}),_GO,new T(function(){var _GQ=E(E(_GO)[2]),_GR=_GQ[1],_GS=_GQ[2],_GT=_GQ[3],_GU=E(_GP),_GV=E(_GU[1]),_GW=_GV[2],_GX=_GV[3],_GY=E(_GU[2]);if(!_GY[0]){switch(B(_d3(_GV[1],_GR))){case 0:var _GZ=[0,E(_GQ),_9];break;case 1:if(_GW>=_GS){if(_GW!=_GS){var _H0=[0,E(_GV),_9];}else{if(_GX>=_GT){var _H1=_GX!=_GT?[0,E(_GV),_9]:[0,E(_GV),_da];}else{var _H1=[0,E(_GQ),_9];}var _H2=_H1,_H0=_H2;}var _H3=_H0,_H4=_H3;}else{var _H4=[0,E(_GQ),_9];}var _H5=_H4,_GZ=_H5;break;default:var _GZ=[0,E(_GV),_9];}var _H6=_GZ;}else{var _H7=B(_jn(_GV,_GY,_FP)),_H8=E(_H7[1]),_H9=B(_db(_H8[1],_H8[2],_H8[3],_H7[2],_GR,_GS,_GT,_9)),_H6=[0,E(_H9[1]),_H9[2]];}var _Ha=_H6,_Hb=_Ha,_Hc=_Hb,_Hd=_Hc;return _Hd;})]);});},function(_He){return new F(function(){return A(_GE,[_GF,_GB,new T(function(){var _Hf=E(E(_GB)[2]),_Hg=_Hf[1],_Hh=_Hf[2],_Hi=_Hf[3],_Hj=E(_He),_Hk=B(_jn(_Hj[1],_Hj[2],_FP)),_Hl=E(_Hk[1]),_Hm=B(_db(_Hl[1],_Hl[2],_Hl[3],_Hk[2],_Hg,_Hh,_Hi,_9)),_Hn=E(_Hm[1]),_Ho=B(_db(_Hn[1],_Hn[2],_Hn[3],_Hm[2],_Hg,_Hh,_Hi,_9));return [0,E(_Ho[1]),_Ho[2]];})]);});});});};return new F(function(){return A(_G8,[_Gu,function(_Hp,_Hq,_Hr){return new F(function(){return _Gz(_Hp,_Hq,_Gv,_Gw,function(_Hs,_Ht,_Hu){return new F(function(){return A(_Gv,[_Hs,_Ht,new T(function(){return B(_e0(_Hr,_Hu));})]);});});});},_Gw,function(_Hv,_Hw,_Hx){return new F(function(){return _Gz(_Hv,_Hw,_Gv,_Gw,function(_Hy,_Hz,_HA){return new F(function(){return A(_Gx,[_Hy,_Hz,new T(function(){return B(_e0(_Hx,_HA));})]);});});});},_Gy]);});},_HB=function(_HC,_HD,_HE,_HF,_HG){var _HH=function(_HI,_HJ,_HK){return new F(function(){return _Gs(_HI,_HJ,_HD,_HE,function(_HL,_HM,_HN){return new F(function(){return A(_HF,[_HL,_HM,new T(function(){return B(_e0(_HK,_HN));})]);});},function(_HO){return new F(function(){return A(_HG,[new T(function(){return B(_e0(_HK,_HO));})]);});});});};return new F(function(){return _Fx(new T(function(){return E(E(_Gb)[4]);}),_HC,function(_HP,_HQ,_HR){return new F(function(){return _Gs(_HP,_HQ,_HD,_HE,function(_HS,_HT,_HU){return new F(function(){return A(_HD,[_HS,_HT,new T(function(){return B(_e0(_HR,_HU));})]);});},function(_HV){return new F(function(){return A(_HE,[new T(function(){return B(_e0(_HR,_HV));})]);});});});},_HE,function(_HW,_HX,_HY){return new F(function(){return _HH(_HW,_HX,new T(function(){var _HZ=E(_HY),_I0=E(_HZ[2]);if(!_I0[0]){var _I1=E(_HZ);}else{var _I2=B(_jn(_HZ[1],_I0,_FP)),_I1=[0,E(_I2[1]),_I2[2]];}var _I3=_I1;return _I3;}));});},function(_I4){return new F(function(){return _HH(_6P,_HC,new T(function(){var _I5=E(E(_HC)[2]),_I6=E(_I4),_I7=B(_jn(_I6[1],_I6[2],_FP)),_I8=E(_I7[1]),_I9=B(_db(_I8[1],_I8[2],_I8[3],_I7[2],_I5[1],_I5[2],_I5[3],_9));return [0,E(_I9[1]),_I9[2]];}));});});});},_Ia=function(_Ib,_Ic,_Id,_Ie,_If,_Ig){var _Ih=function(_Ii){return new F(function(){return A(_Ge,[_Ic,_Id,_Ie,function(_Ij,_Ik,_Il){return new F(function(){return A(_If,[_Ij,_Ik,new T(function(){return B(_e0(_Ii,_Il));})]);});},function(_Im){return new F(function(){return A(_Gm,[_Ic,_Id,_Ie,function(_In,_Io,_Ip){return new F(function(){return A(_If,[_In,_Io,new T(function(){var _Iq=E(_Ii),_Ir=E(_Iq[1]),_Is=E(_Im),_It=E(_Is[1]),_Iu=E(_Ip),_Iv=E(_Iu[1]),_Iw=B(_db(_It[1],_It[2],_It[3],_Is[2],_Iv[1],_Iv[2],_Iv[3],_Iu[2])),_Ix=E(_Iw[1]),_Iy=B(_db(_Ir[1],_Ir[2],_Ir[3],_Iq[2],_Ix[1],_Ix[2],_Ix[3],_Iw[2]));return [0,E(_Iy[1]),_Iy[2]];})]);});},function(_Iz){return new F(function(){return A(_Ig,[new T(function(){var _IA=E(_Ii),_IB=E(_IA[1]),_IC=E(_Im),_ID=E(_IC[1]),_IE=E(_Iz),_IF=E(_IE[1]),_IG=B(_db(_ID[1],_ID[2],_ID[3],_IC[2],_IF[1],_IF[2],_IF[3],_IE[2])),_IH=E(_IG[1]),_II=B(_db(_IB[1],_IB[2],_IB[3],_IA[2],_IH[1],_IH[2],_IH[3],_IG[2]));return [0,E(_II[1]),_II[2]];})]);});}]);});}]);});},_IJ=function(_IK,_IL,_IM,_IN,_IO,_IP){var _IQ=function(_IR,_IS,_IT){return new F(function(){return A(_IM,[new T(function(){return B(A(_IK,[_Ib,_IR]));}),_IS,new T(function(){var _IU=E(E(_IS)[2]),_IV=E(_IT),_IW=E(_IV[1]),_IX=B(_db(_IW[1],_IW[2],_IW[3],_IV[2],_IU[1],_IU[2],_IU[3],_9));return [0,E(_IX[1]),_IX[2]];})]);});};return new F(function(){return _HB(_IL,function(_IY,_IZ,_J0){return new F(function(){return _Ia(_IY,_IZ,_IQ,_IN,function(_J1,_J2,_J3){return new F(function(){return _IQ(_J1,_J2,new T(function(){var _J4=E(_J0),_J5=E(_J4[1]),_J6=E(_J3),_J7=E(_J6[1]),_J8=B(_db(_J5[1],_J5[2],_J5[3],_J4[2],_J7[1],_J7[2],_J7[3],_J6[2]));return [0,E(_J8[1]),_J8[2]];},1));});},function(_J9){return new F(function(){return _IQ(_IY,_IZ,new T(function(){var _Ja=E(E(_IZ)[2]),_Jb=E(_J0),_Jc=E(_Jb[1]),_Jd=E(_J9),_Je=E(_Jd[1]),_Jf=B(_db(_Je[1],_Je[2],_Je[3],_Jd[2],_Ja[1],_Ja[2],_Ja[3],_9)),_Jg=E(_Jf[1]),_Jh=B(_db(_Jc[1],_Jc[2],_Jc[3],_Jb[2],_Jg[1],_Jg[2],_Jg[3],_Jf[2]));return [0,E(_Jh[1]),_Jh[2]];},1));});});});},_IN,function(_Ji,_Jj,_Jk){var _Jl=function(_Jm,_Jn,_Jo){return new F(function(){return A(_IO,[new T(function(){return B(A(_IK,[_Ib,_Jm]));}),_Jn,new T(function(){var _Jp=E(E(_Jn)[2]),_Jq=E(_Jk),_Jr=E(_Jq[1]),_Js=E(_Jo),_Jt=E(_Js[1]),_Ju=B(_db(_Jr[1],_Jr[2],_Jr[3],_Jq[2],_Jt[1],_Jt[2],_Jt[3],_Js[2])),_Jv=E(_Ju[1]),_Jw=B(_db(_Jv[1],_Jv[2],_Jv[3],_Ju[2],_Jp[1],_Jp[2],_Jp[3],_9));return [0,E(_Jw[1]),_Jw[2]];})]);});};return new F(function(){return _Ia(_Ji,_Jj,_IQ,_IN,_Jl,function(_Jx){return new F(function(){return _Jl(_Ji,_Jj,new T(function(){var _Jy=E(E(_Jj)[2]),_Jz=E(_Jx),_JA=E(_Jz[1]),_JB=B(_db(_JA[1],_JA[2],_JA[3],_Jz[2],_Jy[1],_Jy[2],_Jy[3],_9));return [0,E(_JB[1]),_JB[2]];},1));});});});},_IP);});};return new F(function(){return _Fx(_Gk,_Ic,function(_JC,_JD,_JE){return new F(function(){return _IJ(_JC,_JD,_Id,_Ie,function(_JF,_JG,_JH){return new F(function(){return A(_Id,[_JF,_JG,new T(function(){return B(_e0(_JE,_JH));})]);});},function(_JI){return new F(function(){return A(_Ie,[new T(function(){return B(_e0(_JE,_JI));})]);});});});},_Ie,function(_JJ,_JK,_JL){return new F(function(){return _IJ(_JJ,_JK,_Id,_Ie,function(_JM,_JN,_JO){return new F(function(){return A(_If,[_JM,_JN,new T(function(){return B(_e0(_JL,_JO));})]);});},function(_JP){return new F(function(){return _Ih(new T(function(){return B(_e0(_JL,_JP));}));});});});},_Ih);});},_JQ=new T(function(){return B(_Fa(_FK,function(_JR,_JS,_JT,_JU,_JV){return new F(function(){return _Fx(_Gk,_JR,_JS,_JT,_JU,_JV);});}));}),_JW=function(_JX,_JY,_JZ,_K0,_K1,_K2){var _K3=function(_K4){return new F(function(){return A(_JQ,[_JY,_JZ,_K0,function(_K5,_K6,_K7){return new F(function(){return A(_K1,[_K5,_K6,new T(function(){return B(_e0(_K4,_K7));})]);});},function(_K8){return new F(function(){return A(_Gm,[_JY,_JZ,_K0,function(_K9,_Ka,_Kb){return new F(function(){return A(_K1,[_K9,_Ka,new T(function(){var _Kc=E(_K4),_Kd=E(_Kc[1]),_Ke=E(_K8),_Kf=E(_Ke[1]),_Kg=E(_Kb),_Kh=E(_Kg[1]),_Ki=B(_db(_Kf[1],_Kf[2],_Kf[3],_Ke[2],_Kh[1],_Kh[2],_Kh[3],_Kg[2])),_Kj=E(_Ki[1]),_Kk=B(_db(_Kd[1],_Kd[2],_Kd[3],_Kc[2],_Kj[1],_Kj[2],_Kj[3],_Ki[2]));return [0,E(_Kk[1]),_Kk[2]];})]);});},function(_Kl){return new F(function(){return A(_K2,[new T(function(){var _Km=E(_K4),_Kn=E(_Km[1]),_Ko=E(_K8),_Kp=E(_Ko[1]),_Kq=E(_Kl),_Kr=E(_Kq[1]),_Ks=B(_db(_Kp[1],_Kp[2],_Kp[3],_Ko[2],_Kr[1],_Kr[2],_Kr[3],_Kq[2])),_Kt=E(_Ks[1]),_Ku=B(_db(_Kn[1],_Kn[2],_Kn[3],_Km[2],_Kt[1],_Kt[2],_Kt[3],_Ks[2]));return [0,E(_Ku[1]),_Ku[2]];})]);});}]);});}]);});},_Kv=function(_Kw,_Kx,_Ky,_Kz,_KA,_KB){var _KC=function(_KD){var _KE=new T(function(){return B(A(_Kw,[_JX,_KD]));});return function(_KF,_KG,_KH,_KI,_KJ){return new F(function(){return _JW(_KE,_KF,_KG,_KH,_KI,function(_KK){return new F(function(){return A(_KI,[_KE,_KF,new T(function(){var _KL=E(E(_KF)[2]),_KM=E(_KK),_KN=E(_KM[1]),_KO=B(_db(_KN[1],_KN[2],_KN[3],_KM[2],_KL[1],_KL[2],_KL[3],_9));return [0,E(_KO[1]),_KO[2]];})]);});});});};};return new F(function(){return _HB(_Kx,function(_KP,_KQ,_KR){return new F(function(){return A(_KC,[_KP,_KQ,_Ky,_Kz,function(_KS,_KT,_KU){return new F(function(){return A(_Ky,[_KS,_KT,new T(function(){return B(_e0(_KR,_KU));})]);});},function(_KV){return new F(function(){return A(_Kz,[new T(function(){return B(_e0(_KR,_KV));})]);});}]);});},_Kz,function(_KW,_KX,_KY){return new F(function(){return A(_KC,[_KW,_KX,_Ky,_Kz,function(_KZ,_L0,_L1){return new F(function(){return A(_KA,[_KZ,_L0,new T(function(){return B(_e0(_KY,_L1));})]);});},function(_L2){return new F(function(){return A(_KB,[new T(function(){return B(_e0(_KY,_L2));})]);});}]);});},_KB);});};return new F(function(){return _Fx(_Gd,_JY,function(_L3,_L4,_L5){return new F(function(){return _Kv(_L3,_L4,_JZ,_K0,function(_L6,_L7,_L8){return new F(function(){return A(_JZ,[_L6,_L7,new T(function(){return B(_e0(_L5,_L8));})]);});},function(_L9){return new F(function(){return A(_K0,[new T(function(){return B(_e0(_L5,_L9));})]);});});});},_K0,function(_La,_Lb,_Lc){return new F(function(){return _Kv(_La,_Lb,_JZ,_K0,function(_Ld,_Le,_Lf){return new F(function(){return A(_K1,[_Ld,_Le,new T(function(){return B(_e0(_Lc,_Lf));})]);});},function(_Lg){return new F(function(){return _K3(new T(function(){return B(_e0(_Lc,_Lg));}));});});});},_K3);});},_Lh=function(_Li,_Lj,_Lk,_Ll,_Lm,_Ln){var _Lo=function(_Lp,_Lq,_Lr,_Ls,_Lt,_Lu){var _Lv=function(_Lw){return function(_Lx,_Ly,_Lz,_LA,_LB){return new F(function(){return A(_JQ,[_Lx,_Ly,_Lz,_LA,function(_LC){return new F(function(){return A(_Ge,[_Lx,_Ly,_Lz,function(_LD,_LE,_LF){return new F(function(){return A(_LA,[_LD,_LE,new T(function(){return B(_e0(_LC,_LF));})]);});},function(_LG){return new F(function(){return A(_Gm,[_Lx,_Ly,_Lz,function(_LH,_LI,_LJ){return new F(function(){return A(_LA,[_LH,_LI,new T(function(){var _LK=E(_LC),_LL=E(_LK[1]),_LM=E(_LG),_LN=E(_LM[1]),_LO=E(_LJ),_LP=E(_LO[1]),_LQ=B(_db(_LN[1],_LN[2],_LN[3],_LM[2],_LP[1],_LP[2],_LP[3],_LO[2])),_LR=E(_LQ[1]),_LS=B(_db(_LL[1],_LL[2],_LL[3],_LK[2],_LR[1],_LR[2],_LR[3],_LQ[2]));return [0,E(_LS[1]),_LS[2]];})]);});},function(_LT){return new F(function(){return A(_LA,[new T(function(){return B(A(_Lp,[_Li,_Lw]));}),_Lx,new T(function(){var _LU=E(E(_Lx)[2]),_LV=E(_LC),_LW=E(_LV[1]),_LX=E(_LG),_LY=E(_LX[1]),_LZ=E(_LT),_M0=E(_LZ[1]),_M1=B(_db(_M0[1],_M0[2],_M0[3],_LZ[2],_LU[1],_LU[2],_LU[3],_9)),_M2=E(_M1[1]),_M3=B(_db(_LY[1],_LY[2],_LY[3],_LX[2],_M2[1],_M2[2],_M2[3],_M1[2])),_M4=E(_M3[1]),_M5=B(_db(_LW[1],_LW[2],_LW[3],_LV[2],_M4[1],_M4[2],_M4[3],_M3[2]));return [0,E(_M5[1]),_M5[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _HB(_Lq,function(_M6,_M7,_M8){return new F(function(){return A(_Lv,[_M6,_M7,_Lr,_Ls,function(_M9,_Ma,_Mb){return new F(function(){return A(_Lr,[_M9,_Ma,new T(function(){return B(_e0(_M8,_Mb));})]);});},function(_Mc){return new F(function(){return A(_Ls,[new T(function(){return B(_e0(_M8,_Mc));})]);});}]);});},_Ls,function(_Md,_Me,_Mf){return new F(function(){return A(_Lv,[_Md,_Me,_Lr,_Ls,function(_Mg,_Mh,_Mi){return new F(function(){return A(_Lt,[_Mg,_Mh,new T(function(){return B(_e0(_Mf,_Mi));})]);});},function(_Mj){return new F(function(){return A(_Lu,[new T(function(){return B(_e0(_Mf,_Mj));})]);});}]);});},_Lu);});};return new F(function(){return _jI(function(_Mk,_Ml,_Mm,_Mn,_Mo){return new F(function(){return _Ia(_Li,_Mk,_Ml,_Mm,_Mn,function(_Mp){return new F(function(){return _JW(_Li,_Mk,_Ml,_Mm,function(_Mq,_Mr,_Ms){return new F(function(){return A(_Mn,[_Mq,_Mr,new T(function(){return B(_e0(_Mp,_Ms));})]);});},function(_Mt){var _Mu=function(_Mv){return new F(function(){return A(_Mn,[_Li,_Mk,new T(function(){var _Mw=E(E(_Mk)[2]),_Mx=E(_Mp),_My=E(_Mx[1]),_Mz=E(_Mt),_MA=E(_Mz[1]),_MB=E(_Mv),_MC=E(_MB[1]),_MD=B(_db(_MC[1],_MC[2],_MC[3],_MB[2],_Mw[1],_Mw[2],_Mw[3],_9)),_ME=E(_MD[1]),_MF=B(_db(_MA[1],_MA[2],_MA[3],_Mz[2],_ME[1],_ME[2],_ME[3],_MD[2])),_MG=E(_MF[1]),_MH=B(_db(_My[1],_My[2],_My[3],_Mx[2],_MG[1],_MG[2],_MG[3],_MF[2]));return [0,E(_MH[1]),_MH[2]];})]);});};return new F(function(){return _Fx(_Gl,_Mk,function(_MI,_MJ,_MK){return new F(function(){return _Lo(_MI,_MJ,_Ml,_Mm,function(_ML,_MM,_MN){return new F(function(){return A(_Ml,[_ML,_MM,new T(function(){return B(_e0(_MK,_MN));})]);});},function(_MO){return new F(function(){return A(_Mm,[new T(function(){return B(_e0(_MK,_MO));})]);});});});},_Mm,function(_MP,_MQ,_MR){return new F(function(){return _Lo(_MP,_MQ,_Ml,_Mm,function(_MS,_MT,_MU){return new F(function(){return A(_Mn,[_MS,_MT,new T(function(){var _MV=E(_Mp),_MW=E(_MV[1]),_MX=E(_Mt),_MY=E(_MX[1]),_MZ=E(_MR),_N0=E(_MZ[1]),_N1=E(_MU),_N2=E(_N1[1]),_N3=B(_db(_N0[1],_N0[2],_N0[3],_MZ[2],_N2[1],_N2[2],_N2[3],_N1[2])),_N4=E(_N3[1]),_N5=B(_db(_MY[1],_MY[2],_MY[3],_MX[2],_N4[1],_N4[2],_N4[3],_N3[2])),_N6=E(_N5[1]),_N7=B(_db(_MW[1],_MW[2],_MW[3],_MV[2],_N6[1],_N6[2],_N6[3],_N5[2]));return [0,E(_N7[1]),_N7[2]];})]);});},function(_N8){return new F(function(){return _Mu(new T(function(){var _N9=E(_MR),_Na=E(_N9[1]),_Nb=E(_N8),_Nc=E(_Nb[1]),_Nd=B(_db(_Na[1],_Na[2],_Na[3],_N9[2],_Nc[1],_Nc[2],_Nc[3],_Nb[2]));return [0,E(_Nd[1]),_Nd[2]];},1));});});});},_Mu);});});});});});},_FO,_Lj,_Lk,_Ll,_Lm,_Ln);});};_G5=function(_Ne,_Nf,_Ng,_Nh,_Ni){return new F(function(){return _HB(_Ne,function(_Nj,_Nk,_Nl){return new F(function(){return _Lh(_Nj,_Nk,_Nf,_Ng,function(_Nm,_Nn,_No){return new F(function(){return A(_Nf,[_Nm,_Nn,new T(function(){return B(_e0(_Nl,_No));})]);});},function(_Np){return new F(function(){return A(_Ng,[new T(function(){return B(_e0(_Nl,_Np));})]);});});});},_Ng,function(_Nq,_Nr,_Ns){return new F(function(){return _Lh(_Nq,_Nr,_Nf,_Ng,function(_Nt,_Nu,_Nv){return new F(function(){return A(_Nh,[_Nt,_Nu,new T(function(){return B(_e0(_Ns,_Nv));})]);});},function(_Nw){return new F(function(){return A(_Ni,[new T(function(){return B(_e0(_Ns,_Nw));})]);});});});},_Ni);});};_G6=_Ga[2];return null;}})(_G5,_G6);if(_G7!=null){return _G7;}}},_Nx=0,_Ny=[3,_],_Nz=function(_NA,_NB){return [5,_Ny,_NA,_NB];},_NC=new T(function(){return B(unCStr("=>"));}),_ND=function(_NE){return E(E(_NE)[1]);},_NF=function(_NG,_NH,_NI,_NJ){while(1){var _NK=E(_NJ);if(!_NK[0]){return [0,_NG,_NH,_NI];}else{var _NL=_NK[2];switch(E(E(_NK[1])[1])){case 9:var _NM=(_NI+8|0)-B(_gt(_NI-1|0,8))|0;_NJ=_NL;_NI=_NM;continue;case 10:var _NN=_NH+1|0;_NI=1;_NJ=_NL;_NH=_NN;continue;default:var _NM=_NI+1|0;_NJ=_NL;_NI=_NM;continue;}}}},_NO=function(_NP){return E(E(_NP)[1]);},_NQ=function(_NR){return E(E(_NR)[2]);},_NS=function(_NT){return [0,E(E(_NT)[2]),_9];},_NU=function(_NV,_NW,_NX,_NY,_NZ,_O0,_O1){var _O2=E(_NW);if(!_O2[0]){return new F(function(){return A(_O0,[_9,_NX,new T(function(){return B(_NS(_NX));})]);});}else{var _O3=E(_NX),_O4=E(_O3[2]),_O5=new T(function(){return B(_ND(_NV));}),_O6=[0,E(_O4),[1,[2,E([1,_gp,new T(function(){return B(_if(_O2,_gq));})])],_gs]],_O7=[2,E([1,_gp,new T(function(){return B(_if(_O2,_gq));})])],_O8=new T(function(){var _O9=B(_NF(_O4[1],_O4[2],_O4[3],_O2));return [0,_O9[1],_O9[2],_O9[3]];}),_Oa=function(_Ob,_Oc){var _Od=E(_Ob);if(!_Od[0]){return new F(function(){return A(_NY,[_O2,new T(function(){return [0,_Oc,E(E(_O8)),E(_O3[3])];}),new T(function(){return [0,E(E(_O8)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_NO(_O5));}),[new T(function(){return B(A(new T(function(){return B(_NQ(_NV));}),[_Oc]));}),function(_Oe){var _Of=E(_Oe);if(!_Of[0]){return E(new T(function(){return B(A(_NZ,[_O6]));}));}else{var _Og=E(_Of[1]),_Oh=E(_Og[1]);return E(_Od[1])[1]!=_Oh[1]?B(A(_NZ,[[0,E(_O4),[1,_O7,[1,[0,E([1,_gp,new T(function(){return B(_if([1,_Oh,_9],_gq));})])],_9]]]])):B(_Oa(_Od[2],_Og[2]));}}]);});}};return new F(function(){return A(_NO,[_O5,new T(function(){return B(A(_NQ,[_NV,_O3[1]]));}),function(_Oi){var _Oj=E(_Oi);if(!_Oj[0]){return E(new T(function(){return B(A(_O1,[_O6]));}));}else{var _Ok=E(_Oj[1]),_Ol=E(_Ok[1]);return E(_O2[1])[1]!=_Ol[1]?B(A(_O1,[[0,E(_O4),[1,_O7,[1,[0,E([1,_gp,new T(function(){return B(_if([1,_Ol,_9],_gq));})])],_9]]]])):B(_Oa(_O2[2],_Ok[2]));}}]);});}},_Om=function(_On,_Oo,_Op,_Oq,_Or){return new F(function(){return _NU(_ks,_NC,_On,function(_Os,_Ot,_Ou){return new F(function(){return A(_Oo,[_Nz,_Ot,new T(function(){var _Ov=E(E(_Ot)[2]),_Ow=E(_Ou),_Ox=E(_Ow[1]),_Oy=B(_db(_Ox[1],_Ox[2],_Ox[3],_Ow[2],_Ov[1],_Ov[2],_Ov[3],_9));return [0,E(_Oy[1]),_Oy[2]];})]);});},_Op,function(_Oz,_OA,_OB){return new F(function(){return A(_Oq,[_Nz,_OA,new T(function(){var _OC=E(E(_OA)[2]),_OD=E(_OB),_OE=E(_OD[1]),_OF=B(_db(_OE[1],_OE[2],_OE[3],_OD[2],_OC[1],_OC[2],_OC[3],_9));return [0,E(_OF[1]),_OF[2]];})]);});},_Or);});},_OG=[0,_Om,_Nx],_OH=[1,_OG,_9],_OI=[1,_OH,_9],_OJ=1,_OK=[2,_],_OL=function(_NA,_NB){return [5,_OK,_NA,_NB];},_OM=new T(function(){return B(unCStr("\\/"));}),_ON=function(_OO,_OP,_OQ,_OR,_OS){return new F(function(){return _NU(_ks,_OM,_OO,function(_OT,_OU,_OV){return new F(function(){return A(_OP,[_OL,_OU,new T(function(){var _OW=E(E(_OU)[2]),_OX=E(_OV),_OY=E(_OX[1]),_OZ=B(_db(_OY[1],_OY[2],_OY[3],_OX[2],_OW[1],_OW[2],_OW[3],_9));return [0,E(_OZ[1]),_OZ[2]];})]);});},_OQ,function(_P0,_P1,_P2){return new F(function(){return A(_OR,[_OL,_P1,new T(function(){var _P3=E(E(_P1)[2]),_P4=E(_P2),_P5=E(_P4[1]),_P6=B(_db(_P5[1],_P5[2],_P5[3],_P4[2],_P3[1],_P3[2],_P3[3],_9));return [0,E(_P6[1]),_P6[2]];})]);});},_OS);});},_P7=[0,_ON,_OJ],_P8=[1,_],_P9=function(_NA,_NB){return [5,_P8,_NA,_NB];},_Pa=new T(function(){return B(unCStr("/\\"));}),_Pb=function(_Pc,_Pd,_Pe,_Pf,_Pg){return new F(function(){return _NU(_ks,_Pa,_Pc,function(_Ph,_Pi,_Pj){return new F(function(){return A(_Pd,[_P9,_Pi,new T(function(){var _Pk=E(E(_Pi)[2]),_Pl=E(_Pj),_Pm=E(_Pl[1]),_Pn=B(_db(_Pm[1],_Pm[2],_Pm[3],_Pl[2],_Pk[1],_Pk[2],_Pk[3],_9));return [0,E(_Pn[1]),_Pn[2]];})]);});},_Pe,function(_Po,_Pp,_Pq){return new F(function(){return A(_Pf,[_P9,_Pp,new T(function(){var _Pr=E(E(_Pp)[2]),_Ps=E(_Pq),_Pt=E(_Ps[1]),_Pu=B(_db(_Pt[1],_Pt[2],_Pt[3],_Ps[2],_Pr[1],_Pr[2],_Pr[3],_9));return [0,E(_Pu[1]),_Pu[2]];})]);});},_Pg);});},_Pv=[0,_Pb,_OJ],_Pw=[1,_Pv,_9],_Px=[1,_P7,_Pw],_Py=[1,_Px,_OI],_Pz=[0,_],_PA=function(_NB){return [4,_Pz,_NB];},_PB=[0,45],_PC=[1,_PB,_9],_PD=function(_PE,_PF,_PG,_PH,_PI){return new F(function(){return _NU(_ks,_PC,_PE,function(_PJ,_PK,_PL){return new F(function(){return A(_PF,[_PA,_PK,new T(function(){var _PM=E(E(_PK)[2]),_PN=E(_PL),_PO=E(_PN[1]),_PP=B(_db(_PO[1],_PO[2],_PO[3],_PN[2],_PM[1],_PM[2],_PM[3],_9));return [0,E(_PP[1]),_PP[2]];})]);});},_PG,function(_PQ,_PR,_PS){return new F(function(){return A(_PH,[_PA,_PR,new T(function(){var _PT=E(E(_PR)[2]),_PU=E(_PS),_PV=E(_PU[1]),_PW=B(_db(_PV[1],_PV[2],_PV[3],_PU[2],_PT[1],_PT[2],_PT[3],_9));return [0,E(_PW[1]),_PW[2]];})]);});},_PI);});},_PX=[1,_PD],_PY=[1,_PX,_9],_PZ=[1,_PY,_Py],_Q0=new T(function(){return B(unCStr("number"));}),_Q1=[1,_Q0,_9],_Q2=new T(function(){return B(err(_kO));}),_Q3=new T(function(){return B(err(_kM));}),_Q4=new T(function(){return B(_uq(_uM,_ud,_uS));}),_Q5=function(_Q6){return function(_Q7,_Q8,_Q9,_Qa,_Qb){return new F(function(){return A(_Qa,[new T(function(){var _Qc=B(_uX(B(_kR(_Q4,_Q6))));return _Qc[0]==0?E(_Q3):E(_Qc[2])[0]==0?E(_Qc[1]):E(_Q2);}),_Q7,new T(function(){return [0,E(E(_Q7)[2]),_9];})]);});};},_Qd=function(_Qe,_Qf,_Qg,_Qh,_Qi){return new F(function(){return _e8(_ke,_Qe,function(_Qj,_Qk,_Ql){return new F(function(){return A(_Q5,[_Qj,_Qk,_Qf,_Qg,function(_Qm,_Qn,_Qo){return new F(function(){return A(_Qf,[_Qm,_Qn,new T(function(){return B(_e0(_Ql,_Qo));})]);});},function(_Qp){return new F(function(){return A(_Qg,[new T(function(){return B(_e0(_Ql,_Qp));})]);});}]);});},_Qg,function(_Qq,_Qr,_Qs){return new F(function(){return A(_Q5,[_Qq,_Qr,_Qf,_Qg,function(_Qt,_Qu,_Qv){return new F(function(){return A(_Qh,[_Qt,_Qu,new T(function(){return B(_e0(_Qs,_Qv));})]);});},function(_Qw){return new F(function(){return A(_Qi,[new T(function(){return B(_e0(_Qs,_Qw));})]);});}]);});},_Qi);});},_Qx=function(_Qy,_Qz,_QA,_QB,_QC){return new F(function(){return _Qd(_Qy,function(_QD,_QE,_QF){return new F(function(){return A(_Qz,[[1,[0,_,_QD]],_QE,new T(function(){var _QG=E(E(_QE)[2]),_QH=E(_QF),_QI=E(_QH[1]),_QJ=B(_db(_QI[1],_QI[2],_QI[3],_QH[2],_QG[1],_QG[2],_QG[3],_9));return [0,E(_QJ[1]),_QJ[2]];})]);});},_QA,function(_QK,_QL,_QM){return new F(function(){return A(_QB,[[1,[0,_,_QK]],_QL,new T(function(){var _QN=E(E(_QL)[2]),_QO=_QN[1],_QP=_QN[2],_QQ=_QN[3],_QR=E(_QM),_QS=E(_QR[1]),_QT=_QS[2],_QU=_QS[3],_QV=E(_QR[2]);if(!_QV[0]){switch(B(_d3(_QS[1],_QO))){case 0:var _QW=[0,E(_QN),_9];break;case 1:if(_QT>=_QP){if(_QT!=_QP){var _QX=[0,E(_QS),_9];}else{if(_QU>=_QQ){var _QY=_QU!=_QQ?[0,E(_QS),_9]:[0,E(_QS),_da];}else{var _QY=[0,E(_QN),_9];}var _QZ=_QY,_QX=_QZ;}var _R0=_QX,_R1=_R0;}else{var _R1=[0,E(_QN),_9];}var _R2=_R1,_QW=_R2;break;default:var _QW=[0,E(_QS),_9];}var _R3=_QW;}else{var _R4=B(_jn(_QS,_QV,_Q1)),_R5=E(_R4[1]),_R6=B(_db(_R5[1],_R5[2],_R5[3],_R4[2],_QO,_QP,_QQ,_9)),_R3=[0,E(_R6[1]),_R6[2]];}var _R7=_R3,_R8=_R7,_R9=_R8,_Ra=_R9;return _Ra;})]);});},function(_Rb){return new F(function(){return A(_QC,[new T(function(){var _Rc=E(_Rb),_Rd=B(_jn(_Rc[1],_Rc[2],_Q1));return [0,E(_Rd[1]),_Rd[2]];})]);});});});},_Re=new T(function(){return B(unCStr("P_"));}),_Rf=function(_Rg,_Rh,_Ri,_Rj,_Rk){return new F(function(){return _NU(_ks,_Re,_Rg,function(_Rl,_Rm,_Rn){return new F(function(){return _Qx(_Rm,_Rh,_Ri,function(_Ro,_Rp,_Rq){return new F(function(){return A(_Rh,[_Ro,_Rp,new T(function(){return B(_e0(_Rn,_Rq));})]);});},function(_Rr){return new F(function(){return A(_Ri,[new T(function(){return B(_e0(_Rn,_Rr));})]);});});});},_Ri,function(_Rs,_Rt,_Ru){return new F(function(){return _Qx(_Rt,_Rh,_Ri,function(_Rv,_Rw,_Rx){return new F(function(){return A(_Rj,[_Rv,_Rw,new T(function(){return B(_e0(_Ru,_Rx));})]);});},function(_Ry){return new F(function(){return A(_Rk,[new T(function(){return B(_e0(_Ru,_Ry));})]);});});});},_Rk);});},_Rz=[0,41],_RA=new T(function(){return B(_kt(_ks,_Rz));}),_RB=function(_RC,_RD,_RE,_RF,_RG,_RH){return new F(function(){return A(_RA,[_RD,function(_RI,_RJ,_RK){return new F(function(){return A(_RE,[_RC,_RJ,new T(function(){var _RL=E(E(_RJ)[2]),_RM=E(_RK),_RN=E(_RM[1]),_RO=B(_db(_RN[1],_RN[2],_RN[3],_RM[2],_RL[1],_RL[2],_RL[3],_9));return [0,E(_RO[1]),_RO[2]];})]);});},_RF,function(_RP,_RQ,_RR){return new F(function(){return A(_RG,[_RC,_RQ,new T(function(){var _RS=E(E(_RQ)[2]),_RT=E(_RR),_RU=E(_RT[1]),_RV=B(_db(_RU[1],_RU[2],_RU[3],_RT[2],_RS[1],_RS[2],_RS[3],_9));return [0,E(_RV[1]),_RV[2]];})]);});},_RH]);});},_RW=function(_RX,_RY,_RZ,_S0,_S1){return new F(function(){return A(_S2,[_RX,function(_S3,_S4,_S5){return new F(function(){return _RB(_S3,_S4,_RY,_RZ,function(_S6,_S7,_S8){return new F(function(){return A(_RY,[_S6,_S7,new T(function(){return B(_e0(_S5,_S8));})]);});},function(_S9){return new F(function(){return A(_RZ,[new T(function(){return B(_e0(_S5,_S9));})]);});});});},_RZ,function(_Sa,_Sb,_Sc){return new F(function(){return _RB(_Sa,_Sb,_RY,_RZ,function(_Sd,_Se,_Sf){return new F(function(){return A(_S0,[_Sd,_Se,new T(function(){return B(_e0(_Sc,_Sf));})]);});},function(_Sg){return new F(function(){return A(_S1,[new T(function(){return B(_e0(_Sc,_Sg));})]);});});});},_S1]);});},_Sh=[0,40],_Si=new T(function(){return B(_kt(_ks,_Sh));}),_Sj=function(_Sk,_Sl,_Sm,_Sn,_So){var _Sp=function(_Sq){return new F(function(){return _Rf(_Sk,_Sl,_Sm,function(_Sr,_Ss,_St){return new F(function(){return A(_Sn,[_Sr,_Ss,new T(function(){return B(_e0(_Sq,_St));})]);});},function(_Su){return new F(function(){return A(_So,[new T(function(){return B(_e0(_Sq,_Su));})]);});});});};return new F(function(){return A(_Si,[_Sk,function(_Sv,_Sw,_Sx){return new F(function(){return _RW(_Sw,_Sl,_Sm,function(_Sy,_Sz,_SA){return new F(function(){return A(_Sl,[_Sy,_Sz,new T(function(){return B(_e0(_Sx,_SA));})]);});},function(_SB){return new F(function(){return A(_Sm,[new T(function(){return B(_e0(_Sx,_SB));})]);});});});},_Sm,function(_SC,_SD,_SE){return new F(function(){return _RW(_SD,_Sl,_Sm,function(_SF,_SG,_SH){return new F(function(){return A(_Sn,[_SF,_SG,new T(function(){return B(_e0(_SE,_SH));})]);});},function(_SI){return new F(function(){return _Sp(new T(function(){return B(_e0(_SE,_SI));}));});});});},_Sp]);});},_S2=new T(function(){return B(_G4(_Sj,_PZ));}),_SJ=function(_SK,_SL,_SM,_SN,_SO){return new F(function(){return A(_S2,[_SK,function(_SP,_SQ,_SR){return new F(function(){return _Ee(_SP,_SQ,_SL,_SM,function(_SS,_ST,_SU){return new F(function(){return A(_SL,[_SS,_ST,new T(function(){return B(_e0(_SR,_SU));})]);});},function(_SV){return new F(function(){return A(_SM,[new T(function(){return B(_e0(_SR,_SV));})]);});});});},_SM,function(_SW,_SX,_SY){return new F(function(){return _Ee(_SW,_SX,_SL,_SM,function(_SZ,_T0,_T1){return new F(function(){return A(_SN,[_SZ,_T0,new T(function(){return B(_e0(_SY,_T1));})]);});},function(_T2){return new F(function(){return A(_SO,[new T(function(){return B(_e0(_SY,_T2));})]);});});});},_SO]);});},_T3=function(_T4,_T5,_T6,_T7,_T8){return new F(function(){return _eL(_j7,_T4,function(_T9,_Ta,_Tb){return new F(function(){return _SJ(_Ta,_T5,_T6,function(_Tc,_Td,_Te){return new F(function(){return A(_T5,[_Tc,_Td,new T(function(){return B(_e0(_Tb,_Te));})]);});},function(_Tf){return new F(function(){return A(_T6,[new T(function(){return B(_e0(_Tb,_Tf));})]);});});});},_T6,function(_Tg,_Th,_Ti){return new F(function(){return _SJ(_Th,_T5,_T6,function(_Tj,_Tk,_Tl){return new F(function(){return A(_T7,[_Tj,_Tk,new T(function(){return B(_e0(_Ti,_Tl));})]);});},function(_Tm){return new F(function(){return A(_T8,[new T(function(){return B(_e0(_Ti,_Tm));})]);});});});});});},_Tn=function(_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv){var _Tw=E(_To);if(!_Tw[0]){return new F(function(){return A(_Tv,[[0,E([0,_Tp,_Tq,_Tr]),_gs]]);});}else{var _Tx=_Tw[1];if(!B(_9r(_iN,_Tx,_wW))){return new F(function(){return A(_Tv,[[0,E([0,_Tp,_Tq,_Tr]),[1,[0,E([1,_gp,new T(function(){return B(_if([1,_Tx,_9],_gq));})])],_9]]]);});}else{var _Ty=function(_Tz,_TA,_TB,_TC){var _TD=[0,E([0,_Tz,_TA,_TB]),_9],_TE=[0,E([0,_Tz,_TA,_TB]),_da];return new F(function(){return _eL(_xu,[0,_Tw[2],E(_TC),E(_Ts)],function(_TF,_TG,_TH){return new F(function(){return _T3(_TG,_Tt,_Tu,function(_TI,_TJ,_TK){return new F(function(){return A(_Tt,[_TI,_TJ,new T(function(){return B(_e0(_TH,_TK));})]);});},function(_TL){return new F(function(){return A(_Tu,[new T(function(){return B(_e0(_TH,_TL));})]);});});});},_Tu,function(_TM,_TN,_TO){return new F(function(){return _T3(_TN,_Tt,_Tu,function(_TP,_TQ,_TR){return new F(function(){return A(_Tt,[_TP,_TQ,new T(function(){var _TS=E(_TO),_TT=E(_TS[1]),_TU=E(_TR),_TV=E(_TU[1]),_TW=B(_db(_TT[1],_TT[2],_TT[3],_TS[2],_TV[1],_TV[2],_TV[3],_TU[2])),_TX=E(_TW[1]),_TY=_TX[2],_TZ=_TX[3],_U0=E(_TW[2]);if(!_U0[0]){switch(B(_d3(_Tz,_TX[1]))){case 0:var _U1=[0,E(_TX),_9];break;case 1:if(_TA>=_TY){if(_TA!=_TY){var _U2=E(_TD);}else{if(_TB>=_TZ){var _U3=_TB!=_TZ?E(_TD):E(_TE);}else{var _U3=[0,E(_TX),_9];}var _U4=_U3,_U2=_U4;}var _U5=_U2,_U6=_U5;}else{var _U6=[0,E(_TX),_9];}var _U7=_U6,_U1=_U7;break;default:var _U1=E(_TD);}var _U8=_U1;}else{var _U8=[0,E(_TX),_U0];}var _U9=_U8,_Ua=_U9,_Ub=_Ua,_Uc=_Ub,_Ud=_Uc,_Ue=_Ud;return _Ue;})]);});},function(_Uf){return new F(function(){return A(_Tu,[new T(function(){var _Ug=E(_TO),_Uh=E(_Ug[1]),_Ui=E(_Uf),_Uj=E(_Ui[1]),_Uk=B(_db(_Uh[1],_Uh[2],_Uh[3],_Ug[2],_Uj[1],_Uj[2],_Uj[3],_Ui[2])),_Ul=E(_Uk[1]),_Um=_Ul[2],_Un=_Ul[3],_Uo=E(_Uk[2]);if(!_Uo[0]){switch(B(_d3(_Tz,_Ul[1]))){case 0:var _Up=[0,E(_Ul),_9];break;case 1:if(_TA>=_Um){if(_TA!=_Um){var _Uq=E(_TD);}else{if(_TB>=_Un){var _Ur=_TB!=_Un?E(_TD):E(_TE);}else{var _Ur=[0,E(_Ul),_9];}var _Us=_Ur,_Uq=_Us;}var _Ut=_Uq,_Uu=_Ut;}else{var _Uu=[0,E(_Ul),_9];}var _Uv=_Uu,_Up=_Uv;break;default:var _Up=E(_TD);}var _Uw=_Up;}else{var _Uw=[0,E(_Ul),_Uo];}var _Ux=_Uw,_Uy=_Ux,_Uz=_Uy,_UA=_Uz,_UB=_UA,_UC=_UB;return _UC;})]);});});});});});};switch(E(E(_Tx)[1])){case 9:var _UD=(_Tr+8|0)-B(_gt(_Tr-1|0,8))|0;return new F(function(){return _Ty(_Tp,_Tq,_UD,[0,_Tp,_Tq,_UD]);});break;case 10:var _UE=_Tq+1|0;return new F(function(){return _Ty(_Tp,_UE,1,[0,_Tp,_UE,1]);});break;default:var _UF=_Tr+1|0;return new F(function(){return _Ty(_Tp,_Tq,_UF,[0,_Tp,_Tq,_UF]);});}}}},_UG=function(_UH,_UI){return E(_1);},_UJ=function(_UK,_UL,_UM,_UN){var _UO=E(_UM);switch(_UO[0]){case 0:var _UP=E(_UN);return _UP[0]==0?E(_1):E(_UP[1]);case 1:return new F(function(){return A(_UK,[_UO[1],_9]);});break;case 2:return new F(function(){return A(_UL,[_UO[1],[1,new T(function(){return B(_UJ(_UK,_UL,_UO[2],_UN));}),_9]]);});break;default:return new F(function(){return A(_UL,[_UO[1],[1,new T(function(){return B(_UJ(_UK,_UL,_UO[2],_UN));}),[1,new T(function(){return B(_UJ(_UK,_UL,_UO[3],_UN));}),_9]]]);});}},_UQ=function(_UR,_US,_UT,_UU,_UV,_UW,_UX,_UY){var _UZ=E(_UX);switch(_UZ[0]){case 0:return [0];case 1:return new F(function(){return A(_UU,[_UZ[1],_9]);});break;case 2:return new F(function(){return A(_UR,[_UZ[1],[1,new T(function(){return B(_UJ(_UU,_UV,_UZ[2],_UY));}),_9]]);});break;case 3:return new F(function(){return A(_UR,[_UZ[1],[1,new T(function(){return B(_UJ(_UU,_UV,_UZ[2],_UY));}),[1,new T(function(){return B(_UJ(_UU,_UV,_UZ[3],_UY));}),_9]]]);});break;case 4:return new F(function(){return A(_US,[_UZ[1],[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,_UZ[2],_UY));}),_9]]);});break;case 5:return new F(function(){return A(_US,[_UZ[1],[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,_UZ[2],_UY));}),[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,_UZ[3],_UY));}),_9]]]);});break;default:var _V0=_UZ[1],_V1=_UZ[2];return new F(function(){return A(_UT,[_V0,[1,new T(function(){return B(A(_UW,[new T(function(){return B(A(_V1,[_2V]));}),_V0]));}),[1,new T(function(){return B(_UQ(_UR,_US,_UT,_UU,_UV,_UW,B(A(_V1,[_2V])),[1,new T(function(){return B(A(_UW,[new T(function(){return B(A(_V1,[_2V]));}),_V0]));}),_9]));}),_9]]]);});}},_V2=[0,95],_V3=[1,_V2,_9],_V4=[1,_V3,_9],_V5=function(_V6){var _V7=function(_V8){var _V9=E(new T(function(){var _Va=B(_Dq(_Cm,_S2,[0,_V6,E(_Cf),E(_6B)]));if(!_Va[0]){var _Vb=E(_Va[1]),_Vc=_Vb[0]==0?[1,_Vb[1]]:[0,_Vb[1]];}else{var _Vd=E(_Va[1]),_Vc=_Vd[0]==0?[1,_Vd[1]]:[0,_Vd[1]];}return _Vc;}));return _V9[0]==0?function(_Ve,_Vf,_Vg,_Vh,_Vi){return new F(function(){return A(_Vh,[[0,[0,new T(function(){var _Vj=E(_V9[1]),_Vk=E(_Vj[1]);return B(_bc(_Vk[1],_Vk[2],_Vk[3],_Vj[2]));})],_9],_Ve,new T(function(){return [0,E(E(_Ve)[2]),_9];})]);});}:function(_Vl,_Vm,_Vn,_Vo,_Vp){return new F(function(){return A(_Vo,[[0,[0,new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_V9[1],_V4));})],_9],_Vl,new T(function(){return [0,E(E(_Vl)[2]),_9];})]);});};};return function(_Vq,_Vr,_Vs,_Vt,_Vu){return new F(function(){return A(_xM,[_Vq,function(_Vv,_Vw,_Vx){return new F(function(){return A(_V7,[_,_Vw,_Vr,_Vs,function(_Vy,_Vz,_VA){return new F(function(){return A(_Vr,[_Vy,_Vz,new T(function(){return B(_e0(_Vx,_VA));})]);});},function(_VB){return new F(function(){return A(_Vs,[new T(function(){return B(_e0(_Vx,_VB));})]);});}]);});},_Vs,function(_VC,_VD,_VE){return new F(function(){return A(_V7,[_,_VD,_Vr,_Vs,function(_VF,_VG,_VH){return new F(function(){return A(_Vt,[_VF,_VG,new T(function(){return B(_e0(_VE,_VH));})]);});},function(_VI){return new F(function(){return A(_Vu,[new T(function(){return B(_e0(_VE,_VI));})]);});}]);});},_Vu]);});};},_VJ=function(_VK,_VL,_VM,_VN,_VO,_VP,_VQ,_VR,_VS,_VT){return new F(function(){return _il(_VK,_VL,function(_VU){return !B(_9r(_iN,_VU,_VM))?true:false;},_VN,_VO,_VP,_VQ,_VR,_VS,_VT);});},_VV=[0,9],_VW=[1,_VV,_9],_VX=[0,10],_VY=[1,_VX,_VW],_VZ=function(_W0,_W1,_W2,_W3,_W4){var _W5=E(_W0),_W6=E(_W5[2]);return new F(function(){return _VJ(_gm,_j5,_VY,_W5[1],_W6[1],_W6[2],_W6[3],_W5[3],_W1,_W4);});},_W7=function(_W8,_W9,_Wa,_Wb,_Wc){return new F(function(){return _e8(_VZ,_W8,function(_Wd,_We,_Wf){return new F(function(){return A(_V5,[_Wd,_We,_W9,_Wa,function(_Wg,_Wh,_Wi){return new F(function(){return A(_W9,[_Wg,_Wh,new T(function(){return B(_e0(_Wf,_Wi));})]);});},function(_Wj){return new F(function(){return A(_Wa,[new T(function(){return B(_e0(_Wf,_Wj));})]);});}]);});},_Wa,function(_Wk,_Wl,_Wm){return new F(function(){return A(_V5,[_Wk,_Wl,_W9,_Wa,function(_Wn,_Wo,_Wp){return new F(function(){return A(_Wb,[_Wn,_Wo,new T(function(){return B(_e0(_Wm,_Wp));})]);});},function(_Wq){return new F(function(){return A(_Wc,[new T(function(){return B(_e0(_Wm,_Wq));})]);});}]);});},_Wc);});},_Wr=function(_Ws,_Wt,_Wu,_Wv,_Ww,_Wx){var _Wy=function(_Wz,_WA,_WB,_WC,_WD,_WE){var _WF=function(_WG){var _WH=[0,[1,[0,_Ws,_Wz,new T(function(){return B(_3d(_v4,_WG));})]],_9];return function(_WI,_WJ,_WK,_WL,_WM){return new F(function(){return A(_xM,[_WI,function(_WN,_WO,_WP){return new F(function(){return A(_WJ,[_WH,_WO,new T(function(){var _WQ=E(E(_WO)[2]),_WR=E(_WP),_WS=E(_WR[1]),_WT=B(_db(_WS[1],_WS[2],_WS[3],_WR[2],_WQ[1],_WQ[2],_WQ[3],_9));return [0,E(_WT[1]),_WT[2]];})]);});},_WK,function(_WU,_WV,_WW){return new F(function(){return A(_WL,[_WH,_WV,new T(function(){var _WX=E(E(_WV)[2]),_WY=E(_WW),_WZ=E(_WY[1]),_X0=B(_db(_WZ[1],_WZ[2],_WZ[3],_WY[2],_WX[1],_WX[2],_WX[3],_9));return [0,E(_X0[1]),_X0[2]];})]);});},_WM]);});};},_X1=function(_X2,_X3,_X4,_X5,_X6){var _X7=function(_X8,_X9,_Xa){return new F(function(){return A(_WF,[_X8,_X9,_X3,_X4,function(_Xb,_Xc,_Xd){return new F(function(){return A(_X5,[_Xb,_Xc,new T(function(){return B(_e0(_Xa,_Xd));})]);});},function(_Xe){return new F(function(){return A(_X6,[new T(function(){return B(_e0(_Xa,_Xe));})]);});}]);});},_Xf=function(_Xg){return new F(function(){return _X7(_9,_X2,new T(function(){var _Xh=E(E(_X2)[2]),_Xi=E(_Xg),_Xj=E(_Xi[1]),_Xk=B(_db(_Xj[1],_Xj[2],_Xj[3],_Xi[2],_Xh[1],_Xh[2],_Xh[3],_9));return [0,E(_Xk[1]),_Xk[2]];}));});};return new F(function(){return _fb(_kk,_kL,_X2,function(_Xl,_Xm,_Xn){return new F(function(){return A(_WF,[_Xl,_Xm,_X3,_X4,function(_Xo,_Xp,_Xq){return new F(function(){return A(_X3,[_Xo,_Xp,new T(function(){return B(_e0(_Xn,_Xq));})]);});},function(_Xr){return new F(function(){return A(_X4,[new T(function(){return B(_e0(_Xn,_Xr));})]);});}]);});},_Xf,_X7,_Xf);});};return new F(function(){return _eL(_j7,_WA,function(_Xs,_Xt,_Xu){return new F(function(){return _X1(_Xt,_WB,_WC,function(_Xv,_Xw,_Xx){return new F(function(){return A(_WB,[_Xv,_Xw,new T(function(){return B(_e0(_Xu,_Xx));})]);});},function(_Xy){return new F(function(){return A(_WC,[new T(function(){return B(_e0(_Xu,_Xy));})]);});});});},_WC,function(_Xz,_XA,_XB){return new F(function(){return _X1(_XA,_WB,_WC,function(_XC,_XD,_XE){return new F(function(){return A(_WD,[_XC,_XD,new T(function(){return B(_e0(_XB,_XE));})]);});},function(_XF){return new F(function(){return A(_WE,[new T(function(){return B(_e0(_XB,_XF));})]);});});});});});},_XG=function(_XH,_XI,_XJ,_XK,_XL){return new F(function(){return _e8(_w2,_XH,function(_XM,_XN,_XO){return new F(function(){return _Wy(_XM,_XN,_XI,_XJ,function(_XP,_XQ,_XR){return new F(function(){return A(_XI,[_XP,_XQ,new T(function(){return B(_e0(_XO,_XR));})]);});},function(_XS){return new F(function(){return A(_XJ,[new T(function(){return B(_e0(_XO,_XS));})]);});});});},_XL,function(_XT,_XU,_XV){return new F(function(){return _Wy(_XT,_XU,_XI,_XJ,function(_XW,_XX,_XY){return new F(function(){return A(_XK,[_XW,_XX,new T(function(){return B(_e0(_XV,_XY));})]);});},function(_XZ){return new F(function(){return A(_XL,[new T(function(){return B(_e0(_XV,_XZ));})]);});});});},_XL);});};return new F(function(){return _eL(_j7,_Wt,function(_Y0,_Y1,_Y2){return new F(function(){return _XG(_Y1,_Wu,_Wv,function(_Y3,_Y4,_Y5){return new F(function(){return A(_Wu,[_Y3,_Y4,new T(function(){return B(_e0(_Y2,_Y5));})]);});},function(_Y6){return new F(function(){return A(_Wv,[new T(function(){return B(_e0(_Y2,_Y6));})]);});});});},_Wv,function(_Y7,_Y8,_Y9){return new F(function(){return _XG(_Y8,_Wu,_Wv,function(_Ya,_Yb,_Yc){return new F(function(){return A(_Ww,[_Ya,_Yb,new T(function(){return B(_e0(_Y9,_Yc));})]);});},function(_Yd){return new F(function(){return A(_Wx,[new T(function(){return B(_e0(_Y9,_Yd));})]);});});});});});},_Ye=function(_Yf,_Yg,_Yh,_Yi,_Yj){return new F(function(){return A(_S2,[_Yf,function(_Yk,_Yl,_Ym){return new F(function(){return _Wr(_Yk,_Yl,_Yg,_Yh,function(_Yn,_Yo,_Yp){return new F(function(){return A(_Yg,[_Yn,_Yo,new T(function(){return B(_e0(_Ym,_Yp));})]);});},function(_Yq){return new F(function(){return A(_Yh,[new T(function(){return B(_e0(_Ym,_Yq));})]);});});});},_Yh,function(_Yr,_Ys,_Yt){return new F(function(){return _Wr(_Yr,_Ys,_Yg,_Yh,function(_Yu,_Yv,_Yw){return new F(function(){return A(_Yi,[_Yu,_Yv,new T(function(){return B(_e0(_Yt,_Yw));})]);});},function(_Yx){return new F(function(){return A(_Yj,[new T(function(){return B(_e0(_Yt,_Yx));})]);});});});},_Yj]);});},_Yy=function(_Yz,_YA,_YB,_YC){var _YD=function(_YE){var _YF=E(_Yz),_YG=E(_YF[2]),_YH=function(_YI){var _YJ=function(_YK){return new F(function(){return A(_YC,[new T(function(){var _YL=E(_YE),_YM=E(_YL[1]),_YN=E(_YI),_YO=E(_YN[1]),_YP=E(_YK),_YQ=E(_YP[1]),_YR=B(_db(_YO[1],_YO[2],_YO[3],_YN[2],_YQ[1],_YQ[2],_YQ[3],_YP[2])),_YS=E(_YR[1]),_YT=B(_db(_YM[1],_YM[2],_YM[3],_YL[2],_YS[1],_YS[2],_YS[3],_YR[2]));return [0,E(_YT[1]),_YT[2]];})]);});};return new F(function(){return _W7(_YF,_YA,_YJ,function(_YU,_YV,_YW){return new F(function(){return A(_YB,[_YU,_YV,new T(function(){var _YX=E(_YE),_YY=E(_YX[1]),_YZ=E(_YI),_Z0=E(_YZ[1]),_Z1=E(_YW),_Z2=E(_Z1[1]),_Z3=B(_db(_Z0[1],_Z0[2],_Z0[3],_YZ[2],_Z2[1],_Z2[2],_Z2[3],_Z1[2])),_Z4=E(_Z3[1]),_Z5=B(_db(_YY[1],_YY[2],_YY[3],_YX[2],_Z4[1],_Z4[2],_Z4[3],_Z3[2]));return [0,E(_Z5[1]),_Z5[2]];})]);});},_YJ);});};return new F(function(){return _Tn(_YF[1],_YG[1],_YG[2],_YG[3],_YF[3],_YA,_YH,_YH);});};return new F(function(){return _Ye(_Yz,_YA,_YD,_YB,_YD);});},_Z6=function(_Z7,_Z8,_Z9,_Za,_Zb){return new F(function(){return _Yy(_Z7,_Z8,_Za,_Zb);});},_DM=function(_Zc,_Zd,_Ze,_Zf,_Zg){return new F(function(){return _e8(_Z6,_Zc,function(_Zh,_Zi,_Zj){return new F(function(){return _ws(_Zh,_Zi,_Zd,function(_Zk,_Zl,_Zm){return new F(function(){return A(_Zd,[_Zk,_Zl,new T(function(){return B(_e0(_Zj,_Zm));})]);});});});},_Ze,function(_Zn,_Zo,_Zp){return new F(function(){return _ws(_Zn,_Zo,_Zd,function(_Zq,_Zr,_Zs){return new F(function(){return A(_Zf,[_Zq,_Zr,new T(function(){return B(_e0(_Zp,_Zs));})]);});});});},_Zg);});},_Zt=function(_Zu,_Zv,_Zw){while(1){var _Zx=E(_Zv);if(!_Zx[0]){return E(_Zw)[0]==0?true:false;}else{var _Zy=E(_Zw);if(!_Zy[0]){return false;}else{if(!B(A(_9p,[_Zu,_Zx[1],_Zy[1]]))){return false;}else{_Zv=_Zx[2];_Zw=_Zy[2];continue;}}}}},_Zz=function(_ZA,_ZB,_ZC){var _ZD=E(_ZB),_ZE=E(_ZC);return !B(_Zt(_ZA,_ZD[1],_ZE[1]))?true:!B(A(_9p,[_ZA,_ZD[2],_ZE[2]]))?true:false;},_ZF=function(_ZG,_ZH,_ZI,_ZJ,_ZK){return !B(_Zt(_ZG,_ZH,_ZJ))?false:B(A(_9p,[_ZG,_ZI,_ZK]));},_ZL=function(_ZM,_ZN,_ZO){var _ZP=E(_ZN),_ZQ=E(_ZO);return new F(function(){return _ZF(_ZM,_ZP[1],_ZP[2],_ZQ[1],_ZQ[2]);});},_ZR=function(_ZS){return [0,function(_ZT,_ZU){return new F(function(){return _ZL(_ZS,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _Zz(_ZS,_ZT,_ZU);});}];},_ZV=function(_ZW,_ZX,_ZY){var _ZZ=E(_ZX),_100=E(_ZY);return !B(_Zt(_ZW,_ZZ[1],_100[1]))?true:!B(A(_9p,[_ZW,_ZZ[2],_100[2]]))?true:false;},_101=function(_102,_103,_104){var _105=E(_103),_106=E(_104);return new F(function(){return _ZF(_102,_105[1],_105[2],_106[1],_106[2]);});},_107=function(_108){return [0,function(_ZT,_ZU){return new F(function(){return _101(_108,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _ZV(_108,_ZT,_ZU);});}];},_109=function(_10a,_10b,_10c){var _10d=E(_10a);switch(_10d[0]){case 0:var _10e=E(_10b);return _10e[0]==0?!B(_3x(_10d[3],_10e[3]))?[0]:[1,_10c]:[0];case 1:var _10f=E(_10b);return _10f[0]==1?!B(_3x(_10d[3],_10f[3]))?[0]:[1,_10c]:[0];case 2:var _10g=E(_10b);return _10g[0]==2?!B(_3x(_10d[3],_10g[3]))?[0]:[1,_10c]:[0];case 3:var _10h=E(_10b);return _10h[0]==3?!B(_3x(_10d[3],_10h[3]))?[0]:[1,_10c]:[0];case 4:var _10i=E(_10b);return _10i[0]==4?!B(_3x(_10d[3],_10i[3]))?[0]:[1,_10c]:[0];case 5:var _10j=E(_10b);return _10j[0]==5?!B(_3x(_10d[3],_10j[3]))?[0]:[1,_10c]:[0];case 6:var _10k=E(_10b);return _10k[0]==6?!B(_3x(_10d[3],_10k[3]))?[0]:[1,_10c]:[0];case 7:var _10l=E(_10b);return _10l[0]==7?!B(_3x(_10d[3],_10l[3]))?[0]:[1,_10c]:[0];case 8:var _10m=E(_10b);return _10m[0]==8?!B(_3x(_10d[3],_10m[3]))?[0]:[1,_10c]:[0];default:var _10n=E(_10b);return _10n[0]==9?!B(_3x(_10d[3],_10n[3]))?[0]:[1,_10c]:[0];}},_10o=new T(function(){return B(_2L("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_10p=function(_10q,_10r,_10s){return [5,_,_10q,_10r,_10s];},_10t=function(_10u,_10v,_10w){return [10,_,_10u,_10v,_10w];},_10x=function(_10y,_10z,_10A){return [6,_,_10y,_10z,_10A];},_10B=function(_10C,_10D){return [12,_,_10C,_10D];},_10E=function(_10F,_10G){return [3,_,_10F,_10G];},_10H=function(_10I,_10J){return [8,_,_10I,_10J];},_10K=function(_10L,_10M){return [4,_,_10L,_10M];},_10N=function(_10O,_10P,_10Q){while(1){var _10R=E(_10Q);if(!_10R[0]){return [0];}else{var _10S=E(_10R[1]),_10T=B(A(_10O,[_10P,_10S[2],_10S[3]]));if(!_10T[0]){_10Q=_10R[2];continue;}else{return E(_10T);}}}},_10U=function(_10V,_10W){while(1){var _10X=(function(_10Y,_10Z){var _110=E(_10Z);switch(_110[0]){case 2:var _111=B(_10N(_109,_110[2],_10Y));if(!_111[0]){return E(_110);}else{var _112=_10Y;_10W=_111[1];_10V=_112;return null;}break;case 4:var _113=_110[3],_114=B(_10N(_109,_110[2],_10Y));if(!_114[0]){return E(_110);}else{var _115=E(_114[1]);switch(_115[0]){case 3:return E(_115[3])[0]==0?B(_10E(_115[2],_113)):E(_110);case 4:if(!E(_115[3])[0]){var _112=_10Y;_10W=B(_10K(_115[2],_113));_10V=_112;return null;}else{return E(_110);}break;default:return E(_110);}}break;case 6:var _116=_110[3],_117=_110[4],_118=B(_10N(_109,_110[2],_10Y));if(!_118[0]){return E(_110);}else{var _119=E(_118[1]);switch(_119[0]){case 5:if(!E(_119[3])[0]){if(!E(_119[4])[0]){var _112=_10Y;_10W=B(_10p(_119[2],_116,_117));_10V=_112;return null;}else{return E(_110);}}else{return E(_110);}break;case 6:if(!E(_119[3])[0]){if(!E(_119[4])[0]){var _112=_10Y;_10W=B(_10x(_119[2],_116,_117));_10V=_112;return null;}else{return E(_110);}}else{return E(_110);}break;default:return E(_110);}}break;case 7:return [7,_,_110[2],new T(function(){return B(_10U(_10Y,_110[3]));})];case 8:var _11a=_110[2],_11b=_110[3],_11c=B(_10N(_109,_11a,_10Y));if(!_11c[0]){return [8,_,_11a,new T(function(){return B(_10U(_10Y,_11b));})];}else{var _11d=E(_11c[1]);switch(_11d[0]){case 7:return E(_11d[3])[0]==0?[7,_,_11d[2],new T(function(){return B(_10U(_10Y,_11b));})]:[8,_,_11a,new T(function(){return B(_10U(_10Y,_11b));})];case 8:if(!E(_11d[3])[0]){var _112=_10Y;_10W=B(_10H(_11d[2],_11b));_10V=_112;return null;}else{return [8,_,_11a,new T(function(){return B(_10U(_10Y,_11b));})];}break;default:return [8,_,_11a,new T(function(){return B(_10U(_10Y,_11b));})];}}break;case 9:return [9,_,_110[2],new T(function(){return B(_10U(_10Y,_110[3]));}),new T(function(){return B(_10U(_10Y,_110[4]));})];case 10:var _11e=_110[2],_11f=_110[3],_11g=_110[4],_11h=B(_10N(_109,_11e,_10Y));if(!_11h[0]){return [10,_,_11e,new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];}else{var _11i=E(_11h[1]);switch(_11i[0]){case 9:if(!E(_11i[3])[0]){if(!E(_11i[4])[0]){var _112=_10Y;_10W=[9,_,_11i[2],new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];_10V=_112;return null;}else{return [10,_,_11e,new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];}}else{return [10,_,_11e,new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];}break;case 10:if(!E(_11i[3])[0]){if(!E(_11i[4])[0]){var _112=_10Y;_10W=B(_10t(_11i[2],_11f,_11g));_10V=_112;return null;}else{return [10,_,_11e,new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];}}else{return [10,_,_11e,new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];}break;default:return [10,_,_11e,new T(function(){return B(_10U(_10Y,_11f));}),new T(function(){return B(_10U(_10Y,_11g));})];}}break;case 11:return [11,_,_110[2],function(_11j){return new F(function(){return _10U(_10Y,B(A(_110[3],[_11j])));});}];case 12:var _11k=_110[2],_11l=_110[3],_11m=B(_10N(_109,_11k,_10Y));if(!_11m[0]){return [12,_,_11k,function(_11n){return new F(function(){return _10U(_10Y,B(A(_11l,[_11n])));});}];}else{var _11o=E(_11m[1]);switch(_11o[0]){case 11:return [11,_,_11o[2],function(_11p){return new F(function(){return _10U(_10Y,B(A(_11l,[_11p])));});}];case 12:var _112=_10Y;_10W=B(_10B(_11o[2],_11l));_10V=_112;return null;default:return [12,_,_11k,function(_11q){return new F(function(){return _10U(_10Y,B(A(_11l,[_11q])));});}];}}break;default:return E(_110);}})(_10V,_10W);if(_10X!=null){return _10X;}}},_11r=function(_11s,_11t){var _11u=E(_11t);if(!_11u[0]){var _11v=B(_10N(_109,_11u[1],_11s));if(!_11v[0]){return E(_11u);}else{var _11w=E(_11v[1]);return _11w[0]==0?E(_10o):[1,new T(function(){return B(_3d(function(_11x){return new F(function(){return _10U(_11s,_11x);});},_11w[1]));})];}}else{return [1,new T(function(){return B(_3d(function(_11y){return new F(function(){return _10U(_11s,_11y);});},_11u[1]));})];}},_11z=function(_11A,_11B,_11C,_11D,_11E,_11F,_11G,_11H,_11I){var _11J=E(_11I);return [0,new T(function(){return B(_3d(function(_11K){return new F(function(){return _11r(_11H,_11K);});},_11J[1]));}),new T(function(){return B(_11r(_11H,_11J[2]));})];},_11L=function(_11M,_11N,_11O,_11P,_11Q,_11R,_11S,_11T,_11U){var _11V=E(_11U);return [0,new T(function(){return B(_3d(function(_11W){return new F(function(){return _11z(_11M,_11N,_11O,_11P,_11Q,_11R,_11S,_11T,_11W);});},_11V[1]));}),new T(function(){return B(_11z(_11M,_11N,_11O,_11P,_11Q,_11R,_11S,_11T,_11V[2]));})];},_11X=function(_11Y){return E(E(_11Y)[1]);},_11Z=function(_120,_121){var _122=E(_121);return new F(function(){return A(_11X,[_122[1],E(_120)[2],_122[2]]);});},_123=function(_124,_125,_126){var _127=E(_126);if(!_127[0]){return [0];}else{var _128=_127[1],_129=_127[2];return !B(A(_124,[_125,_128]))?[1,_128,new T(function(){return B(_123(_124,_125,_129));})]:E(_129);}},_12a=function(_12b,_12c,_12d){while(1){var _12e=E(_12d);if(!_12e[0]){return false;}else{if(!B(A(_12b,[_12c,_12e[1]]))){_12d=_12e[2];continue;}else{return true;}}}},_12f=function(_12g,_12h){var _12i=function(_12j,_12k){while(1){var _12l=(function(_12m,_12n){var _12o=E(_12m);if(!_12o[0]){return [0];}else{var _12p=_12o[1],_12q=_12o[2];if(!B(_12a(_12g,_12p,_12n))){return [1,_12p,new T(function(){return B(_12i(_12q,[1,_12p,_12n]));})];}else{_12j=_12q;var _12r=_12n;_12k=_12r;return null;}}})(_12j,_12k);if(_12l!=null){return _12l;}}};return new F(function(){return _12i(_12h,_9);});},_12s=function(_12t,_12u,_12v){return new F(function(){return _e(_12u,new T(function(){return B((function(_12w,_12x){while(1){var _12y=E(_12x);if(!_12y[0]){return E(_12w);}else{var _12z=B(_123(_12t,_12y[1],_12w));_12x=_12y[2];_12w=_12z;continue;}}})(B(_12f(_12t,_12v)),_12u));},1));});},_12A=function(_12B,_12C){while(1){var _12D=(function(_12E,_12F){var _12G=E(_12F);switch(_12G[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12E,_12G[2]],_9];case 3:var _12H=_12E;_12C=_12G[3];_12B=_12H;return null;case 4:return new F(function(){return _12s(_11Z,[1,[0,_12E,_12G[2]],_9],new T(function(){return B(_12A(_12E,_12G[3]));},1));});break;case 5:return new F(function(){return _12s(_11Z,B(_12A(_12E,_12G[3])),new T(function(){return B(_12A(_12E,_12G[4]));},1));});break;default:return new F(function(){return _12s(_11Z,B(_12s(_11Z,[1,[0,_12E,_12G[2]],_9],new T(function(){return B(_12A(_12E,_12G[3]));},1))),new T(function(){return B(_12A(_12E,_12G[4]));},1));});}})(_12B,_12C);if(_12D!=null){return _12D;}}},_12I=function(_12J,_12K,_12L,_12M){while(1){var _12N=(function(_12O,_12P,_12Q,_12R){var _12S=E(_12R);switch(_12S[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12O,_12S[2]],_9];case 3:return new F(function(){return _12A(_12O,_12S[3]);});break;case 4:return new F(function(){return _12s(_11Z,[1,[0,_12O,_12S[2]],_9],new T(function(){return B(_12A(_12O,_12S[3]));},1));});break;case 5:return new F(function(){return _12s(_11Z,B(_12A(_12O,_12S[3])),new T(function(){return B(_12A(_12O,_12S[4]));},1));});break;case 6:return new F(function(){return _12s(_11Z,B(_12s(_11Z,[1,[0,_12O,_12S[2]],_9],new T(function(){return B(_12A(_12O,_12S[3]));},1))),new T(function(){return B(_12A(_12O,_12S[4]));},1));});break;case 7:var _12T=_12O,_12U=_12P,_12V=_12Q;_12M=_12S[3];_12J=_12T;_12K=_12U;_12L=_12V;return null;case 8:return new F(function(){return _12s(_11Z,[1,[0,_12O,_12S[2]],_9],new T(function(){return B(_12I(_12O,_12P,_12Q,_12S[3]));},1));});break;case 9:return new F(function(){return _12s(_11Z,B(_12I(_12O,_12P,_12Q,_12S[3])),new T(function(){return B(_12I(_12O,_12P,_12Q,_12S[4]));},1));});break;case 10:return new F(function(){return _12s(_11Z,B(_12s(_11Z,[1,[0,_12O,_12S[2]],_9],new T(function(){return B(_12I(_12O,_12P,_12Q,_12S[3]));},1))),new T(function(){return B(_12I(_12O,_12P,_12Q,_12S[4]));},1));});break;case 11:var _12T=_12O,_12U=_12P,_12V=_12Q;_12M=B(A(_12S[3],[_2V]));_12J=_12T;_12K=_12U;_12L=_12V;return null;default:return new F(function(){return _12s(_11Z,[1,[0,_12O,_12S[2]],_9],new T(function(){return B(_12I(_12O,_12P,_12Q,B(A(_12S[3],[_2V]))));},1));});}})(_12J,_12K,_12L,_12M);if(_12N!=null){return _12N;}}},_12W=function(_12X,_12Y,_12Z,_130,_131){var _132=function(_133){return new F(function(){return _12I(_12X,_12Y,_12Z,_133);});};return new F(function(){return _e(B(_8Q(B(_3d(function(_134){var _135=E(_134);if(!_135[0]){return [1,[0,_12X,_135[1]],_9];}else{return new F(function(){return _8Q(B(_3d(_132,_135[1])));});}},_130)))),new T(function(){var _136=E(_131);if(!_136[0]){var _137=[1,[0,_12X,_136[1]],_9];}else{var _137=B(_8Q(B(_3d(_132,_136[1]))));}return _137;},1));});},_138=function(_139,_13a,_13b,_13c,_13d,_13e,_13f,_13g,_13h){var _13i=E(_13h);return new F(function(){return _e(B(_8Q(B(_3d(function(_13j){var _13k=E(_13j);return new F(function(){return _12W(_139,_13d,_13e,_13k[1],_13k[2]);});},_13i[1])))),new T(function(){var _13l=E(_13i[2]);return B(_12W(_139,_13d,_13e,_13l[1],_13l[2]));},1));});},_13m=function(_13n,_13o,_13p,_13q,_13r,_13s,_13t,_13u,_13v,_13w,_13x){return [0,_13n,_13o,_13p,_13q,function(_11W){return new F(function(){return _138(_13n,_13r,_13s,_13t,_13u,_13v,_13w,_13x,_11W);});},function(_13y,_11W){return new F(function(){return _11L(_13r,_13s,_13t,_13u,_13v,_13w,_13x,_13y,_11W);});}];},_13z=function(_13A){return E(E(_13A)[2]);},_13B=function(_13C){return E(E(_13C)[1]);},_13D=[0,_13B,_13z],_13E=[0,125],_13F=new T(function(){return B(unCStr("given = "));}),_13G=new T(function(){return B(unCStr(", "));}),_13H=new T(function(){return B(unCStr("needed = "));}),_13I=new T(function(){return B(unCStr("AbsRule {"));}),_13J=[0,0],_13K=function(_13L){return E(E(_13L)[3]);},_13M=function(_13N){return E(E(_13N)[1]);},_13O=function(_13P,_13Q,_13R,_13S){var _13T=function(_13U){return new F(function(){return _e(_13I,new T(function(){return B(_e(_13H,new T(function(){return B(A(new T(function(){return B(A(_13K,[_13P,_13R]));}),[new T(function(){return B(_e(_13G,new T(function(){return B(_e(_13F,new T(function(){return B(A(new T(function(){return B(A(_13M,[_13P,_13J,_13S]));}),[[1,_13E,_13U]]));},1)));},1)));})]));},1)));},1));});};return _13Q<11?E(_13T):function(_13V){return [1,_E,new T(function(){return B(_13T([1,_D,_13V]));})];};},_13W=function(_13X,_13Y){var _13Z=E(_13Y);return new F(function(){return A(_13O,[_13X,0,_13Z[1],_13Z[2],_9]);});},_140=function(_141,_142,_143){return new F(function(){return _23(function(_144){var _145=E(_144);return new F(function(){return _13O(_141,0,_145[1],_145[2]);});},_142,_143);});},_146=function(_147,_148,_149){var _14a=E(_149);return new F(function(){return _13O(_147,E(_148)[1],_14a[1],_14a[2]);});},_14b=function(_14c){return [0,function(_ZT,_ZU){return new F(function(){return _146(_14c,_ZT,_ZU);});},function(_ZU){return new F(function(){return _13W(_14c,_ZU);});},function(_ZT,_ZU){return new F(function(){return _140(_14c,_ZT,_ZU);});}];},_14d=new T(function(){return B(unCStr("Sequent "));}),_14e=[0,11],_14f=[0,32],_14g=function(_14h,_14i,_14j,_14k){var _14l=new T(function(){return B(A(_13M,[_14h,_14e,_14k]));}),_14m=new T(function(){return B(A(_13K,[_14h,_14j]));});return _14i<11?function(_14n){return new F(function(){return _e(_14d,new T(function(){return B(A(_14m,[[1,_14f,new T(function(){return B(A(_14l,[_14n]));})]]));},1));});}:function(_14o){return [1,_E,new T(function(){return B(_e(_14d,new T(function(){return B(A(_14m,[[1,_14f,new T(function(){return B(A(_14l,[[1,_D,_14o]]));})]]));},1)));})];};},_14p=function(_14q,_14r){var _14s=E(_14r);return new F(function(){return A(_14g,[_14q,0,_14s[1],_14s[2],_9]);});},_14t=function(_14u,_14v,_14w){return new F(function(){return _23(function(_14x){var _14y=E(_14x);return new F(function(){return _14g(_14u,0,_14y[1],_14y[2]);});},_14v,_14w);});},_14z=function(_14A,_14B,_14C){var _14D=E(_14C);return new F(function(){return _14g(_14A,E(_14B)[1],_14D[1],_14D[2]);});},_14E=function(_14F){return [0,function(_ZT,_ZU){return new F(function(){return _14z(_14F,_ZT,_ZU);});},function(_ZU){return new F(function(){return _14p(_14F,_ZU);});},function(_ZT,_ZU){return new F(function(){return _14t(_14F,_ZT,_ZU);});}];},_14G=function(_14H,_14I){return new F(function(){return _e(B(_1r(_14H)),_14I);});},_14J=function(_14K,_14L){return new F(function(){return _23(_14G,_14K,_14L);});},_14M=function(_14N,_14O,_14P){return new F(function(){return _e(B(_1r(_14O)),_14P);});},_14Q=[0,_14M,_1r,_14J],_14R=function(_14S,_14T,_14U,_14V,_14W,_14X,_14Y,_14Z,_150,_151,_152,_153){var _154=E(_153);return new F(function(){return _12W(_14S,_14Z,_150,_154[1],_154[2]);});},_155=function(_156,_157,_158,_159,_15a,_15b,_15c,_15d,_15e,_15f,_15g){return [0,_156,_157,_158,_159,function(_11W){return new F(function(){return _14R(_156,_157,_158,_159,_15a,_15b,_15c,_15d,_15e,_15f,_15g,_11W);});},function(_13y,_11W){return new F(function(){return _11z(_15a,_15b,_15c,_15d,_15e,_15f,_15g,_13y,_11W);});}];},_15h=function(_15i,_15j){return [0];},_15k=function(_15l,_15m,_15n,_15o,_15p,_15q,_15r,_15s,_15t,_15u,_15v,_15w,_15x,_15y){return [0,_15l,_15m,_15h,_1];},_15z=function(_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I,_15J,_15K,_15L){var _15M=E(_15L);if(!_15M[0]){return [1,[0,_15A,_15M[1]],_9];}else{return new F(function(){return _8Q(B(_3d(function(_15N){return new F(function(){return _12I(_15A,_15H,_15I,_15N);});},_15M[1])));});}},_15O=function(_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W,_15X,_15Y,_15Z){return [0,_15P,_15Q,_15R,_15S,function(_11W){return new F(function(){return _15z(_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W,_15X,_15Y,_15Z,_11W);});},_11r];},_160=new T(function(){return B(_Ci("w_syKi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r156}\n                  sv{tv ayol} [tv] quant{tv ayoj} [tv]"));}),_161=new T(function(){return B(_Ci("w_syKh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv ayoj} [tv]"));}),_162=new T(function(){return B(_Ci("w_syKg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv ayoi} [tv]"));}),_163=new T(function(){return B(_Ci("w_syKf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv ayol} [tv]"));}),_164=new T(function(){return B(_Ci("w_syKe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv ayoh} [tv]"));}),_165=new T(function(){return B(_Ci("w_syKd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv ayok} [tv]"));}),_166=new T(function(){return B(_Ci("w_syKj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14g}\n                  sv{tv ayol} [tv]"));}),_167=new T(function(){return B(_Ci("w_syKc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayoj} [tv]"));}),_168=new T(function(){return B(_Ci("w_syKb{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv ayoi} [tv]"));}),_169=new T(function(){return B(_Ci("w_syKa{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv ayol} [tv]"));}),_16a=new T(function(){return B(_Ci("w_syK9{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv ayoh} [tv]"));}),_16b=new T(function(){return B(_Ci("w_syK8{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayok} [tv]"));}),_16c=function(_16d,_16e){return function(_16f,_16g){var _16h=E(_16f);return _16h[0]==0?[1,[0,new T(function(){return B(_16i(_16d,_16e,_16b,_16a,_169,_168,_167,_165,_164,_163,_162,_161,_160,_166));}),_16h[1],_16g]]:[0];};},_16j=function(_16k){return [0,E(_16k)];},_16i=function(_16l,_16m,_16n,_16o,_16p,_16q,_16r,_16s,_16t,_16u,_16v,_16w,_16x,_16y){return [0,_16l,_16m,new T(function(){return B(_16c(_16l,_16m));}),_16j];},_16z=[1,_9],_16A=function(_16B,_16C){while(1){var _16D=E(_16B);if(!_16D[0]){return E(_16C);}else{_16B=_16D[2];var _16E=_16C+1|0;_16C=_16E;continue;}}},_16F=[0,95],_16G=[1,_16F,_9],_16H=[1,_16G,_9],_16I=function(_16J,_16K,_16L){return !B(_3x(B(A(_16J,[_16K,_16H])),B(A(_16J,[_16L,_16H]))))?true:false;},_16M=function(_16N){return [0,function(_16O,_16P){return new F(function(){return _3x(B(A(_16N,[_16O,_16H])),B(A(_16N,[_16P,_16H])));});},function(_44,_45){return new F(function(){return _16I(_16N,_44,_45);});}];},_16Q=function(_16R,_16S){return new F(function(){return _10U(_16R,_16S);});},_16T=function(_16U,_16V,_16W,_16X,_16Y,_16Z,_170,_171,_172,_173,_174){return [0,_16U,_16V,_16W,_16X,function(_175){return new F(function(){return _12I(_16U,_171,_172,_175);});},_16Q];},_176=new T(function(){return B(_Ci("w_soA3{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r156}\n                  sv{tv alxe} [tv] quant{tv alxc} [tv]"));}),_177=new T(function(){return B(_Ci("w_soA2{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv alxc} [tv]"));}),_178=new T(function(){return B(_Ci("w_soA1{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv alxb} [tv]"));}),_179=new T(function(){return B(_Ci("w_soA0{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv alxe} [tv]"));}),_17a=new T(function(){return B(_Ci("w_sozZ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv alxa} [tv]"));}),_17b=new T(function(){return B(_Ci("w_sozY{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv alxd} [tv]"));}),_17c=new T(function(){return B(_Ci("w_soA4{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14g}\n                  sv{tv alxe} [tv]"));}),_17d=new T(function(){return B(_Ci("w_sozX{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv alxc} [tv]"));}),_17e=new T(function(){return B(_Ci("w_sozW{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv alxb} [tv]"));}),_17f=new T(function(){return B(_Ci("w_sozV{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv alxe} [tv]"));}),_17g=new T(function(){return B(_Ci("w_sozU{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv alxa} [tv]"));}),_17h=new T(function(){return B(_Ci("w_sozT{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv alxd} [tv]"));}),_17i=function(_17j,_17k,_17l,_17m){var _17n=E(_17l);switch(_17n[0]){case 2:return [1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17n[2],_17m]];case 4:var _17p=_17n[2];if(!E(_17n[3])[0]){var _17q=E(_17m);switch(_17q[0]){case 3:return E(_17q[3])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17p,_17q]]:[0];case 4:return E(_17q[3])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17p,_17q]]:[0];default:return [0];}}else{return [0];}break;case 6:var _17r=_17n[2];if(!E(_17n[3])[0]){if(!E(_17n[4])[0]){var _17s=E(_17m);switch(_17s[0]){case 5:return E(_17s[3])[0]==0?E(_17s[4])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17r,_17s]]:[0]:[0];case 6:return E(_17s[3])[0]==0?E(_17s[4])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17r,_17s]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _17t=_17n[2];if(!E(_17n[3])[0]){var _17u=E(_17m);switch(_17u[0]){case 7:return E(_17u[3])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17t,_17u]]:[0];case 8:return E(_17u[3])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17t,_17u]]:[0];default:return [0];}}else{return [0];}break;case 10:var _17v=_17n[2];if(!E(_17n[3])[0]){if(!E(_17n[4])[0]){var _17w=E(_17m);switch(_17w[0]){case 9:return E(_17w[3])[0]==0?E(_17w[4])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17v,_17w]]:[0]:[0];case 10:return E(_17w[3])[0]==0?E(_17w[4])[0]==0?[1,[0,new T(function(){return B(_17o(_17j,_17k,_17h,_17g,_17f,_17e,_17d,_17b,_17a,_179,_178,_177,_176,_17c));}),_17v,_17w]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_17x=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_17y=function(_17z){var _17A=E(_17z);switch(_17A[0]){case 3:return [2,_,_17A];case 4:return [4,_,_17A,_V];case 5:return [6,_,_17A,_V,_V];case 6:return [8,_,_17A,_S];case 7:return [10,_,_17A,_S,_S];default:return E(_17x);}},_17o=function(_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,_17J,_17K,_17L,_17M,_17N,_17O){return [0,_17B,_17C,function(_17P,_17Q){return new F(function(){return _17i(_17B,_17C,_17P,_17Q);});},_17y];},_17R=function(_17S,_17T,_17U){return new F(function(){return _23(function(_17V,_17W){return new F(function(){return _e(B(A(_17S,[_17V,_16H])),_17W);});},_17T,_17U);});},_17X=function(_17Y){return [0,function(_17Z,_180,_181){return new F(function(){return _e(B(A(_17Y,[_180,_16H])),_181);});},function(_182){return new F(function(){return A(_17Y,[_182,_16H]);});},function(_44,_45){return new F(function(){return _17R(_17Y,_44,_45);});}];},_183=[1,_9],_184=function(_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18f,_18g){var _18h=E(_18f);if(_18h[0]==2){return E(_183);}else{var _18i=E(_18g);if(_18i[0]==2){return E(_183);}else{var _18j=function(_18k){var _18l=function(_18m){var _18n=function(_18o){var _18p=function(_18q){var _18r=function(_18s){var _18t=function(_18u){var _18v=function(_18w){var _18x=function(_18y){var _18z=function(_18A){var _18B=function(_18C){var _18D=function(_18E){var _18F=function(_18G){var _18H=E(_18h);switch(_18H[0]){case 1:var _18I=E(_18i);return _18I[0]==1?!B(A(_186,[_18H[2],_18I[2]]))?[0]:E(_183):[0];case 3:var _18J=E(_18i);return _18J[0]==3?!B(A(_185,[_18H[2],_18J[2]]))?[0]:E(_183):[0];case 4:var _18K=_18H[2],_18L=E(_18i);switch(_18L[0]){case 3:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[4,_,_18K,_V],[3,_,_18L[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[4,_,_18K,_V],[4,_,_18L[2],_V]]));}),_9]];default:return [0];}break;case 5:var _18N=E(_18i);return _18N[0]==5?!B(A(_185,[_18H[2],_18N[2]]))?[0]:E(_183):[0];case 6:var _18O=_18H[2],_18P=E(_18i);switch(_18P[0]){case 5:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[6,_,_18O,_V,_V],[5,_,_18P[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[6,_,_18O,_V,_V],[6,_,_18P[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _18Q=E(_18i);return _18Q[0]==7?!B(A(_187,[_18H[2],_18Q[2]]))?[0]:[1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18H[3],_18Q[3]]));}),_9]]:[0];case 8:var _18R=_18H[2],_18S=_18H[3],_18T=E(_18i);switch(_18T[0]){case 7:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[8,_,_18R,_S],[7,_,_18T[2],_S]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18S,_18T[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[8,_,_18R,_S],[8,_,_18T[2],_S]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18S,_18T[3]]));}),_9]]];default:return [0];}break;case 9:var _18U=E(_18i);return _18U[0]==9?!B(A(_187,[_18H[2],_18U[2]]))?[0]:[1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18H[3],_18U[3]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18H[4],_18U[4]]));}),_9]]]:[0];case 10:var _18V=_18H[2],_18W=_18H[3],_18X=_18H[4],_18Y=function(_18Z){var _190=E(_18i);switch(_190[0]){case 9:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[10,_,_18V,_S,_S],[9,_,_190[2],_S,_S]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18W,_190[3]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18X,_190[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,[10,_,_18V,_S,_S],[10,_,_190[2],_S,_S]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18W,_190[3]]));}),[1,new T(function(){return B(A(_18M,[_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d,_18e,_18X,_190[4]]));}),_9]]]];default:return [0];}};return E(_18W)[0]==0?E(_18X)[0]==0?E(_183):B(_18Y(_)):B(_18Y(_));default:return [0];}},_191=E(_18i);return _191[0]==10?E(_191[3])[0]==0?E(_191[4])[0]==0?E(_183):B(_18F(_)):B(_18F(_)):B(_18F(_));},_192=E(_18h);return _192[0]==8?E(_192[3])[0]==0?E(_183):B(_18D(_)):B(_18D(_));},_193=E(_18i);switch(_193[0]){case 6:return E(_193[3])[0]==0?E(_193[4])[0]==0?E(_183):B(_18B(_)):B(_18B(_));case 8:return E(_193[3])[0]==0?E(_183):B(_18B(_));default:return new F(function(){return _18B(_);});}},_194=E(_18h);return _194[0]==6?E(_194[3])[0]==0?E(_194[4])[0]==0?E(_183):B(_18z(_)):B(_18z(_)):B(_18z(_));},_195=E(_18i);return _195[0]==4?E(_195[3])[0]==0?E(_183):B(_18x(_)):B(_18x(_));},_196=E(_18h);switch(_196[0]){case 4:return E(_196[3])[0]==0?E(_183):B(_18v(_));case 9:return E(_196[3])[0]==0?E(_196[4])[0]==0?E(_183):B(_18v(_)):B(_18v(_));default:return new F(function(){return _18v(_);});}},_197=E(_18i);return _197[0]==9?E(_197[3])[0]==0?E(_197[4])[0]==0?E(_183):B(_18t(_)):B(_18t(_)):B(_18t(_));},_198=E(_18h);return _198[0]==7?E(_198[3])[0]==0?E(_183):B(_18r(_)):B(_18r(_));},_199=E(_18i);switch(_199[0]){case 5:return E(_199[3])[0]==0?E(_199[4])[0]==0?E(_183):B(_18p(_)):B(_18p(_));case 7:return E(_199[3])[0]==0?E(_183):B(_18p(_));default:return new F(function(){return _18p(_);});}},_19a=E(_18h);return _19a[0]==5?E(_19a[3])[0]==0?E(_19a[4])[0]==0?E(_183):B(_18n(_)):B(_18n(_)):B(_18n(_));},_19b=E(_18i);return _19b[0]==3?E(_19b[3])[0]==0?E(_183):B(_18l(_)):B(_18l(_));},_19c=E(_18h);return _19c[0]==3?E(_19c[3])[0]==0?E(_183):B(_18j(_)):B(_18j(_));}}},_19d=function(_19e,_19f,_19g){return [0,_19e,_19f,_19g];},_19h=new T(function(){return B(_Ci("w_soAc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv alwz} [tv]"));}),_19i=new T(function(){return B(_Ci("w_soA8{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv alwA} [tv]"));}),_19j=function(_19k){return [0,function(_19l,_19m){return B(A(_19k,[_19l,_19m,_1]))[0]==0?false:true;},function(_19n,_19o){return B(A(_19k,[_19n,_19o,_1]))[0]==0?true:false;}];},_19p=new T(function(){return B(_19j(_109));}),_18M=function(_19q,_19r,_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z){var _19A=function(_19B,_19C){return new F(function(){return _2W(_19u,_19w,_19x,_19v,_19t,_19y,_19z,_19B);});};return function(_ma,_19D){return new F(function(){return _19d(new T(function(){return B(_17o(function(_19E,_19F){return new F(function(){return _184(_19q,_19r,_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19E,_19F);});},new T(function(){return B(_16T(_19p,_14Q,new T(function(){return B(_16M(_19A));}),new T(function(){return B(_17X(_19A));}),_19u,_19w,_19x,_19t,_19v,_19y,_19z));}),_19i,_19q,_19r,_19s,_19h,_19t,_19u,_19v,_19w,_19x,_19y,_19z));}),_ma,_19D);});};},_19G=function(_19H,_19I,_19J){var _19K=E(_19I);if(!_19K[0]){return [0];}else{var _19L=E(_19J);return _19L[0]==0?[0]:[1,new T(function(){return B(A(_19H,[_19K[1],_19L[1]]));}),new T(function(){return B(_19G(_19H,_19K[2],_19L[2]));})];}},_19M=function(_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U,_19V,_19W,_19X,_19Y){var _19Z=E(_19X);if(!_19Z[0]){return E(_16z);}else{var _1a0=_19Z[1],_1a1=E(_19Y);if(!_1a1[0]){return E(_16z);}else{var _1a2=_1a1[1];return B(_16A(_1a0,0))!=B(_16A(_1a2,0))?[0]:[1,new T(function(){return B(_19G(new T(function(){return B(_18M(_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U,_19V,_19W));}),_1a0,_1a2));})];}}},_1a3=new T(function(){return B(_Ci("w_syL3{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayo1} [tv]"));}),_1a4=new T(function(){return B(_Ci("w_syL7{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayo0} [tv]"));}),_1a5=new T(function(){return B(_19j(_109));}),_1a6=function(_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag){var _1ah=new T(function(){return B(_16i(function(_1ai,_1aj){return new F(function(){return _19M(_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag,_1ai,_1aj);});},new T(function(){return B(_15O(_1a5,_14Q,new T(function(){return B(_3W(_1ab,_1ad,_1ae,_1aa,_1ac,_1af,_1ag));}),new T(function(){return B(_bI(_1ab,_1ad,_1ae,_1aa,_1ac,_1af,_1ag));}),_1ab,_1ad,_1ae,_1aa,_1ac,_1af,_1ag));}),_1a3,_1a7,_1a8,_1a9,_1a4,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag));});return function(_1ak,_1al){var _1am=E(_1ak),_1an=_1am[1],_1ao=E(_1al),_1ap=_1ao[1];return B(_16A(_1an,0))!=B(_16A(_1ap,0))?[0]:[1,[1,[0,_1ah,_1am[2],_1ao[2]],new T(function(){return B(_19G(function(_13y,_11W){return [0,_1ah,_13y,_11W];},_1an,_1ap));})]];};},_1aq=new T(function(){return B(_Ci("w_syNF{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayny} [tv]"));}),_1ar=new T(function(){return B(_Ci("w_syNJ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aynx} [tv]"));}),_1as=function(_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC){var _1aD=new T(function(){return B(_15k(new T(function(){return B(_1a6(_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC));}),new T(function(){return B(_155(_1a5,_14Q,new T(function(){return B(_107(new T(function(){return B(_3W(_1ax,_1az,_1aA,_1aw,_1ay,_1aB,_1aC));})));}),new T(function(){return B(_14E(new T(function(){return B(_bI(_1ax,_1az,_1aA,_1aw,_1ay,_1aB,_1aC));})));}),_1ax,_1az,_1aA,_1aw,_1ay,_1aB,_1aC));}),_1aq,_1at,_1au,_1av,_1ar,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC));});return function(_1aE,_1aF){var _1aG=E(_1aE),_1aH=_1aG[1],_1aI=E(_1aF),_1aJ=_1aI[1];return B(_16A(_1aH,0))!=B(_16A(_1aJ,0))?[0]:[1,[1,[0,_1aD,_1aG[2],_1aI[2]],new T(function(){return B(_19G(function(_13y,_11W){return [0,_1aD,_13y,_11W];},_1aH,_1aJ));})]];};},_1aK=function(_1aL,_1aM){while(1){var _1aN=E(_1aM);if(!_1aN[0]){return false;}else{var _1aO=E(_1aN[1]);if(!B(A(_11X,[_1aO[1],_1aL,_1aO[2]]))){_1aM=_1aN[2];continue;}else{return true;}}}},_1aP=[0,_9],_1aQ=function(_1aR,_1aS,_1aT,_1aU,_1aV,_1aW,_1aX,_1aY,_1aZ,_1b0,_1b1){var _1b2=E(_1aU);return !B(A(_1b2[1],[new T(function(){return B(A(_1aZ,[_1b0]));}),_1b1]))?!B(_1aK(_1b0,B(A(_1aW,[_1b1]))))?[0,[1,[0,[0,_1aR,[0,_1aS,_1aT,_1b2,_1aV,_1aW,_1aX],_1aY,_1aZ],_1b0,_1b1],_9]]:[1,[1,_,[0,_1aR,[0,_1aS,_1aT,_1b2,_1aV,_1aW,_1aX],_1aY,_1aZ],[3,_1aT,_1aV,_1b0,_1b1]]]:E(_1aP);},_1b3=function(_1b4){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(54,15)-(56,42)|case");});},_1b5=new T(function(){return B(_1b3(_));}),_1b6=new T(function(){return B(unCStr(": empty list"));}),_1b7=new T(function(){return B(unCStr("Prelude."));}),_1b8=function(_1b9){return new F(function(){return err(B(_e(_1b7,new T(function(){return B(_e(_1b9,_1b6));},1))));});},_1ba=new T(function(){return B(unCStr("head"));}),_1bb=new T(function(){return B(_1b8(_1ba));}),_1bc=function(_1bd){return E(E(_1bd)[2]);},_1be=function(_1bf,_1bg){while(1){var _1bh=E(_1bf);if(!_1bh){return E(_1bg);}else{var _1bi=E(_1bg);if(!_1bi[0]){return [0];}else{_1bf=_1bh-1|0;_1bg=_1bi[2];continue;}}}},_1bj=function(_1bk,_1bl){var _1bm=E(_1bk)[1];return _1bm>=0?B(_1be(_1bm,_1bl)):E(_1bl);},_1bn=function(_1bo){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:96:31-64|function conc");});},_1bp=new T(function(){return B(_1bn(_));}),_1bq=function(_1br){var _1bs=E(_1br);switch(_1bs[0]){case 3:return [2,_,_1bs];case 4:return [4,_,_1bs,_V];case 5:return [6,_,_1bs,_V,_V];case 6:return [8,_,_1bs,_S];case 7:return [10,_,_1bs,_S,_S];default:return E(_17x);}},_1bt=function(_1bu){var _1bv=E(_1bu);if(!_1bv[0]){return [0];}else{var _1bw=E(_1bv[1]);if(!_1bw[0]){return [0];}else{return new F(function(){return _e(_1bw[1],new T(function(){return B(_1bt(_1bv[2]));},1));});}}},_1bx=function(_1by){var _1bz=E(_1by);return [0,[1,[1,new T(function(){return B(_1bt(_1bz[1]));})],_9],_1bz[2]];},_1bA=function(_1bB,_1bC,_1bD){return !B(_9r(_1bB,_1bC,_1bD))?E(_1bD):[1,_1bC,new T(function(){return B(_8T(function(_1bE){return !B(A(_9p,[_1bB,_1bE,_1bC]))?true:false;},_1bD));})];},_1bF=function(_1bG,_1bH,_1bI,_1bJ,_1bK,_1bL,_1bM){return function(_1bN,_1bO){var _1bP=E(_1bN);if(!_1bP[0]){return new F(function(){return _1bx(_1bO);});}else{var _1bQ=E(_1bO);return [0,[1,[1,new T(function(){return B(_1bA(new T(function(){return B(_16M(function(_1bR,_1bS){return new F(function(){return _2W(_1bM,_1bL,_1bK,_1bI,_1bJ,_1bG,_1bH,_1bR);});}));}),_1bP[1],B(_1bt(_1bQ[1]))));})],_9],_1bQ[2]];}};},_1bT=new T(function(){return B(_19j(_109));}),_1bU=function(_1bV){return E(E(_1bV)[1]);},_1bW=function(_1bX,_1bY){var _1bZ=E(_1bX);if(!_1bZ){return [0];}else{var _1c0=E(_1bY);return _1c0[0]==0?[0]:[1,_1c0[1],new T(function(){return B(_1bW(_1bZ-1|0,_1c0[2]));})];}},_1c1=function(_1c2,_1c3){return _1c2<0?[0]:B(_1bW(_1c2,_1c3));},_1c4=function(_1c5,_1c6){var _1c7=E(_1c5)[1];return _1c7>0?B(_1c1(_1c7,_1c6)):[0];},_1c8=function(_1c9,_1ca){return [1,_,_1c9,_1ca];},_1cb=function(_1cc){return E(E(_1cc)[2]);},_1cd=function(_1ce){return E(E(_1ce)[4]);},_1cf=function(_1cg,_1ch,_1ci){var _1cj=E(_1cg),_1ck=E(_1cj[2]);return new F(function(){return _1aQ(_1cj[1],_1ck[1],_1ck[2],_1ck[3],_1ck[4],_1ck[5],_1ck[6],_1cj[3],_1cj[4],_1ch,_1ci);});},_1cl=function(_1cm,_1cn,_1co,_1cp,_1cq,_1cr){var _1cs=B(A(_1co,[_1cq,_1cr]));if(!_1cs[0]){var _1ct=B(A(_1co,[_1cr,_1cq]));if(!_1ct[0]){var _1cu=B(A(_1cm,[_1cq,_1cr]));if(!_1cu[0]){return [1,[0,new T(function(){return B(_1cd(_1cn));}),_1cq,_1cr]];}else{var _1cv=B(_1cw([0,_1cm,_1cn,_1co,_1cp],_1cu[1]));return _1cv[0]==0?E(_1cv):[1,[2,new T(function(){return B(_1cd(_1cn));}),_1cv[1],_1cq,_1cr]];}}else{var _1cx=E(_1ct[1]);return new F(function(){return _1cf(_1cx[1],_1cx[2],_1cx[3]);});}}else{var _1cy=E(_1cs[1]);return new F(function(){return _1cf(_1cy[1],_1cy[2],_1cy[3]);});}},_1cz=function(_1cA){return E(E(_1cA)[6]);},_1cw=function(_1cB,_1cC){var _1cD=E(_1cC);if(!_1cD[0]){return E(_1aP);}else{var _1cE=E(_1cD[1]),_1cF=E(_1cE[1]),_1cG=B(_1cl(_1cF[1],_1cF[2],_1cF[3],_1cF[4],_1cE[2],_1cE[3]));if(!_1cG[0]){var _1cH=_1cG[1],_1cI=B(_1cw(_1cB,B(_3d(function(_1cJ){var _1cK=E(_1cJ),_1cL=_1cK[1];return [0,_1cL,new T(function(){return B(A(_1cz,[B(_1cb(_1cL)),_1cH,_1cK[2]]));}),new T(function(){return B(A(_1cz,[B(_1cb(_1cL)),_1cH,_1cK[3]]));})];},_1cD[2]))));if(!_1cI[0]){var _1cM=_1cI[1];return [0,new T(function(){var _1cN=function(_1cO){var _1cP=E(_1cO);return _1cP[0]==0?E(_1cM):[1,new T(function(){var _1cQ=E(_1cP[1]),_1cR=_1cQ[1];return [0,_1cR,_1cQ[2],new T(function(){return B(A(_1cz,[B(_1cb(_1cR)),_1cM,_1cQ[3]]));})];}),new T(function(){return B(_1cN(_1cP[2]));})];};return B(_1cN(_1cH));})];}else{return [1,new T(function(){return B(_1c8(_1cB,_1cI[1]));})];}}else{return [1,[1,_,_1cF,_1cG[1]]];}}},_1cS=function(_1cT,_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ,_1d0,_1d1,_1d2,_1d3,_1d4){var _1d5=new T(function(){return B(_1bc(_1d4));}),_1d6=function(_1d7,_1d8){return new F(function(){return _2W(_1cZ,_1cY,_1cX,_1cV,_1cW,_1cT,_1cU,_1d7);});},_1d9=new T(function(){return B(_16T(_1bT,_14Q,new T(function(){return B(_16M(_1d6));}),new T(function(){return B(_17X(_1d6));}),_1cZ,_1cY,_1cX,_1cW,_1cV,_1cT,_1cU));}),_1da=function(_1db,_1dc){return new F(function(){return _184(_1d3,_1d1,_1d2,_1cW,_1cZ,_1cV,_1cY,_1cX,_1cT,_1cU,_1db,_1dc);});};return function(_1dd,_1de,_1df){var _1dg=new T(function(){return B(A(_1d0,[_1df]));});return [0,new T(function(){return B(_19G(function(_1dh,_1di){var _1dj=B(A(new T(function(){return B(_1bF(_1cT,_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ));}),[new T(function(){var _1dk=E(E(_1di)[1]);if(!_1dk[0]){var _1dl=[0];}else{var _1dm=E(_1dk[1]),_1dl=_1dm[0]==0?[0]:[1,new T(function(){var _1dn=E(_1dm[1]);return _1dn[0]==0?E(_1bb):B(_10U(new T(function(){var _1do=E(B(A(_1d5,[_1dd]))[2]);if(!_1do[0]){var _1dp=E(_1bp);}else{var _1dq=E(_1do[1]);if(!_1dq[0]){var _1dr=E(_1bp);}else{var _1ds=_1dq[1];if(!E(_1dq[2])[0]){var _1dt=B(_17i(_1da,_1d9,_1ds,_1dg));if(!_1dt[0]){var _1du=B(_17i(_1da,_1d9,_1dg,_1ds));if(!_1du[0]){var _1dv=B(_1da(_1ds,_1dg));if(!_1dv[0]){var _1dw=[0];}else{var _1dx=B(_1cw([0,_1da,_1d9,function(_1dy,_1dz){return new F(function(){return _17i(_1da,_1d9,_1dy,_1dz);});},_1bq],_1dv[1])),_1dw=_1dx[0]==0?E(_1dx[1]):[0];}var _1dA=_1dw;}else{var _1dB=E(_1du[1]),_1dC=E(_1dB[1]),_1dD=E(_1dC[2]),_1dE=B(_1aQ(_1dC[1],_1dD[1],_1dD[2],_1dD[3],_1dD[4],_1dD[5],_1dD[6],_1dC[3],_1dC[4],_1dB[2],_1dB[3])),_1dA=_1dE[0]==0?E(_1dE[1]):[0];}var _1dF=_1dA;}else{var _1dG=E(_1dt[1]),_1dH=E(_1dG[1]),_1dI=E(_1dH[2]),_1dJ=B(_1aQ(_1dH[1],_1dI[1],_1dI[2],_1dI[3],_1dI[4],_1dI[5],_1dI[6],_1dH[3],_1dH[4],_1dG[2],_1dG[3])),_1dF=_1dJ[0]==0?E(_1dJ[1]):[0];}var _1dK=_1dF;}else{var _1dK=E(_1bp);}var _1dr=_1dK;}var _1dp=_1dr;}var _1dL=_1dp;return _1dL;}),_1dn[1]));})];}var _1dM=_1dl;return _1dM;}),_1dh])),_1dN=_1dj[2],_1dO=E(E(_1di)[1]);if(!_1dO[0]){return E(_1b5);}else{var _1dP=E(_1dO[1]);if(!_1dP[0]){return E(_1dO[2])[0]==0?E(_1dj):E(_1b5);}else{var _1dQ=E(_1dj[1]);if(!_1dQ[0]){return [0,_9,_1dN];}else{var _1dR=E(_1dQ[1]);if(!_1dR[0]){return E(_1dj);}else{var _1dS=_1dR[1],_1dT=new T(function(){return [0,B(_16A(_1dP[1],0))];});return [0,[1,[1,new T(function(){return B(_1c4(_1dT,_1dS));})],[1,[1,new T(function(){return B(_1bj(_1dT,_1dS));})],_1dQ[2]]],_1dN];}}}}},_1de,new T(function(){return B(A(new T(function(){return B(_1bU(_1d4));}),[_1dd]));},1)));}),[0,new T(function(){return E(B(A(_1d5,[_1dd]))[1]);}),[1,[1,_1dg,_9]]]];};},_1dU=function(_1dV,_1dW){return [0];},_1dX=function(_1dY,_1dZ,_1e0,_1e1,_1e2,_1e3,_1e4,_1e5,_1e6,_1e7,_1e8){var _1e9=new T(function(){return B(_1cS(_1dY,_1dZ,_1e0,_1e1,_1e2,_1e3,_1e4,_1e5,_1e6,_1e7,_1e8,_13D));}),_1ea=new T(function(){return B(_1as(_1e8,_1e6,_1e7,_1e1,_1e4,_1e0,_1e3,_1e2,_1dY,_1dZ));}),_1eb=[0,_1ea,new T(function(){return B(_13m(_1bT,_14Q,new T(function(){return B(_ZR(new T(function(){return B(_107(new T(function(){return B(_3W(_1e4,_1e3,_1e2,_1e1,_1e0,_1dY,_1dZ));})));})));}),new T(function(){return B(_14b(new T(function(){return B(_14E(new T(function(){return B(_bI(_1e4,_1e3,_1e2,_1e1,_1e0,_1dY,_1dZ));})));})));}),_1e4,_1e3,_1e2,_1e1,_1e0,_1dY,_1dZ));}),_1dU,_1];return function(_1ec,_1ed,_1ee){var _1ef=B(_8T(function(_1eg){var _1eh=B(A(_1ea,[new T(function(){return B(A(_1e9,[_1eg,_1ed,_1ee]));}),_1eg]));return _1eh[0]==0?false:B(_1cw(_1eb,_1eh[1]))[0]==0?true:false;},E(_1ec)[1]));if(!_1ef[0]){return [0];}else{var _1ei=_1ef[1],_1ej=new T(function(){return B(A(_1e9,[_1ei,_1ed,_1ee]));}),_1ek=B(A(_1ea,[_1ei,_1ej]));if(!_1ek[0]){return [0];}else{var _1el=B(_1cw(_1eb,_1ek[1]));if(!_1el[0]){var _1em=_1el[1];return [1,new T(function(){var _1en=E(E(_1ej)[2]);return [0,new T(function(){return B(_3d(function(_1eo){return new F(function(){return _11r(_1em,_1eo);});},_1en[1]));}),new T(function(){return B(_11r(_1em,_1en[2]));})];})];}else{return [0];}}}};},_1ep=[1],_1eq=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1er=function(_1es){return new F(function(){return err(_1eq);});},_1et=new T(function(){return B(_1er(_));}),_1eu=function(_1ev,_1ew,_1ex){var _1ey=E(_1ex);if(!_1ey[0]){var _1ez=_1ey[1],_1eA=E(_1ew);if(!_1eA[0]){var _1eB=_1eA[1],_1eC=_1eA[2];if(_1eB<=(imul(3,_1ez)|0)){return [0,(1+_1eB|0)+_1ez|0,E(E(_1ev)),E(_1eA),E(_1ey)];}else{var _1eD=E(_1eA[3]);if(!_1eD[0]){var _1eE=_1eD[1],_1eF=E(_1eA[4]);if(!_1eF[0]){var _1eG=_1eF[1],_1eH=_1eF[2],_1eI=_1eF[3];if(_1eG>=(imul(2,_1eE)|0)){var _1eJ=function(_1eK){var _1eL=E(_1eF[4]);return _1eL[0]==0?[0,(1+_1eB|0)+_1ez|0,E(_1eH),E([0,(1+_1eE|0)+_1eK|0,E(_1eC),E(_1eD),E(_1eI)]),E([0,(1+_1ez|0)+_1eL[1]|0,E(E(_1ev)),E(_1eL),E(_1ey)])]:[0,(1+_1eB|0)+_1ez|0,E(_1eH),E([0,(1+_1eE|0)+_1eK|0,E(_1eC),E(_1eD),E(_1eI)]),E([0,1+_1ez|0,E(E(_1ev)),E(_1ep),E(_1ey)])];},_1eM=E(_1eI);return _1eM[0]==0?B(_1eJ(_1eM[1])):B(_1eJ(0));}else{return [0,(1+_1eB|0)+_1ez|0,E(_1eC),E(_1eD),E([0,(1+_1ez|0)+_1eG|0,E(E(_1ev)),E(_1eF),E(_1ey)])];}}else{return E(_1et);}}else{return E(_1et);}}}else{return [0,1+_1ez|0,E(E(_1ev)),E(_1ep),E(_1ey)];}}else{var _1eN=E(_1ew);if(!_1eN[0]){var _1eO=_1eN[1],_1eP=_1eN[2],_1eQ=_1eN[4],_1eR=E(_1eN[3]);if(!_1eR[0]){var _1eS=_1eR[1],_1eT=E(_1eQ);if(!_1eT[0]){var _1eU=_1eT[1],_1eV=_1eT[2],_1eW=_1eT[3];if(_1eU>=(imul(2,_1eS)|0)){var _1eX=function(_1eY){var _1eZ=E(_1eT[4]);return _1eZ[0]==0?[0,1+_1eO|0,E(_1eV),E([0,(1+_1eS|0)+_1eY|0,E(_1eP),E(_1eR),E(_1eW)]),E([0,1+_1eZ[1]|0,E(E(_1ev)),E(_1eZ),E(_1ep)])]:[0,1+_1eO|0,E(_1eV),E([0,(1+_1eS|0)+_1eY|0,E(_1eP),E(_1eR),E(_1eW)]),E([0,1,E(E(_1ev)),E(_1ep),E(_1ep)])];},_1f0=E(_1eW);return _1f0[0]==0?B(_1eX(_1f0[1])):B(_1eX(0));}else{return [0,1+_1eO|0,E(_1eP),E(_1eR),E([0,1+_1eU|0,E(E(_1ev)),E(_1eT),E(_1ep)])];}}else{return [0,3,E(_1eP),E(_1eR),E([0,1,E(E(_1ev)),E(_1ep),E(_1ep)])];}}else{var _1f1=E(_1eQ);return _1f1[0]==0?[0,3,E(_1f1[2]),E([0,1,E(_1eP),E(_1ep),E(_1ep)]),E([0,1,E(E(_1ev)),E(_1ep),E(_1ep)])]:[0,2,E(E(_1ev)),E(_1eN),E(_1ep)];}}else{return [0,1,E(E(_1ev)),E(_1ep),E(_1ep)];}}},_1f2=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_1f3=function(_1f4){return new F(function(){return err(_1f2);});},_1f5=new T(function(){return B(_1f3(_));}),_1f6=function(_1f7,_1f8,_1f9){var _1fa=E(_1f8);if(!_1fa[0]){var _1fb=_1fa[1],_1fc=E(_1f9);if(!_1fc[0]){var _1fd=_1fc[1],_1fe=_1fc[2];if(_1fd<=(imul(3,_1fb)|0)){return [0,(1+_1fb|0)+_1fd|0,E(E(_1f7)),E(_1fa),E(_1fc)];}else{var _1ff=E(_1fc[3]);if(!_1ff[0]){var _1fg=_1ff[1],_1fh=_1ff[2],_1fi=_1ff[3],_1fj=E(_1fc[4]);if(!_1fj[0]){var _1fk=_1fj[1];if(_1fg>=(imul(2,_1fk)|0)){var _1fl=function(_1fm){var _1fn=E(_1f7),_1fo=E(_1ff[4]);return _1fo[0]==0?[0,(1+_1fb|0)+_1fd|0,E(_1fh),E([0,(1+_1fb|0)+_1fm|0,E(_1fn),E(_1fa),E(_1fi)]),E([0,(1+_1fk|0)+_1fo[1]|0,E(_1fe),E(_1fo),E(_1fj)])]:[0,(1+_1fb|0)+_1fd|0,E(_1fh),E([0,(1+_1fb|0)+_1fm|0,E(_1fn),E(_1fa),E(_1fi)]),E([0,1+_1fk|0,E(_1fe),E(_1ep),E(_1fj)])];},_1fp=E(_1fi);return _1fp[0]==0?B(_1fl(_1fp[1])):B(_1fl(0));}else{return [0,(1+_1fb|0)+_1fd|0,E(_1fe),E([0,(1+_1fb|0)+_1fg|0,E(E(_1f7)),E(_1fa),E(_1ff)]),E(_1fj)];}}else{return E(_1f5);}}else{return E(_1f5);}}}else{return [0,1+_1fb|0,E(E(_1f7)),E(_1fa),E(_1ep)];}}else{var _1fq=E(_1f9);if(!_1fq[0]){var _1fr=_1fq[1],_1fs=_1fq[2],_1ft=_1fq[4],_1fu=E(_1fq[3]);if(!_1fu[0]){var _1fv=_1fu[1],_1fw=_1fu[2],_1fx=_1fu[3],_1fy=E(_1ft);if(!_1fy[0]){var _1fz=_1fy[1];if(_1fv>=(imul(2,_1fz)|0)){var _1fA=function(_1fB){var _1fC=E(_1f7),_1fD=E(_1fu[4]);return _1fD[0]==0?[0,1+_1fr|0,E(_1fw),E([0,1+_1fB|0,E(_1fC),E(_1ep),E(_1fx)]),E([0,(1+_1fz|0)+_1fD[1]|0,E(_1fs),E(_1fD),E(_1fy)])]:[0,1+_1fr|0,E(_1fw),E([0,1+_1fB|0,E(_1fC),E(_1ep),E(_1fx)]),E([0,1+_1fz|0,E(_1fs),E(_1ep),E(_1fy)])];},_1fE=E(_1fx);return _1fE[0]==0?B(_1fA(_1fE[1])):B(_1fA(0));}else{return [0,1+_1fr|0,E(_1fs),E([0,1+_1fv|0,E(E(_1f7)),E(_1ep),E(_1fu)]),E(_1fy)];}}else{return [0,3,E(_1fw),E([0,1,E(E(_1f7)),E(_1ep),E(_1ep)]),E([0,1,E(_1fs),E(_1ep),E(_1ep)])];}}else{var _1fF=E(_1ft);return _1fF[0]==0?[0,3,E(_1fs),E([0,1,E(E(_1f7)),E(_1ep),E(_1ep)]),E(_1fF)]:[0,2,E(E(_1f7)),E(_1ep),E(_1fq)];}}else{return [0,1,E(E(_1f7)),E(_1ep),E(_1ep)];}}},_1fG=function(_1fH){return [0,1,E(E(_1fH)),E(_1ep),E(_1ep)];},_1fI=function(_1fJ,_1fK){var _1fL=E(_1fK);if(!_1fL[0]){return new F(function(){return _1eu(_1fL[2],B(_1fI(_1fJ,_1fL[3])),_1fL[4]);});}else{return new F(function(){return _1fG(_1fJ);});}},_1fM=function(_1fN,_1fO){var _1fP=E(_1fO);if(!_1fP[0]){return new F(function(){return _1f6(_1fP[2],_1fP[3],B(_1fM(_1fN,_1fP[4])));});}else{return new F(function(){return _1fG(_1fN);});}},_1fQ=function(_1fR,_1fS,_1fT,_1fU,_1fV){return new F(function(){return _1f6(_1fT,_1fU,B(_1fM(_1fR,_1fV)));});},_1fW=function(_1fX,_1fY,_1fZ,_1g0,_1g1){return new F(function(){return _1eu(_1fZ,B(_1fI(_1fX,_1g0)),_1g1);});},_1g2=function(_1g3,_1g4,_1g5,_1g6,_1g7,_1g8){var _1g9=E(_1g4);if(!_1g9[0]){var _1ga=_1g9[1],_1gb=_1g9[2],_1gc=_1g9[3],_1gd=_1g9[4];if((imul(3,_1ga)|0)>=_1g5){if((imul(3,_1g5)|0)>=_1ga){return [0,(_1ga+_1g5|0)+1|0,E(E(_1g3)),E(_1g9),E([0,_1g5,E(_1g6),E(_1g7),E(_1g8)])];}else{return new F(function(){return _1f6(_1gb,_1gc,B(_1g2(_1g3,_1gd,_1g5,_1g6,_1g7,_1g8)));});}}else{return new F(function(){return _1eu(_1g6,B(_1ge(_1g3,_1ga,_1gb,_1gc,_1gd,_1g7)),_1g8);});}}else{return new F(function(){return _1fW(_1g3,_1g5,_1g6,_1g7,_1g8);});}},_1ge=function(_1gf,_1gg,_1gh,_1gi,_1gj,_1gk){var _1gl=E(_1gk);if(!_1gl[0]){var _1gm=_1gl[1],_1gn=_1gl[2],_1go=_1gl[3],_1gp=_1gl[4];if((imul(3,_1gg)|0)>=_1gm){if((imul(3,_1gm)|0)>=_1gg){return [0,(_1gg+_1gm|0)+1|0,E(E(_1gf)),E([0,_1gg,E(_1gh),E(_1gi),E(_1gj)]),E(_1gl)];}else{return new F(function(){return _1f6(_1gh,_1gi,B(_1g2(_1gf,_1gj,_1gm,_1gn,_1go,_1gp)));});}}else{return new F(function(){return _1eu(_1gn,B(_1ge(_1gf,_1gg,_1gh,_1gi,_1gj,_1go)),_1gp);});}}else{return new F(function(){return _1fQ(_1gf,_1gg,_1gh,_1gi,_1gj);});}},_1gq=function(_1gr,_1gs,_1gt){var _1gu=E(_1gs);if(!_1gu[0]){var _1gv=_1gu[1],_1gw=_1gu[2],_1gx=_1gu[3],_1gy=_1gu[4],_1gz=E(_1gt);if(!_1gz[0]){var _1gA=_1gz[1],_1gB=_1gz[2],_1gC=_1gz[3],_1gD=_1gz[4];if((imul(3,_1gv)|0)>=_1gA){if((imul(3,_1gA)|0)>=_1gv){return [0,(_1gv+_1gA|0)+1|0,E(E(_1gr)),E(_1gu),E(_1gz)];}else{return new F(function(){return _1f6(_1gw,_1gx,B(_1g2(_1gr,_1gy,_1gA,_1gB,_1gC,_1gD)));});}}else{return new F(function(){return _1eu(_1gB,B(_1ge(_1gr,_1gv,_1gw,_1gx,_1gy,_1gC)),_1gD);});}}else{return new F(function(){return _1fQ(_1gr,_1gv,_1gw,_1gx,_1gy);});}}else{return new F(function(){return _1fI(_1gr,_1gt);});}},_1gE=function(_1gF,_1gG,_1gH,_1gI){var _1gJ=E(_1gI);if(!_1gJ[0]){var _1gK=new T(function(){var _1gL=B(_1gE(_1gJ[1],_1gJ[2],_1gJ[3],_1gJ[4]));return [0,_1gL[1],_1gL[2]];});return [0,new T(function(){return E(E(_1gK)[1]);}),new T(function(){return B(_1eu(_1gG,_1gH,E(_1gK)[2]));})];}else{return [0,_1gG,_1gH];}},_1gM=function(_1gN,_1gO,_1gP,_1gQ){var _1gR=E(_1gP);if(!_1gR[0]){var _1gS=new T(function(){var _1gT=B(_1gM(_1gR[1],_1gR[2],_1gR[3],_1gR[4]));return [0,_1gT[1],_1gT[2]];});return [0,new T(function(){return E(E(_1gS)[1]);}),new T(function(){return B(_1f6(_1gO,E(_1gS)[2],_1gQ));})];}else{return [0,_1gO,_1gQ];}},_1gU=function(_1gV,_1gW){var _1gX=E(_1gV);if(!_1gX[0]){var _1gY=_1gX[1],_1gZ=E(_1gW);if(!_1gZ[0]){var _1h0=_1gZ[1];if(_1gY<=_1h0){var _1h1=B(_1gM(_1h0,_1gZ[2],_1gZ[3],_1gZ[4]));return new F(function(){return _1eu(_1h1[1],_1gX,_1h1[2]);});}else{var _1h2=B(_1gE(_1gY,_1gX[2],_1gX[3],_1gX[4]));return new F(function(){return _1f6(_1h2[1],_1h2[2],_1gZ);});}}else{return E(_1gX);}}else{return E(_1gW);}},_1h3=function(_1h4,_1h5,_1h6,_1h7,_1h8){var _1h9=E(_1h4);if(!_1h9[0]){var _1ha=_1h9[1],_1hb=_1h9[2],_1hc=_1h9[3],_1hd=_1h9[4];if((imul(3,_1ha)|0)>=_1h5){if((imul(3,_1h5)|0)>=_1ha){return new F(function(){return _1gU(_1h9,[0,_1h5,E(_1h6),E(_1h7),E(_1h8)]);});}else{return new F(function(){return _1f6(_1hb,_1hc,B(_1h3(_1hd,_1h5,_1h6,_1h7,_1h8)));});}}else{return new F(function(){return _1eu(_1h6,B(_1he(_1ha,_1hb,_1hc,_1hd,_1h7)),_1h8);});}}else{return [0,_1h5,E(_1h6),E(_1h7),E(_1h8)];}},_1he=function(_1hf,_1hg,_1hh,_1hi,_1hj){var _1hk=E(_1hj);if(!_1hk[0]){var _1hl=_1hk[1],_1hm=_1hk[2],_1hn=_1hk[3],_1ho=_1hk[4];if((imul(3,_1hf)|0)>=_1hl){if((imul(3,_1hl)|0)>=_1hf){return new F(function(){return _1gU([0,_1hf,E(_1hg),E(_1hh),E(_1hi)],_1hk);});}else{return new F(function(){return _1f6(_1hg,_1hh,B(_1h3(_1hi,_1hl,_1hm,_1hn,_1ho)));});}}else{return new F(function(){return _1eu(_1hm,B(_1he(_1hf,_1hg,_1hh,_1hi,_1hn)),_1ho);});}}else{return [0,_1hf,E(_1hg),E(_1hh),E(_1hi)];}},_1hp=function(_1hq,_1hr){var _1hs=E(_1hq);if(!_1hs[0]){var _1ht=_1hs[1],_1hu=_1hs[2],_1hv=_1hs[3],_1hw=_1hs[4],_1hx=E(_1hr);if(!_1hx[0]){var _1hy=_1hx[1],_1hz=_1hx[2],_1hA=_1hx[3],_1hB=_1hx[4];if((imul(3,_1ht)|0)>=_1hy){if((imul(3,_1hy)|0)>=_1ht){return new F(function(){return _1gU(_1hs,_1hx);});}else{return new F(function(){return _1f6(_1hu,_1hv,B(_1h3(_1hw,_1hy,_1hz,_1hA,_1hB)));});}}else{return new F(function(){return _1eu(_1hz,B(_1he(_1ht,_1hu,_1hv,_1hw,_1hA)),_1hB);});}}else{return E(_1hs);}}else{return E(_1hr);}},_1hC=function(_1hD,_1hE){var _1hF=E(_1hE);if(!_1hF[0]){var _1hG=_1hF[2],_1hH=_1hF[3],_1hI=_1hF[4];if(!B(A(_1hD,[_1hG]))){return new F(function(){return _1hp(B(_1hC(_1hD,_1hH)),B(_1hC(_1hD,_1hI)));});}else{return new F(function(){return _1gq(_1hG,B(_1hC(_1hD,_1hH)),B(_1hC(_1hD,_1hI)));});}}else{return [1];}},_1hJ=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_1hK=new T(function(){return B(err(_1hJ));}),_1hL=function(_1hM,_1hN,_1hO,_1hP){while(1){var _1hQ=E(_1hO);if(!_1hQ[0]){_1hM=_1hQ[1];_1hN=_1hQ[2];_1hO=_1hQ[3];_1hP=_1hQ[4];continue;}else{return E(_1hN);}}},_1hR=function(_1hS,_1hT){var _1hU=B(_1hC(function(_1hV){return new F(function(){return _3x(E(_1hV)[2],_1hS);});},_1hT));if(!_1hU[0]){var _1hW=E(_1hU[3]);return _1hW[0]==0?B(_1hL(_1hW[1],_1hW[2],_1hW[3],_1hW[4])):E(_1hU[2]);}else{return E(_1hK);}},_1hX=[1,_9],_1hY=function(_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9,_1ia,_1ib,_1ic){var _1id=E(_1ic);if(!_1id[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_1i6,[_1ib]));}),_9]],_9],[1,[1,new T(function(){return B(A(_1i6,[_1ib]));}),_9]]]];}else{var _1ie=function(_1if){var _1ig=E(_1if);if(!_1ig[0]){return E(_1hX);}else{var _1ih=E(_1ig[1]),_1ii=B(_1hY(_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9,_1ia,_1ih[1],_1ih[2]));if(!_1ii[0]){return [0];}else{var _1ij=B(_1ie(_1ig[2]));return _1ij[0]==0?[0]:[1,[1,_1ii[1],_1ij[1]]];}}},_1ik=B(_1ie(_1id[2]));return _1ik[0]==0?[0]:B(A(_1dX,[_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9,new T(function(){return B(_1hR(_1id[1],_1ia));}),_1ik[1],_1ib]));}},_1il=function(_1im,_1in,_1io,_1ip,_1iq,_1ir,_1is,_1it,_1iu,_1iv,_1iw,_1ix,_1iy,_1iz,_1iA){var _1iB=E(_1iA);return new F(function(){return _1hY(_1im,_1in,_1io,_1ip,_1iq,_1ir,_1is,_1it,_1iu,_1ix,_1iy,_1iz,_1iB[1],_1iB[2]);});},_1iC=new T(function(){return B(unCStr("div"));}),_1iD=function(_1iE,_1iF,_1iG,_){var _1iH=jsCreateElem(toJSStr(E(_1iC))),_1iI=_1iH,_1iJ=jsAppendChild(_1iI,E(_1iG)[1]),_1iK=[0,_1iI],_1iL=B(A(_1iE,[_1iF,_1iK,_])),_1iM=_1iL;return _1iK;},_1iN=function(_1iO,_1iP){while(1){var _1iQ=E(_1iP);if(!_1iQ[0]){return true;}else{if(!B(A(_1iO,[_1iQ[1]]))){return false;}else{_1iP=_1iQ[2];continue;}}}},_1iR=[3],_1iS=function(_1iT){var _1iU=E(_1iT);switch(_1iU[0]){case 1:return [0,_1iU[1]];case 3:return [3];default:return E(_1iU);}},_1iV=function(_1iW,_1iX){return [0,_1iR,new T(function(){var _1iY=B(_16A(_1iX,0))-E(_1iW)[1]|0,_1iZ=new T(function(){return _1iY>=0?B(_1be(_1iY,_1iX)):E(_1iX);});if(_1iY>0){var _1j0=function(_1j1,_1j2){var _1j3=E(_1j1);if(!_1j3[0]){return E(_1iZ);}else{var _1j4=_1j3[1];return _1j2>1?[1,new T(function(){return B(_1iS(_1j4));}),new T(function(){return B(_1j0(_1j3[2],_1j2-1|0));})]:[1,new T(function(){return B(_1iS(_1j4));}),_1iZ];}},_1j5=B(_1j0(_1iX,_1iY));}else{var _1j5=E(_1iZ);}var _1j6=_1j5,_1j7=_1j6,_1j8=_1j7,_1j9=_1j8;return _1j9;})];},_1ja=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1jb=[2,_1ja],_1jc=new T(function(){return B(unCStr(" is closed, and can\'t be used"));}),_1jd=function(_1je){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_1je)[1],_9)),_1jc));}));});},_1jf=new T(function(){return B(unCStr(" has nothing on it"));}),_1jg=function(_1jh){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_1jh)[1],_9)),_1jf));}));});},_1ji=new T(function(){return B(unCStr(" depends on something not-well-formed, and can\'t be used"));}),_1jj=function(_1jk){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_1jk)[1],_9)),_1ji));}));});},_1jl=function(_1jm,_1jn,_1jo,_1jp,_1jq,_1jr,_1js){var _1jt=E(_1jm);if(_1jt[0]==1){var _1ju=E(_1jn);return _1ju[0]==1?[0,[1,[0,_1jo,[1,_1jr,[1,_1jt[1],[1,_1ju[1],_9]]]]],_1js]:[0,[2,new T(function(){switch(E(_1ju)[0]){case 0:var _1jv=B(_1jd(_1jq));break;case 2:var _1jv=B(_1jj(_1jq));break;default:var _1jv=B(_1jg(_1jq));}return _1jv;})],_1js];}else{var _1jw=E(_1jn);return _1jw[0]==1?[0,[2,new T(function(){switch(E(_1jt)[0]){case 0:var _1jx=B(_1jd(_1jp));break;case 2:var _1jx=B(_1jj(_1jp));break;default:var _1jx=B(_1jg(_1jp));}return _1jx;})],_1js]:[0,[2,new T(function(){var _1jy=new T(function(){return B(unAppCStr(" and ",new T(function(){switch(E(_1jw)[0]){case 0:var _1jz=B(_1jd(_1jq));break;case 2:var _1jz=B(_1jj(_1jq));break;default:var _1jz=B(_1jg(_1jq));}return _1jz;})));},1);switch(E(_1jt)[0]){case 0:var _1jA=B(_e(B(_1jd(_1jp)),_1jy));break;case 2:var _1jA=B(_e(B(_1jj(_1jp)),_1jy));break;default:var _1jA=B(_e(B(_1jg(_1jp)),_1jy));}return _1jA;})],_1js];}},_1jB=function(_1jC){return new F(function(){return _dq(_1jC,_9);});},_1jD=function(_1jE,_1jF){return _1jE<=B(_16A(_1jF,0))?[1,new T(function(){var _1jG=_1jE-1|0;if(_1jG>=0){var _1jH=B(_gE(B(_1jB(_1jF)),_1jG));}else{var _1jH=E(_gB);}var _1jI=_1jH,_1jJ=_1jI;return _1jJ;})]:[0];},_1jK=new T(function(){return B(unCStr(" is unavailable"));}),_1jL=new T(function(){return B(unCStr(" are unavailable"));}),_1jM=function(_1jN,_1jO,_1jP,_1jQ,_1jR,_1jS,_1jT){var _1jU=B(_1jV(_1jN,_1jO,[1,_1iR,_1jT])),_1jW=B(_1jD(_1jQ,_1jU));if(!_1jW[0]){return B(_1jD(_1jR,_1jU))[0]==0?B(_1jV(_1jN,_1jO,[1,[2,new T(function(){return B(unAppCStr("The lines ",new T(function(){return B(_e(B(_F(0,_1jQ,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_1jR,_9)),_1jL));})));},1)));})));})],_1jT])):B(_1jV(_1jN,_1jO,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_1jQ,_9)),_1jK));})));})],_1jT]));}else{var _1jX=B(_1jD(_1jR,_1jU));return _1jX[0]==0?B(_1jV(_1jN,_1jO,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_1jR,_9)),_1jK));})));})],_1jT])):B(_1jV(_1jN,_1jO,new T(function(){var _1jY=B(_1jl(_1jW[1],_1jX[1],_1jP,[0,_1jQ],[0,_1jR],_1jS,_1jT));return [1,_1jY[1],_1jY[2]];})));}},_1jZ=function(_1k0,_1k1,_1k2,_1k3,_1k4,_1k5,_1k6){return new F(function(){return _1jM(_1k0,_1k1,_1k2,E(_1k3)[1],E(_1k4)[1],_1k5,_1k6);});},_1k7=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1k8=[2,_1k7],_1k9=function(_1ka,_1kb,_1kc,_1kd,_1ke,_1kf){var _1kg=E(_1ke);if(!_1kg[0]){return new F(function(){return _1jV(_1ka,_1kb,[1,_1k8,_1kf]);});}else{var _1kh=E(_1kg[2]);return _1kh[0]==0?B(_1jV(_1ka,_1kb,[1,_1k8,_1kf])):E(_1kh[2])[0]==0?B(_1jZ(_1ka,_1kb,_1kc,_1kg[1],_1kh[1],_1kd,_1kf)):B(_1jV(_1ka,_1kb,[1,_1k8,_1kf]));}},_1ki=new T(function(){return B(unCStr("Open Subproof"));}),_1kj=[2,_1ki],_1kk=new T(function(){return B(unCStr("Impossible Error 2"));}),_1kl=[2,_1kk],_1km=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1kn=[2,_1km],_1ko=new T(function(){return B(unCStr("SHOW"));}),_1kp=function(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv){var _1kw=new T(function(){return B(_1jV(_1kq,_1kr,[1,_1iR,_1kv]));});if(_1kt<=B(_16A(_1kw,0))){var _1kx=_1kt-1|0;if(_1kx>=0){var _1ky=B(_gE(B(_1jB(_1kw)),_1kx));switch(_1ky[0]){case 0:return new F(function(){return _1jV(_1kq,_1kr,[1,[2,new T(function(){return B(_1jd([0,_1kt]));})],_1kv]);});break;case 1:return new F(function(){return _1jV(_1kq,_1kr,[1,[1,[0,_1ks,[1,_1ku,[1,_1ky[1],_9]]]],_1kv]);});break;case 2:return new F(function(){return _1jV(_1kq,_1kr,[1,[2,new T(function(){return B(_1jj([0,_1kt]));})],_1kv]);});break;default:return new F(function(){return _1jV(_1kq,_1kr,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_1kt,_9)),_1jf));})));})],_1kv]);});}}else{return E(_gB);}}else{return new F(function(){return _1jV(_1kq,_1kr,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_1kt,_9)),_1jK));})));})],_1kv]);});}},_1kz=function(_1kA,_1kB,_1kC,_1kD,_1kE,_1kF){return new F(function(){return _1kp(_1kA,_1kB,_1kC,E(_1kD)[1],_1kE,_1kF);});},_1kG=function(_1kH,_1kI,_1kJ,_1kK,_1kL,_1kM){var _1kN=E(_1kL);return _1kN[0]==0?B(_1jV(_1kH,_1kI,[1,_1k8,_1kM])):E(_1kN[2])[0]==0?B(_1kz(_1kH,_1kI,_1kJ,_1kN[1],_1kK,_1kM)):B(_1jV(_1kH,_1kI,[1,_1k8,_1kM]));},_1kO=function(_1kP,_1kQ,_1kR,_1kS,_1kT,_1kU){if(!B(_3x(_1kQ,_1ko))){var _1kV=B(A(_1kS,[_1kQ]));if(!_1kV[0]){return [0,_1jb,_1kU];}else{var _1kW=E(_1kV[1]);if(!_1kW[0]){return [0,_1kn,_1kU];}else{switch(E(E(_1kW[1])[1])){case 1:return new F(function(){return _1iV(new T(function(){return [0,B(_16A(_1kU,0))+1|0];},1),new T(function(){return B(_1kG(_1kT,_1kS,_1kP,_1kQ,_1kR,_1kU));}));});break;case 2:return new F(function(){return _1iV(new T(function(){return [0,B(_16A(_1kU,0))+1|0];},1),new T(function(){return B(_1k9(_1kT,_1kS,_1kP,_1kQ,_1kR,_1kU));}));});break;default:return [0,_1kl,_1kU];}}}}else{return new F(function(){return _1iV(new T(function(){return [0,B(_16A(_1kU,0))+1|0];},1),new T(function(){return B(_1jV(_1kT,_1kS,[1,_1kj,_1kU]));}));});}},_1kX=[0],_1kY=new T(function(){return B(unCStr("PR"));}),_1kZ=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1l0=[2,_1kZ],_1l1=new T(function(){return B(unCStr("Impossible Error 1"));}),_1l2=[2,_1l1],_1l3=function(_1l4,_1l5,_1l6,_1l7,_1l8){var _1l9=B(_1jD(_1l5,_1l8));if(!_1l9[0]){return B(_1jD(_1l6,_1l8))[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the lines ",new T(function(){return B(_e(B(_F(0,_1l5,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_1l6,_9)),_1jL));})));},1)));})));})],_1l8]:[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_1l5,_9)),_1jK));})));})],_1l8];}else{var _1la=B(_1jD(_1l6,_1l8));return _1la[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_1l6,_9)),_1jK));})));})],_1l8]:B(_1jl(_1l9[1],_1la[1],_1l4,[0,_1l5],[0,_1l6],_1l7,_1l8));}},_1lb=new T(function(){return B(unCStr("wrong number of premises"));}),_1lc=[2,_1lb],_1ld=function(_1le,_1lf,_1lg,_1lh){var _1li=E(_1lg);if(!_1li[0]){return [1,_1lc,_1lh];}else{var _1lj=E(_1li[2]);if(!_1lj[0]){return [1,_1lc,_1lh];}else{if(!E(_1lj[2])[0]){var _1lk=B(_1l3(_1le,E(_1li[1])[1],E(_1lj[1])[1],_1lf,_1lh));return [1,_1lk[1],_1lk[2]];}else{return [1,_1lc,_1lh];}}}},_1ll=new T(function(){return B(unCStr("has nothing on it"));}),_1lm=new T(function(){return B(unCStr("is unavailable"));}),_1ln=function(_1lo,_1lp,_1lq,_1lr){var _1ls=B(_1jD(_1lp,_1lr));if(!_1ls[0]){return [0,[2,new T(function(){return B(unAppCStr("line",new T(function(){return B(_e(B(_F(0,_1lp,_9)),_1lm));})));})],_1lr];}else{var _1lt=E(_1ls[1]);switch(_1lt[0]){case 0:return [0,[2,new T(function(){return B(_1jd([0,_1lp]));})],_1lr];case 1:return [0,[1,[0,_1lo,[1,_1lq,[1,_1lt[1],_9]]]],_1lr];case 2:return [0,[2,new T(function(){return B(_1jj([0,_1lp]));})],_1lr];default:return [0,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_1lp,_9)),_1ll));})));})],_1lr];}}},_1lu=function(_1lv,_1lw,_1lx,_1ly){var _1lz=B(_1ln(_1lv,E(_1lw)[1],_1lx,_1ly));return [1,_1lz[1],_1lz[2]];},_1lA=function(_1lB,_1lC,_1lD,_1lE){var _1lF=E(_1lD);return _1lF[0]==0?[1,_1lc,_1lE]:E(_1lF[2])[0]==0?B(_1lu(_1lB,_1lF[1],_1lC,_1lE)):[1,_1lc,_1lE];},_1lG=function(_1lH,_1lI,_1lJ,_1lK,_1lL){var _1lM=function(_1lN){var _1lO=B(A(_1lK,[_1lI]));if(!_1lO[0]){return [1,_1jb,_1lL];}else{var _1lP=E(_1lO[1]);if(!_1lP[0]){switch(E(E(_1lP[1])[1])){case 1:return new F(function(){return _1lA(_1lH,_1lI,_1lJ,_1lL);});break;case 2:return new F(function(){return _1ld(_1lH,_1lI,_1lJ,_1lL);});break;default:return [1,_1l2,_1lL];}}else{return [1,_1l0,_1lL];}}};return !B(_3x(_1lI,_1kY))?B(_1lM(_)):E(_1lJ)[0]==0?[1,[1,[0,_1lH,_1kX]],_1lL]:B(_1lM(_));},_1lQ=function(_1lR,_1lS,_1lT){var _1lU=E(_1lR);return new F(function(){return _1lG(_1lU[1],_1lU[2],_1lU[3],_1lS,_1lT);});},_1lV=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1lW=[2,_1lV],_1lX=new T(function(){return B(unCStr("incomplete line"));}),_1lY=[2,_1lX],_1lZ=function(_1m0,_1m1,_1m2,_1m3){var _1m4=E(_1m0);if(!_1m4[0]){return E(_1m1)[0]==0?[1,_1lY,_1m3]:[1,_1lW,_1m3];}else{var _1m5=_1m4[1],_1m6=E(_1m1);if(!_1m6[0]){return new F(function(){return _1lQ(_1m5,_1m2,_1m3);});}else{var _1m7=E(_1m5),_1m8=B(_1kO(_1m7[1],_1m7[2],_1m7[3],_1m2,_1m6,_1m3));return [1,_1m8[1],_1m8[2]];}}},_1m9=function(_1ma,_1mb,_1mc){var _1md=E(_1ma);return new F(function(){return _1lZ(_1md[1],_1md[2],_1mb,_1mc);});},_1jV=function(_1me,_1mf,_1mg){return new F(function(){return (function(_1mh,_1mi){while(1){var _1mj=(function(_1mk,_1ml){var _1mm=E(_1ml);if(!_1mm[0]){return E(_1mk);}else{_1mh=new T(function(){return B(_1m9(_1mm[1],_1mf,_1mk));});_1mi=_1mm[2];return null;}})(_1mh,_1mi);if(_1mj!=null){return _1mj;}}})(_1mg,_1me);});},_1mn=[0,666],_1mo=[0,_,_1mn],_1mp=[1,_1mo],_1mq=[0,_1mp,_1kX],_1mr=function(_1ms){return E(_1ms)[0]==2?false:true;},_1mt=function(_1mu,_1mv){var _1mw=B(_1jV(_1mu,_1mv,_9));return !B(_1iN(_1mr,_1mw))?[0,_1mw]:[1,new T(function(){var _1mx=B(_16A(_1mu,0))-1|0;if(_1mx>=0){var _1my=B(_gE(B(_1jB(_1mw)),_1mx)),_1mz=_1my[0]==1?E(_1my[1]):E(_1mq);}else{var _1mz=E(_gB);}var _1mA=_1mz,_1mB=_1mA,_1mC=_1mB;return _1mC;})];},_1mD=function(_1mE,_1mF){return new F(function(){return _F(0,E(_1mE)[1],_1mF);});},_1mG=function(_1mH){return function(_ma,_19D){return new F(function(){return _6v(new T(function(){return B(_23(_1mD,_1mH,_9));}),_ma,_19D);});};},_1mI=function(_1mJ){return function(_ma,_19D){return new F(function(){return _6v(new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1mJ,_V4));}),_ma,_19D);});};},_1mK=new T(function(){return B(unCStr("open"));}),_1mL=new T(function(){return B(unCStr("termination"));}),_1mM=new T(function(){return B(unCStr("closed"));}),_1mN=function(_1mO,_){return _1mO;},_1mP=function(_1mQ){var _1mR=E(_1mQ);return _1mR[0]==0?E(_1mN):function(_1mS,_){var _1mT=B(A(new T(function(){var _1mU=E(_1mR[1]);return B(_1mV(_1mU[1],_1mU[2]));}),[_1mS,_])),_1mW=_1mT,_1mX=B(A(new T(function(){return B(_1mP(_1mR[2]));}),[_1mS,_])),_1mY=_1mX;return _1mS;};},_1mZ=function(_1n0){var _1n1=E(_1n0);return _1n1[0]==0?E(_1mN):function(_1n2,_){var _1n3=B(A(new T(function(){var _1n4=E(_1n1[1]);return B(_1mV(_1n4[1],_1n4[2]));}),[_1n2,_])),_1n5=_1n3,_1n6=B(A(new T(function(){return B(_1mZ(_1n1[2]));}),[_1n2,_])),_1n7=_1n6;return _1n2;};},_1n8=new T(function(){return B(unCStr("SHOW"));}),_1mV=function(_1n9,_1na){var _1nb=E(_1n9);if(!_1nb[0]){return function(_ma,_19D){return new F(function(){return _1iD(_6v,_1nb[1],_ma,_19D);});};}else{var _1nc=E(_1nb[1]),_1nd=_1nc[1],_1ne=_1nc[2],_1nf=_1nc[3];if(!B(_3x(_1ne,_1n8))){var _1ng=E(_1na);return _1ng[0]==0?function(_ma,_19D){return new F(function(){return _1iD(_7s,function(_1nh,_){var _1ni=B(_7i(_1mI,_1nd,_1nh,_)),_1nj=_1ni,_1nk=B(_7i(_7s,function(_1nl,_){var _1nm=B(_7i(_6v,_1ne,_1nl,_)),_1nn=_1nm,_1no=B(_7i(_1mG,_1nf,_1nl,_)),_1np=_1no;return _1nl;},_1nh,_)),_1nq=_1nk;return _1nh;},_ma,_19D);});}:function(_ma,_19D){return new F(function(){return _1iD(_7s,function(_1nr,_){var _1ns=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1nd,_V4));})));}),_1nr,_)),_1nt=_1ns,_1nu=B(_1iD(_7s,function(_1nv,_){var _1nw=B(_7i(_7s,new T(function(){return B(_1mZ(_1ng));}),_1nv,_)),_1nx=_1nw,_1ny=B(_1iD(_7s,function(_1nz,_){var _1nA=B(_7i(_6v,_9,_1nz,_)),_1nB=_1nA,_1nC=B(A(_6C,[_6P,_1nB,_cn,_1mL,_])),_1nD=_1nC,_1nE=B(_7i(_7s,function(_1nF,_){var _1nG=B(_7i(_6v,_1ne,_1nF,_)),_1nH=_1nG,_1nI=B(_7i(_1mG,_1nf,_1nF,_)),_1nJ=_1nI;return _1nF;},_1nz,_)),_1nK=_1nE;return _1nz;},_1nv,_)),_1nL=_1ny;return _1nv;},_1nr,_)),_1nM=_1nu,_1nN=B(A(_6C,[_6P,_1nM,_cn,_1mM,_])),_1nO=_1nN;return _1nr;},_ma,_19D);});};}else{var _1nP=E(_1na);return _1nP[0]==0?function(_ma,_19D){return new F(function(){return _1iD(_7s,function(_c9,_){return new F(function(){return _7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1nd,_V4));})));}),_c9,_);});},_ma,_19D);});}:function(_ma,_19D){return new F(function(){return _1iD(_7s,function(_1nQ,_){var _1nR=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UQ(_Q,_u,_Q,_N,_Q,_UG,_1nd,_V4));})));}),_1nQ,_)),_1nS=_1nR,_1nT=B(_1iD(_7s,function(_c9,_){return new F(function(){return _7i(_7s,new T(function(){return B(_1mP(_1nP));}),_c9,_);});},_1nQ,_)),_1nU=_1nT,_1nV=B(A(_6C,[_6P,_1nU,_cn,_1mK,_])),_1nW=_1nV;return _1nQ;},_ma,_19D);});};}}},_1nX=function(_1nY){var _1nZ=E(_1nY);return _1nZ[0]==0?E(_1mN):function(_1o0,_){var _1o1=B(A(new T(function(){var _1o2=E(_1nZ[1]);return B(_1mV(_1o2[1],_1o2[2]));}),[_1o0,_])),_1o3=_1o1,_1o4=B(A(new T(function(){return B(_1nX(_1nZ[2]));}),[_1o0,_])),_1o5=_1o4;return _1o0;};},_1o6=function(_c9,_){return new F(function(){return _1iD(_6v,_9,_c9,_);});},_1o7=new T(function(){return B(unCStr("errormsg"));}),_1o8=[0,10006],_1o9=[1,_1o8,_9],_1oa=new T(function(){return B(_2L("Carnap/Frontend/Components/ProofPadEmbedding.hs:(79,27)-(83,84)|case"));}),_1ob=function(_1oc){var _1od=E(_1oc);switch(_1od[0]){case 2:return function(_ma,_19D){return new F(function(){return _1iD(_7s,function(_1oe,_){var _1of=B(_7i(_6v,_1o9,_1oe,_)),_1og=_1of,_1oh=B(_7i(_6v,_1od[1],_1oe,_)),_1oi=_1oh,_1oj=B(A(_6C,[_6P,_1oi,_cn,_1o7,_])),_1ok=_1oj;return _1oe;},_ma,_19D);});};case 3:return E(_1oa);default:return E(_1o6);}},_1ol=function(_1om){var _1on=E(_1om);return _1on[0]==0?E(_1mN):function(_1oo,_){var _1op=B(A(new T(function(){return B(_1ob(_1on[1]));}),[_1oo,_])),_1oq=_1op,_1or=B(A(new T(function(){return B(_1ol(_1on[2]));}),[_1oo,_])),_1os=_1or;return _1oo;};},_1ot=[0,10],_1ou=[1,_1ot,_9],_1ov=function(_1ow,_1ox,_){var _1oy=jsCreateElem(toJSStr(E(_1ow))),_1oz=_1oy,_1oA=jsAppendChild(_1oz,E(_1ox)[1]);return [0,_1oz];},_1oB=function(_1oC,_1oD,_1oE,_){var _1oF=B(_1ov(_1oC,_1oE,_)),_1oG=_1oF,_1oH=B(A(_1oD,[_1oG,_])),_1oI=_1oH;return _1oG;},_1oJ=new T(function(){return B(unCStr("()"));}),_1oK=new T(function(){return B(unCStr("GHC.Tuple"));}),_1oL=new T(function(){return B(unCStr("ghc-prim"));}),_1oM=new T(function(){var _1oN=hs_wordToWord64(2170319554),_1oO=_1oN,_1oP=hs_wordToWord64(26914641),_1oQ=_1oP;return [0,_1oO,_1oQ,[0,_1oO,_1oQ,_1oL,_1oK,_1oJ],_9];}),_1oR=function(_1oS){return E(_1oM);},_1oT=new T(function(){return B(unCStr("PerchM"));}),_1oU=new T(function(){return B(unCStr("Haste.Perch"));}),_1oV=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1oW=new T(function(){var _1oX=hs_wordToWord64(3005229400),_1oY=_1oX,_1oZ=hs_wordToWord64(2682402736),_1p0=_1oZ;return [0,_1oY,_1p0,[0,_1oY,_1p0,_1oV,_1oU,_1oT],_9];}),_1p1=function(_1p2){return E(_1oW);},_1p3=function(_1p4){var _1p5=E(_1p4);if(!_1p5[0]){return [0];}else{var _1p6=E(_1p5[1]);return [1,[0,_1p6[1],_1p6[2]],new T(function(){return B(_1p3(_1p5[2]));})];}},_1p7=function(_1p8,_1p9){var _1pa=E(_1p8);if(!_1pa){return [0,_9,_1p9];}else{var _1pb=E(_1p9);if(!_1pb[0]){return [0,_9,_9];}else{var _1pc=new T(function(){var _1pd=B(_1p7(_1pa-1|0,_1pb[2]));return [0,_1pd[1],_1pd[2]];});return [0,[1,_1pb[1],new T(function(){return E(E(_1pc)[1]);})],new T(function(){return E(E(_1pc)[2]);})];}}},_1pe=[0,120],_1pf=[0,48],_1pg=function(_1ph){var _1pi=new T(function(){var _1pj=B(_1p7(8,new T(function(){var _1pk=md5(toJSStr(E(_1ph))),_1pl=_1pk;return fromJSStr(_1pl);})));return [0,_1pj[1],_1pj[2]];}),_1pm=parseInt([0,toJSStr([1,_1pf,[1,_1pe,new T(function(){return E(E(_1pi)[1]);})]])]),_1pn=_1pm,_1po=new T(function(){var _1pp=B(_1p7(8,new T(function(){return E(E(_1pi)[2]);})));return [0,_1pp[1],_1pp[2]];}),_1pq=parseInt([0,toJSStr([1,_1pf,[1,_1pe,new T(function(){return E(E(_1po)[1]);})]])]),_1pr=_1pq,_1ps=hs_mkWord64(_1pn,_1pr),_1pt=_1ps,_1pu=parseInt([0,toJSStr([1,_1pf,[1,_1pe,new T(function(){return E(B(_1p7(8,new T(function(){return E(E(_1po)[2]);})))[1]);})]])]),_1pv=_1pu,_1pw=hs_mkWord64(_1pv,_1pv),_1px=_1pw;return [0,_1pt,_1px];},_1py=function(_1pz,_1pA){var _1pB=jsShowI(_1pz),_1pC=_1pB,_1pD=md5(_1pC),_1pE=_1pD;return new F(function(){return _e(fromJSStr(_1pE),new T(function(){var _1pF=jsShowI(_1pA),_1pG=_1pF,_1pH=md5(_1pG),_1pI=_1pH;return fromJSStr(_1pI);},1));});},_1pJ=function(_1pK){var _1pL=E(_1pK);return new F(function(){return _1py(_1pL[1],_1pL[2]);});},_1pM=function(_1pN,_1pO){return function(_1pP){return E(new T(function(){var _1pQ=B(A(_1pN,[_])),_1pR=E(_1pQ[3]),_1pS=_1pR[1],_1pT=_1pR[2],_1pU=B(_e(_1pQ[4],[1,new T(function(){return B(A(_1pO,[_]));}),_9]));if(!_1pU[0]){var _1pV=[0,_1pS,_1pT,_1pR,_9];}else{var _1pW=B(_1pg(new T(function(){return B(_8Q(B(_3d(_1pJ,[1,[0,_1pS,_1pT],new T(function(){return B(_1p3(_1pU));})]))));},1))),_1pV=[0,_1pW[1],_1pW[2],_1pR,_1pU];}var _1pX=_1pV,_1pY=_1pX;return _1pY;}));};},_1pZ=new T(function(){return B(_1pM(_1p1,_1oR));}),_1q0=function(_1q1,_1q2,_1q3,_){var _1q4=E(_1q2),_1q5=B(A(_1q1,[_1q3,_])),_1q6=_1q5,_1q7=B(A(_6C,[_6P,_1q6,_1q4[1],_1q4[2],_])),_1q8=_1q7;return _1q6;},_1q9=function(_1qa,_1qb){while(1){var _1qc=(function(_1qd,_1qe){var _1qf=E(_1qe);if(!_1qf[0]){return E(_1qd);}else{_1qa=function(_1qg,_){return new F(function(){return _1q0(_1qd,_1qf[1],_1qg,_);});};_1qb=_1qf[2];return null;}})(_1qa,_1qb);if(_1qc!=null){return _1qc;}}},_1qh=new T(function(){return B(unCStr("value"));}),_1qi=new T(function(){return B(unCStr("id"));}),_1qj=new T(function(){return B(unCStr("onclick"));}),_1qk=new T(function(){return B(unCStr("checked"));}),_1ql=[0,_1qk,_9],_1qm=[1,_1ql,_9],_1qn=new T(function(){return B(unCStr("type"));}),_1qo=new T(function(){return B(unCStr("input"));}),_1qp=function(_1qq,_){return new F(function(){return _1ov(_1qo,_1qq,_);});},_1qr=function(_1qs,_1qt,_1qu,_1qv,_1qw){var _1qx=new T(function(){var _1qy=new T(function(){return B(_1q9(_1qp,[1,[0,_1qn,_1qt],[1,[0,_1qi,_1qs],[1,[0,_1qh,_1qu],_9]]]));});return !E(_1qv)?E(_1qy):B(_1q9(_1qy,_1qm));}),_1qz=E(_1qw);return _1qz[0]==0?E(_1qx):B(_1q9(_1qx,[1,[0,_1qj,_1qz[1]],_9]));},_1qA=new T(function(){return B(unCStr("href"));}),_1qB=[0,97],_1qC=[1,_1qB,_9],_1qD=function(_1qE,_){return new F(function(){return _1ov(_1qC,_1qE,_);});},_1qF=function(_1qG,_1qH){return function(_1qI,_){var _1qJ=B(A(new T(function(){return B(_1q9(_1qD,[1,[0,_1qA,_1qG],_9]));}),[_1qI,_])),_1qK=_1qJ,_1qL=B(A(_1qH,[_1qK,_])),_1qM=_1qL;return _1qK;};},_1qN=function(_1qO){return new F(function(){return _1qF(_1qO,function(_1qg,_){return new F(function(){return _6v(_1qO,_1qg,_);});});});},_1qP=new T(function(){return B(unCStr("option"));}),_1qQ=function(_1qR,_){return new F(function(){return _1ov(_1qP,_1qR,_);});},_1qS=new T(function(){return B(unCStr("selected"));}),_1qT=[0,_1qS,_9],_1qU=[1,_1qT,_9],_1qV=function(_1qW,_1qX,_1qY){var _1qZ=new T(function(){return B(_1q9(_1qQ,[1,[0,_1qh,_1qW],_9]));});if(!E(_1qY)){return function(_1r0,_){var _1r1=B(A(_1qZ,[_1r0,_])),_1r2=_1r1,_1r3=B(A(_1qX,[_1r2,_])),_1r4=_1r3;return _1r2;};}else{return new F(function(){return _1q9(function(_1r5,_){var _1r6=B(A(_1qZ,[_1r5,_])),_1r7=_1r6,_1r8=B(A(_1qX,[_1r7,_])),_1r9=_1r8;return _1r7;},_1qU);});}},_1ra=function(_1rb,_1rc){return new F(function(){return _1qV(_1rb,function(_1qg,_){return new F(function(){return _6v(_1rb,_1qg,_);});},_1rc);});},_1rd=new T(function(){return B(unCStr("method"));}),_1re=new T(function(){return B(unCStr("action"));}),_1rf=new T(function(){return B(unCStr("UTF-8"));}),_1rg=new T(function(){return B(unCStr("acceptCharset"));}),_1rh=[0,_1rg,_1rf],_1ri=new T(function(){return B(unCStr("form"));}),_1rj=function(_1rk,_){return new F(function(){return _1ov(_1ri,_1rk,_);});},_1rl=function(_1rm,_1rn,_1ro){return function(_1rp,_){var _1rq=B(A(new T(function(){return B(_1q9(_1rj,[1,_1rh,[1,[0,_1re,_1rm],[1,[0,_1rd,_1rn],_9]]]));}),[_1rp,_])),_1rr=_1rq,_1rs=B(A(_1ro,[_1rr,_])),_1rt=_1rs;return _1rr;};},_1ru=new T(function(){return B(unCStr("select"));}),_1rv=function(_1rw,_){return new F(function(){return _1ov(_1ru,_1rw,_);});},_1rx=function(_1ry,_1rz){return function(_1rA,_){var _1rB=B(A(new T(function(){return B(_1q9(_1rv,[1,[0,_1qi,_1ry],_9]));}),[_1rA,_])),_1rC=_1rB,_1rD=B(A(_1rz,[_1rC,_])),_1rE=_1rD;return _1rC;};},_1rF=new T(function(){return B(unCStr("textarea"));}),_1rG=function(_1rH,_){return new F(function(){return _1ov(_1rF,_1rH,_);});},_1rI=function(_1rJ,_1rK){return function(_1rL,_){var _1rM=B(A(new T(function(){return B(_1q9(_1rG,[1,[0,_1qi,_1rJ],_9]));}),[_1rL,_])),_1rN=_1rM,_1rO=B(_6v(_1rK,_1rN,_)),_1rP=_1rO;return _1rN;};},_1rQ=new T(function(){return B(unCStr("color:red"));}),_1rR=new T(function(){return B(unCStr("style"));}),_1rS=[0,_1rR,_1rQ],_1rT=[1,_1rS,_9],_1rU=[0,98],_1rV=[1,_1rU,_9],_1rW=function(_1rX){return new F(function(){return _1q9(function(_1rY,_){var _1rZ=B(_1ov(_1rV,_1rY,_)),_1s0=_1rZ,_1s1=B(A(_1rX,[_1s0,_])),_1s2=_1s1;return _1s0;},_1rT);});},_1s3=function(_1s4,_1s5,_){var _1s6=E(_1s4);if(!_1s6[0]){return _1s5;}else{var _1s7=B(A(_1s6[1],[_1s5,_])),_1s8=_1s7,_1s9=B(_1s3(_1s6[2],_1s5,_)),_1sa=_1s9;return _1s5;}},_1sb=function(_1sc,_1sd,_){return new F(function(){return _1s3(_1sc,_1sd,_);});},_1se=function(_1sf,_1sg,_1sh,_){var _1si=B(A(_1sf,[_1sh,_])),_1sj=_1si,_1sk=B(A(_1sg,[_1sh,_])),_1sl=_1sk;return _1sh;},_1sm=[0,_6S,_1se,_1sb],_1sn=[0,_1sm,_1pZ,_6v,_6v,_1oB,_1rW,_1qF,_1qN,_1qr,_1rI,_1rx,_1qV,_1ra,_1rl,_1q9],_1so=function(_1sp,_1sq,_){var _1sr=B(A(_1sq,[_])),_1ss=_1sr;return _1sp;},_1st=function(_1su,_1sv,_){var _1sw=B(A(_1sv,[_])),_1sx=_1sw;return new T(function(){return B(A(_1su,[_1sx]));});},_1sy=[0,_1st,_1so],_1sz=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1sA=new T(function(){return B(unCStr("base"));}),_1sB=new T(function(){return B(unCStr("IOException"));}),_1sC=new T(function(){var _1sD=hs_wordToWord64(4053623282),_1sE=_1sD,_1sF=hs_wordToWord64(3693590983),_1sG=_1sF;return [0,_1sE,_1sG,[0,_1sE,_1sG,_1sA,_1sz,_1sB],_9];}),_1sH=function(_1sI){return E(_1sC);},_1sJ=function(_1sK){var _1sL=E(_1sK);return new F(function(){return _1I(B(_1G(_1sL[1])),_1sH,_1sL[2]);});},_1sM=new T(function(){return B(unCStr(": "));}),_1sN=[0,41],_1sO=new T(function(){return B(unCStr(" ("));}),_1sP=new T(function(){return B(unCStr("already exists"));}),_1sQ=new T(function(){return B(unCStr("does not exist"));}),_1sR=new T(function(){return B(unCStr("protocol error"));}),_1sS=new T(function(){return B(unCStr("failed"));}),_1sT=new T(function(){return B(unCStr("invalid argument"));}),_1sU=new T(function(){return B(unCStr("inappropriate type"));}),_1sV=new T(function(){return B(unCStr("hardware fault"));}),_1sW=new T(function(){return B(unCStr("unsupported operation"));}),_1sX=new T(function(){return B(unCStr("timeout"));}),_1sY=new T(function(){return B(unCStr("resource vanished"));}),_1sZ=new T(function(){return B(unCStr("interrupted"));}),_1t0=new T(function(){return B(unCStr("resource busy"));}),_1t1=new T(function(){return B(unCStr("resource exhausted"));}),_1t2=new T(function(){return B(unCStr("end of file"));}),_1t3=new T(function(){return B(unCStr("illegal operation"));}),_1t4=new T(function(){return B(unCStr("permission denied"));}),_1t5=new T(function(){return B(unCStr("user error"));}),_1t6=new T(function(){return B(unCStr("unsatisified constraints"));}),_1t7=new T(function(){return B(unCStr("system error"));}),_1t8=function(_1t9,_1ta){switch(E(_1t9)){case 0:return new F(function(){return _e(_1sP,_1ta);});break;case 1:return new F(function(){return _e(_1sQ,_1ta);});break;case 2:return new F(function(){return _e(_1t0,_1ta);});break;case 3:return new F(function(){return _e(_1t1,_1ta);});break;case 4:return new F(function(){return _e(_1t2,_1ta);});break;case 5:return new F(function(){return _e(_1t3,_1ta);});break;case 6:return new F(function(){return _e(_1t4,_1ta);});break;case 7:return new F(function(){return _e(_1t5,_1ta);});break;case 8:return new F(function(){return _e(_1t6,_1ta);});break;case 9:return new F(function(){return _e(_1t7,_1ta);});break;case 10:return new F(function(){return _e(_1sR,_1ta);});break;case 11:return new F(function(){return _e(_1sS,_1ta);});break;case 12:return new F(function(){return _e(_1sT,_1ta);});break;case 13:return new F(function(){return _e(_1sU,_1ta);});break;case 14:return new F(function(){return _e(_1sV,_1ta);});break;case 15:return new F(function(){return _e(_1sW,_1ta);});break;case 16:return new F(function(){return _e(_1sX,_1ta);});break;case 17:return new F(function(){return _e(_1sY,_1ta);});break;default:return new F(function(){return _e(_1sZ,_1ta);});}},_1tb=[0,125],_1tc=new T(function(){return B(unCStr("{handle: "));}),_1td=function(_1te,_1tf,_1tg,_1th,_1ti,_1tj){var _1tk=new T(function(){var _1tl=new T(function(){return B(_1t8(_1tf,new T(function(){var _1tm=E(_1th);return _1tm[0]==0?E(_1tj):B(_e(_1sO,new T(function(){return B(_e(_1tm,[1,_1sN,_1tj]));},1)));},1)));},1),_1tn=E(_1tg);return _1tn[0]==0?E(_1tl):B(_e(_1tn,new T(function(){return B(_e(_1sM,_1tl));},1)));},1),_1to=E(_1ti);if(!_1to[0]){var _1tp=E(_1te);if(!_1tp[0]){return E(_1tk);}else{var _1tq=E(_1tp[1]);return _1tq[0]==0?B(_e(_1tc,new T(function(){return B(_e(_1tq[1],[1,_1tb,new T(function(){return B(_e(_1sM,_1tk));})]));},1))):B(_e(_1tc,new T(function(){return B(_e(_1tq[1],[1,_1tb,new T(function(){return B(_e(_1sM,_1tk));})]));},1)));}}else{return new F(function(){return _e(_1to[1],new T(function(){return B(_e(_1sM,_1tk));},1));});}},_1tr=function(_1ts){var _1tt=E(_1ts);return new F(function(){return _1td(_1tt[1],_1tt[2],_1tt[3],_1tt[4],_1tt[6],_9);});},_1tu=function(_1tv,_1tw){var _1tx=E(_1tv);return new F(function(){return _1td(_1tx[1],_1tx[2],_1tx[3],_1tx[4],_1tx[6],_1tw);});},_1ty=function(_1tz,_1tA){return new F(function(){return _23(_1tu,_1tz,_1tA);});},_1tB=function(_1tC,_1tD,_1tE){var _1tF=E(_1tD);return new F(function(){return _1td(_1tF[1],_1tF[2],_1tF[3],_1tF[4],_1tF[6],_1tE);});},_1tG=[0,_1tB,_1tr,_1ty],_1tH=new T(function(){return [0,_1sH,_1tG,_1tI,_1sJ];}),_1tI=function(_1tJ){return [0,_1tH,_1tJ];},_1tK=7,_1tL=function(_1tM){return [0,_4O,_1tK,_9,_1tM,_4O,_4O];},_1tN=function(_1tO,_){return new F(function(){return die(new T(function(){return B(_1tI(new T(function(){return B(_1tL(_1tO));})));}));});},_1tP=function(_1tQ,_){return new F(function(){return _1tN(_1tQ,_);});},_1tR=function(_1tS,_){return new F(function(){return _1tP(_1tS,_);});},_1tT=function(_1tU,_){return new F(function(){return _1tR(_1tU,_);});},_1tV=function(_1tW,_1tX,_){var _1tY=B(A(_1tW,[_])),_1tZ=_1tY;return new F(function(){return A(_1tX,[_1tZ,_]);});},_1u0=function(_1u1,_1u2,_){var _1u3=B(A(_1u1,[_])),_1u4=_1u3;return new F(function(){return A(_1u2,[_]);});},_1u5=[0,_1tV,_1u0,_6S,_1tT],_1u6=[0,_1u5,_6P],_1u7=function(_1u8){return E(E(_1u8)[1]);},_1u9=function(_1ua){return E(E(_1ua)[2]);},_1ub=function(_1uc,_1ud){var _1ue=new T(function(){return B(_1u7(_1uc));});return function(_1uf){return new F(function(){return A(new T(function(){return B(_NO(_1ue));}),[new T(function(){return B(A(_1u9,[_1uc,_1ud]));}),function(_1ug){return new F(function(){return A(new T(function(){return B(_iZ(_1ue));}),[[0,_1ug,_1uf]]);});}]);});};},_1uh=function(_1ui,_1uj){return [0,_1ui,function(_1uk){return new F(function(){return _1ub(_1uj,_1uk);});}];},_1ul=function(_1um,_1un,_1uo,_1up){return new F(function(){return A(_NO,[_1um,new T(function(){return B(A(_1un,[_1up]));}),function(_1uq){return new F(function(){return A(_1uo,[new T(function(){return E(E(_1uq)[1]);}),new T(function(){return E(E(_1uq)[2]);})]);});}]);});},_1ur=function(_1us,_1ut,_1uu,_1uv){return new F(function(){return A(_NO,[_1us,new T(function(){return B(A(_1ut,[_1uv]));}),function(_1uw){return new F(function(){return A(_1uu,[new T(function(){return E(E(_1uw)[2]);})]);});}]);});},_1ux=function(_1uy,_1uz,_1uA,_1uB){return new F(function(){return _1ur(_1uy,_1uz,_1uA,_1uB);});},_1uC=function(_1uD){return E(E(_1uD)[4]);},_1uE=function(_1uF,_1uG){return function(_1uH){return E(new T(function(){return B(A(_1uC,[_1uF,_1uG]));}));};},_1uI=function(_1uJ){return [0,function(_1uz,_1uA,_1uB){return new F(function(){return _1ul(_1uJ,_1uz,_1uA,_1uB);});},function(_1uz,_1uA,_1uB){return new F(function(){return _1ux(_1uJ,_1uz,_1uA,_1uB);});},function(_1uK,_1uL){return new F(function(){return A(new T(function(){return B(_iZ(_1uJ));}),[[0,_1uK,_1uL]]);});},function(_1uB){return new F(function(){return _1uE(_1uJ,_1uB);});}];},_1uM=function(_1uN,_1uO,_1uP){return new F(function(){return A(_iZ,[_1uN,[0,_1uO,_1uP]]);});},_1uQ=[0,10],_1uR=function(_1uS,_1uT){var _1uU=E(_1uT);if(!_1uU[0]){return E(_6P);}else{var _1uV=_1uU[1],_1uW=E(_1uU[2]);if(!_1uW[0]){var _1uX=E(_1uV);return new F(function(){return _1uY(_1uQ,_1uX[3],_1uX[4]);});}else{return function(_1uZ){return new F(function(){return A(new T(function(){var _1v0=E(_1uV);return B(_1uY(_1uQ,_1v0[3],_1v0[4]));}),[new T(function(){return B(A(_1uS,[new T(function(){return B(A(new T(function(){return B(_1uR(_1uS,_1uW));}),[_1uZ]));})]));})]);});};}}},_1v1=new T(function(){return B(unCStr("(->)"));}),_1v2=new T(function(){return B(unCStr("GHC.Prim"));}),_1v3=new T(function(){var _1v4=hs_wordToWord64(4173248105),_1v5=_1v4,_1v6=hs_wordToWord64(4270398258),_1v7=_1v6;return [0,_1v5,_1v7,[0,_1v5,_1v7,_1oL,_1v2,_1v1],_9];}),_1v8=new T(function(){return E(E(_1v3)[3]);}),_1v9=new T(function(){return B(unCStr("GHC.Types"));}),_1va=new T(function(){return B(unCStr("[]"));}),_1vb=new T(function(){var _1vc=hs_wordToWord64(4033920485),_1vd=_1vc,_1ve=hs_wordToWord64(786266835),_1vf=_1ve;return [0,_1vd,_1vf,[0,_1vd,_1vf,_1oL,_1v9,_1va],_9];}),_1vg=[1,_1oM,_9],_1vh=function(_1vi){var _1vj=E(_1vi);if(!_1vj[0]){return [0];}else{var _1vk=E(_1vj[1]);return [1,[0,_1vk[1],_1vk[2]],new T(function(){return B(_1vh(_1vj[2]));})];}},_1vl=new T(function(){var _1vm=E(_1vb),_1vn=E(_1vm[3]),_1vo=B(_e(_1vm[4],_1vg));if(!_1vo[0]){var _1vp=E(_1vn);}else{var _1vq=B(_1pg(new T(function(){return B(_8Q(B(_3d(_1pJ,[1,[0,_1vn[1],_1vn[2]],new T(function(){return B(_1vh(_1vo));})]))));},1))),_1vp=E(_1vn);}var _1vr=_1vp,_1vs=_1vr;return _1vs;}),_1vt=[0,8],_1vu=[0,32],_1vv=function(_1vw){return [1,_1vu,_1vw];},_1vx=new T(function(){return B(unCStr(" -> "));}),_1vy=[0,9],_1vz=[0,93],_1vA=[0,91],_1vB=[0,41],_1vC=[0,44],_1vD=function(_1vw){return [1,_1vC,_1vw];},_1vE=[0,40],_1vF=[0,0],_1uY=function(_1vG,_1vH,_1vI){var _1vJ=E(_1vI);if(!_1vJ[0]){return function(_1vK){return new F(function(){return _e(E(_1vH)[5],_1vK);});};}else{var _1vL=_1vJ[1],_1vM=function(_1vN){var _1vO=E(_1vH)[5],_1vP=function(_1vQ){var _1vR=new T(function(){return B(_1uR(_1vv,_1vJ));});return E(_1vG)[1]<=9?function(_1vS){return new F(function(){return _e(_1vO,[1,_1vu,new T(function(){return B(A(_1vR,[_1vS]));})]);});}:function(_1vT){return [1,_E,new T(function(){return B(_e(_1vO,[1,_1vu,new T(function(){return B(A(_1vR,[[1,_D,_1vT]]));})]));})];};},_1vU=E(_1vO);if(!_1vU[0]){return new F(function(){return _1vP(_);});}else{if(E(E(_1vU[1])[1])==40){var _1vV=E(_1vU[2]);if(!_1vV[0]){return new F(function(){return _1vP(_);});}else{if(E(E(_1vV[1])[1])==44){return function(_1vW){return [1,_1vE,new T(function(){return B(A(new T(function(){return B(_1uR(_1vD,_1vJ));}),[[1,_1vB,_1vW]]));})];};}else{return new F(function(){return _1vP(_);});}}}else{return new F(function(){return _1vP(_);});}}},_1vX=E(_1vJ[2]);if(!_1vX[0]){var _1vY=E(_1vH),_1vZ=E(_1vl),_1w0=hs_eqWord64(_1vY[1],_1vZ[1]),_1w1=_1w0;if(!E(_1w1)){return new F(function(){return _1vM(_);});}else{var _1w2=hs_eqWord64(_1vY[2],_1vZ[2]),_1w3=_1w2;if(!E(_1w3)){return new F(function(){return _1vM(_);});}else{return function(_1w4){return [1,_1vA,new T(function(){return B(A(new T(function(){var _1w5=E(_1vL);return B(_1uY(_1vF,_1w5[3],_1w5[4]));}),[[1,_1vz,_1w4]]));})];};}}}else{if(!E(_1vX[2])[0]){var _1w6=E(_1vH),_1w7=E(_1v8),_1w8=hs_eqWord64(_1w6[1],_1w7[1]),_1w9=_1w8;if(!E(_1w9)){return new F(function(){return _1vM(_);});}else{var _1wa=hs_eqWord64(_1w6[2],_1w7[2]),_1wb=_1wa;if(!E(_1wb)){return new F(function(){return _1vM(_);});}else{var _1wc=new T(function(){var _1wd=E(_1vX[1]);return B(_1uY(_1vt,_1wd[3],_1wd[4]));}),_1we=new T(function(){var _1wf=E(_1vL);return B(_1uY(_1vy,_1wf[3],_1wf[4]));});return E(_1vG)[1]<=8?function(_1wg){return new F(function(){return A(_1we,[new T(function(){return B(_e(_1vx,new T(function(){return B(A(_1wc,[_1wg]));},1)));})]);});}:function(_1wh){return [1,_E,new T(function(){return B(A(_1we,[new T(function(){return B(_e(_1vx,new T(function(){return B(A(_1wc,[[1,_D,_1wh]]));},1)));})]));})];};}}}else{return new F(function(){return _1vM(_);});}}}},_1wi=function(_1wj,_1wk){return new F(function(){return A(_1wj,[function(_){return new F(function(){return jsFind(toJSStr(E(_1wk)));});}]);});},_1wl=[0],_1wm=function(_1wn){return E(E(_1wn)[3]);},_1wo=new T(function(){return [0,"value"];}),_1wp=function(_1wq){return E(E(_1wq)[6]);},_1wr=function(_1ws){return E(E(_1ws)[1]);},_1wt=new T(function(){return B(unCStr("Char"));}),_1wu=new T(function(){var _1wv=hs_wordToWord64(3763641161),_1ww=_1wv,_1wx=hs_wordToWord64(1343745632),_1wy=_1wx;return [0,_1ww,_1wy,[0,_1ww,_1wy,_1oL,_1v9,_1wt],_9];}),_1wz=function(_1wA){return E(_1wu);},_1wB=function(_1wC){return E(_1vb);},_1wD=new T(function(){return B(_1pM(_1wB,_1wz));}),_1wE=new T(function(){return B(A(_1wD,[_]));}),_1wF=function(_1wG,_1wH,_1wI,_1wJ,_1wK,_1wL,_1wM,_1wN,_1wO){var _1wP=new T(function(){return B(A(_1wJ,[_1wl]));});return new F(function(){return A(_1wH,[new T(function(){return B(_1wi(E(_1wG)[2],_1wO));}),function(_1wQ){var _1wR=E(_1wQ);return _1wR[0]==0?E(_1wP):B(A(_1wH,[new T(function(){return B(A(E(_1wG)[2],[function(_){var _1wS=jsGet(E(_1wR[1])[1],E(_1wo)[1]),_1wT=_1wS;return [1,new T(function(){return fromJSStr(_1wT);})];}]));}),function(_1wU){var _1wV=E(_1wU);if(!_1wV[0]){return E(_1wP);}else{var _1wW=_1wV[1];if(!E(new T(function(){var _1wX=B(A(_1wL,[_])),_1wY=E(_1wE),_1wZ=hs_eqWord64(_1wX[1],_1wY[1]),_1x0=_1wZ;if(!E(_1x0)){var _1x1=false;}else{var _1x2=hs_eqWord64(_1wX[2],_1wY[2]),_1x3=_1x2,_1x1=E(_1x3)==0?false:true;}var _1x4=_1x1,_1x5=_1x4;return _1x5;}))){var _1x6=function(_1x7){return new F(function(){return A(_1wJ,[[1,_1wW,new T(function(){return B(A(new T(function(){return B(_1wp(_1wN));}),[new T(function(){return B(A(new T(function(){return B(_1wm(_1wN));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1wW,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1x8=B(A(_1wL,[_]));return B(A(_1uY,[_1vF,_1x8[3],_1x8[4],_9]));})));})));})));})]));})]));})]]);});},_1x9=B(A(new T(function(){return B(A(_1wr,[_1wM,_4x]));}),[_1wW]));if(!_1x9[0]){return new F(function(){return _1x6(_);});}else{var _1xa=E(_1x9[1]);return E(_1xa[2])[0]==0?E(_1x9[2])[0]==0?B(A(_1wJ,[[2,_1xa[1]]])):B(_1x6(_)):B(_1x6(_));}}else{return new F(function(){return A(_1wJ,[[2,_1wW]]);});}}}]));}]);});},_1xb=function(_1xc){return E(E(_1xc)[10]);},_1xd=function(_1xe){return new F(function(){return _l1([1,function(_1xf){return new F(function(){return A(_sC,[_1xf,function(_1xg){return E(new T(function(){return B(_tS(function(_1xh){var _1xi=E(_1xh);return _1xi[0]==0?B(A(_1xe,[_1xi[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_ue(_1xj,_1xe))];}));});},_1xj=function(_1xk,_1xl){return new F(function(){return _1xd(_1xl);});},_1xm=[0,91],_1xn=[1,_1xm,_9],_1xo=function(_1xp,_1xq){var _1xr=function(_1xs,_1xt){return [1,function(_1xu){return new F(function(){return A(_sC,[_1xu,function(_1xv){return E(new T(function(){return B(_tS(function(_1xw){var _1xx=E(_1xw);if(_1xx[0]==2){var _1xy=E(_1xx[1]);if(!_1xy[0]){return [2];}else{var _1xz=_1xy[2];switch(E(E(_1xy[1])[1])){case 44:return E(_1xz)[0]==0?!E(_1xs)?[2]:E(new T(function(){return B(A(_1xp,[_ud,function(_1xA){return new F(function(){return _1xr(_o9,function(_1xB){return new F(function(){return A(_1xt,[[1,_1xA,_1xB]]);});});});}]));})):[2];case 93:return E(_1xz)[0]==0?E(new T(function(){return B(A(_1xt,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1xC=function(_1xD){return new F(function(){return _l1([1,function(_1xE){return new F(function(){return A(_sC,[_1xE,function(_1xF){return E(new T(function(){return B(_tS(function(_1xG){var _1xH=E(_1xG);return _1xH[0]==2?!B(_3x(_1xH[1],_1xn))?[2]:E(new T(function(){return B(_l1(B(_1xr(_4y,_1xD)),new T(function(){return B(A(_1xp,[_ud,function(_1xI){return new F(function(){return _1xr(_o9,function(_1xJ){return new F(function(){return A(_1xD,[[1,_1xI,_1xJ]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_ue(function(_1xK,_1xL){return new F(function(){return _1xC(_1xL);});},_1xD))];}));});};return new F(function(){return _1xC(_1xq);});},_1xM=function(_1xN){return new F(function(){return _l1(B(_l1([1,function(_1xO){return new F(function(){return A(_sC,[_1xO,function(_1xP){return E(new T(function(){return B(_tS(function(_1xQ){var _1xR=E(_1xQ);return _1xR[0]==1?B(A(_1xN,[_1xR[1]])):[2];}));}));}]);});}],new T(function(){return B(_1xo(_1xj,_1xN));}))),new T(function(){return [1,B(_ue(_1xS,_1xN))];}));});},_1xS=function(_1xT,_1xU){return new F(function(){return _1xM(_1xU);});},_1xV=new T(function(){return B(_1xM(_lK));}),_1xW=function(_1xX){return new F(function(){return _kR(_1xV,_1xX);});},_1xY=new T(function(){return B(_1xd(_lK));}),_1xZ=function(_1xX){return new F(function(){return _kR(_1xY,_1xX);});},_1y0=function(_1y1){return E(_1xZ);},_1y2=[0,_1y0,_1xW,_1xj,_1xS],_1y3=function(_1y4){return E(E(_1y4)[4]);},_1y5=function(_1y6,_1y7,_1y8){return new F(function(){return _1xo(new T(function(){return B(_1y3(_1y6));}),_1y8);});},_1y9=function(_1ya){return function(_ma){return new F(function(){return _kR(new T(function(){return B(_1xo(new T(function(){return B(_1y3(_1ya));}),_lK));}),_ma);});};},_1yb=function(_1yc,_1yd){return function(_ma){return new F(function(){return _kR(new T(function(){return B(A(_1y3,[_1yc,_1yd,_lK]));}),_ma);});};},_1ye=function(_1yf){return [0,function(_1xX){return new F(function(){return _1yb(_1yf,_1xX);});},new T(function(){return B(_1y9(_1yf));}),new T(function(){return B(_1y3(_1yf));}),function(_1yg,_1xX){return new F(function(){return _1y5(_1yf,_1yg,_1xX);});}];},_1yh=new T(function(){return B(_1ye(_1y2));}),_1yi=function(_1yj,_1yk,_1yl){var _1ym=new T(function(){return B(_1xb(_1yj));}),_1yn=new T(function(){return B(_1u7(_1yl));}),_1yo=new T(function(){return B(_iZ(_1yn));});return function(_1yp,_1yq){return new F(function(){return A(new T(function(){return B(_NO(_1yn));}),[new T(function(){return B(A(new T(function(){return B(_NO(_1yn));}),[new T(function(){return B(A(new T(function(){return B(_iZ(_1yn));}),[[0,_1yq,_1yq]]));}),function(_1yr){var _1ys=new T(function(){return E(E(_1yr)[1]);}),_1yt=new T(function(){return E(E(_1ys)[2]);});return new F(function(){return A(new T(function(){return B(_NO(_1yn));}),[new T(function(){return B(A(new T(function(){return B(_iZ(_1yn));}),[[0,_6B,new T(function(){var _1yu=E(_1ys);return [0,_1yu[1],new T(function(){return [0,E(_1yt)[1]+1|0];}),_1yu[3],_1yu[4],_1yu[5],_1yu[6],_1yu[7]];})]]));}),function(_1yv){return new F(function(){return A(new T(function(){return B(_iZ(_1yn));}),[[0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_1yt)[1],_9)),new T(function(){return E(E(_1ys)[1]);},1)));})],new T(function(){return E(E(_1yv)[2]);})]]);});}]);});}]));}),function(_1yw){var _1yx=new T(function(){return E(E(_1yw)[1]);});return new F(function(){return A(new T(function(){return B(_NO(_1yn));}),[new T(function(){return B(A(_1wF,[new T(function(){return B(_1uh(new T(function(){return B(_1uI(_1yn));}),_1yl));}),function(_1yy,_1qg,_1yz){return new F(function(){return _1ul(_1yn,_1yy,_1qg,_1yz);});},function(_1yy,_1qg,_1yz){return new F(function(){return _1ux(_1yn,_1yy,_1qg,_1yz);});},function(_1qg,_1yz){return new F(function(){return _1uM(_1yn,_1qg,_1yz);});},function(_1yz){return new F(function(){return _1uE(_1yn,_1yz);});},_1wD,_1yh,_1yj,_1yx,new T(function(){return E(E(_1yw)[2]);})]));}),function(_1yA){var _1yB=E(_1yA),_1yC=_1yB[2],_1yD=E(_1yB[1]);switch(_1yD[0]){case 0:return new F(function(){return A(_1yo,[[0,[0,new T(function(){return B(A(_1ym,[_1yx,_1yp]));}),_4O],_1yC]]);});break;case 1:return new F(function(){return A(_1yo,[[0,[0,new T(function(){return B(A(_1ym,[_1yx,_1yD[1]]));}),_4O],_1yC]]);});break;default:var _1yE=_1yD[1];return new F(function(){return A(_1yo,[[0,[0,new T(function(){return B(A(_1ym,[_1yx,_1yE]));}),[1,_1yE]],_1yC]]);});}}]);});}]);});};},_1yF=new T(function(){return B(_1yi(_1sn,_1sy,_1u6));}),_1yG=new T(function(){return B(_Ci("w_s8nn{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv a7wT} [tv]"));}),_1yH=new T(function(){return B(_Ci("w_s8no{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv a7wS} [tv]"));}),_1yI=function(_1yJ){return E(E(_1yJ)[2]);},_1yK=function(_1yL){return E(E(_1yL)[1]);},_1yM=function(_1yN,_1yO,_1yP){return function(_1yQ,_){var _1yR=B(A(_1yO,[_1yQ,_])),_1yS=_1yR,_1yT=E(_1yS),_1yU=E(_1yT[1]),_1yV=new T(function(){return B(A(new T(function(){return B(_1yI(_1yN));}),[_1yP,function(_){var _1yW=E(E(_1yQ)[4]),_1yX=B(A(_1yW[1],[_])),_1yY=_1yX,_1yZ=E(_1yY);if(!_1yZ[0]){return _6B;}else{var _1z0=B(A(_1yW[2],[_1yZ[1],_])),_1z1=_1z0;return _6B;}}]));});return [0,[0,function(_1z2,_){var _1z3=B(A(_1yU[1],[_1z2,_])),_1z4=_1z3,_1z5=E(_1z4),_1z6=E(_1yV),_1z7=jsSetCB(_1z5[1],toJSStr(E(new T(function(){return B(A(_1yK,[_1yN,_1yP]));}))),_1yV),_1z8=_1z7;return _1z5;},_1yU[2]],_1yT[2]];};},_1z9=function(_1za,_1zb,_1zc,_1zd,_1ze,_1zf,_1zg,_1zh,_1zi,_1zj,_1zk){return function(_1zl,_1zm){return function(_ma,_19D){return new F(function(){return _7u(function(_1zn,_){var _1zo=B(A(new T(function(){return B(_1yM(_6u,new T(function(){return B(_1yM(_6u,new T(function(){return B(A(_1yF,[_1zm]));}),_1p));}),_1o));}),[_1zn,_])),_1zp=_1zo,_1zq=E(_1zp),_1zr=E(_1zq[1]);return [0,[0,function(_1zs,_){var _1zt=B(A(_1zr[1],[_1zs,_])),_1zu=_1zt,_1zv=B(A(_6C,[_6P,_1zu,_cn,_cu,_])),_1zw=_1zv;return _1zu;},_1zr[2]],_1zq[2]];},function(_1zx){var _1zy=new T(function(){var _1zz=B(_Dq(_Cm,_DM,[0,new T(function(){return B(_e(_1zx,_1ou));}),E(_Cf),E(_6B)]));if(!_1zz[0]){var _1zA=E(_1zz[1]);if(!_1zA[0]){var _1zB=E(E(_1zA[1])[1]);}else{var _1zB=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1zA[1]));})));})],_9],_9];}var _1zC=_1zB;}else{var _1zD=E(_1zz[1]);if(!_1zD[0]){var _1zE=E(E(_1zD[1])[1]);}else{var _1zE=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1zD[1]));})));})],_9],_9];}var _1zC=_1zE;}return _1zC;});return function(_ma,_19D){return new F(function(){return _7u(_c8,function(_1zF,_1zG,_){return new F(function(){return _7u(_ce,function(_1zH,_1zI,_){return new F(function(){return _7u(_cj,function(_1zJ,_1zK,_){return new F(function(){return _7u(function(_1zL,_){return [0,[0,function(_1zM,_){var _1zN=B(_1iD(_6v,_9,_1zM,_)),_1zO=_1zN,_1zP=B(A(_6C,[_6P,_1zO,_6O,_1zF,_])),_1zQ=_1zP,_1zR=B(A(_6C,[_6P,_1zO,_cn,_ck,_])),_1zS=_1zR;return _1zO;},_cq],_1zL];},function(_1zT,_1zU,_){return new F(function(){return _7u(function(_1zV,_){return [0,[0,function(_1zW,_){var _1zX=B(_7i(_7s,new T(function(){return B(_1nX(_1zy));}),_1zW,_)),_1zY=_1zX,_1zZ=B(A(_6C,[_6P,_1zY,_6O,_1zH,_])),_1A0=_1zZ,_1A1=B(A(_6C,[_6P,_1zY,_cn,_cl,_])),_1A2=_1A1;return _1zY;},_cq],_1zV];},function(_1A3){return E(new T(function(){var _1A4=E(new T(function(){var _1A5=B(_1mt(_1zy,new T(function(){return E(E(_1zl)[1]);})));return _1A5[0]==0?[0,_1A5[1]]:[1,new T(function(){return B(_1il(_1za,_1zb,_1zc,_1zd,_1ze,_1zf,_1zg,_1zh,_1zi,_1yG,_1yH,_1zj,_1zk,new T(function(){return E(E(_1zl)[2]);}),_1A5[1]));})];}));if(!_1A4[0]){var _1A6=function(_1A7,_){return [0,[0,function(_1A8,_){var _1A9=B(_1iD(_7s,new T(function(){return B(_1ol(B(_dq(_1A4[1],_9))));}),_1A8,_)),_1Aa=_1A9,_1Ab=B(A(_6C,[_6P,_1Aa,_6O,_1zJ,_])),_1Ac=_1Ab,_1Ad=B(A(_6C,[_6P,_1Aa,_cn,_cm,_])),_1Ae=_1Ad;return _1Aa;},_cq],_1A7];};}else{var _1Af=E(_1A4[1]);if(!_1Af[0]){var _1Ag=function(_c9,_){return new F(function(){return _cw(_1zF,_c1,_cs,_c9,_);});};}else{var _1Ag=function(_ma,_19D){return new F(function(){return _cw(_1zF,_c1,function(_1Ah,_){return [0,[0,function(_c9,_){return new F(function(){return _7i(_6v,new T(function(){var _1Ai=E(_1Af[1]);return B(_bV(new T(function(){return B(_bI(_1zg,_1zf,_1ze,_1zd,_1zc,_1za,_1zb));}),new T(function(){return B(_3W(_1zg,_1zf,_1ze,_1zd,_1zc,_1za,_1zb));}),_1Ai[1],_1Ai[2]));}),_c9,_);});},_cq],_1Ah];},_ma,_19D);});};}var _1A6=_1Ag;}return _1A6;}));},_1zU,_);});},_1zK,_);});},_1zI,_);});},_1zG,_);});},_ma,_19D);});};},_ma,_19D);});};};},_1Aj=function(_1Ak,_1Al,_1Am,_1An){return new F(function(){return A(_1Ak,[function(_){var _1Ao=jsSet(E(_1Al)[1],toJSStr(E(_1Am)),toJSStr(E(_1An)));return _6B;}]);});},_1Ap=new T(function(){return B(unCStr("innerHTML"));}),_1Aq=new T(function(){return B(unCStr("textContent"));}),_1Ar=function(_1As,_1At,_1Au,_1Av,_1Aw,_1Ax,_1Ay,_1Az,_1AA,_1AB,_1AC,_1AD,_1AE,_){var _1AF=B(_1j(_1AE,_1Aq,_)),_1AG=_1AF,_1AH=[0,_1AE],_1AI=B(A(_1Aj,[_6P,_1AH,_1Ap,_9,_])),_1AJ=_1AI,_1AK=E(_51)[1],_1AL=takeMVar(_1AK),_1AM=_1AL,_1AN=B(A(_1z9,[_1As,_1At,_1Au,_1Av,_1Aw,_1Ax,_1Ay,_1Az,_1AA,_1AB,_1AC,_1AD,_1AG,_1AM,_])),_1AO=_1AN,_1AP=E(_1AO),_1AQ=E(_1AP[1]),_=putMVar(_1AK,_1AP[2]),_1AR=B(A(_1AQ[1],[_1AH,_])),_1AS=_1AR;return _1AQ[2];},_1AT=function(_){var _1AU=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1AV=_1AU;return _6B;},_1AW=new T(function(){return B(unCStr("embedding complete"));}),_1AX=new T(function(){return B(unCStr("proofbox"));}),_1AY=function(_1AZ,_1B0,_1B1,_1B2,_1B3,_1B4,_1B5,_1B6,_1B7,_1B8,_1B9,_1Ba,_){var _1Bb=jsElemsByClassName(toJSStr(E(_1AX))),_1Bc=_1Bb,_1Bd=B((function(_1Be,_){while(1){var _1Bf=E(_1Be);if(!_1Bf[0]){return _6B;}else{var _1Bg=B(_1Ar(_1AZ,_1B0,_1B1,_1B2,_1B3,_1B4,_1B5,_1B6,_1B7,_1B8,_1B9,_1Ba,E(_1Bf[1])[1],_)),_1Bh=_1Bg;_1Be=_1Bf[2];continue;}}})(_1Bc,_)),_1Bi=_1Bd,_1Bj=jsLog(toJSStr(E(_1AW))),_1Bk=jsSetTimeout(60,_1AT);return _6B;},_1Bl=new T(function(){return B(unCStr("ADD"));}),_1Bm=new T(function(){return B(unCStr("ADJ"));}),_1Bn=[0,1],_1Bo=[1,_1Bn],_1Bp=[1,_1Bo],_1Bq=[0,_1Bn],_1Br=[1,_1Bq],_1Bs=new T(function(){return B(unCStr("DN"));}),_1Bt=new T(function(){return B(_3x(_9,_1Bs));}),_1Bu=new T(function(){return B(unCStr("MTP"));}),_1Bv=new T(function(){return B(unCStr("MP"));}),_1Bw=new T(function(){return B(unCStr("ID"));}),_1Bx=new T(function(){return B(unCStr("CD"));}),_1By=[0,2],_1Bz=[1,_1By],_1BA=[1,_1Bz],_1BB=[0,_1By],_1BC=[1,_1BB],_1BD=function(_1BE){if(!B(_3x(_1BE,_1Bl))){if(!B(_3x(_1BE,_1Bm))){if(!B(_3x(_1BE,_1Bx))){if(!B(_3x(_1BE,_1Bw))){if(!B(_3x(_1BE,_1Bv))){if(!B(_3x(_1BE,_1Bu))){var _1BF=E(_1BE);return _1BF[0]==0?!E(_1Bt)?[0]:E(_1Br):E(E(_1BF[1])[1])==83?E(_1BF[2])[0]==0?E(_1Br):!B(_3x(_1BF,_1Bs))?[0]:E(_1Br):!B(_3x(_1BF,_1Bs))?[0]:E(_1Br);}else{return E(_1BC);}}else{return E(_1BC);}}else{return E(_1BA);}}else{return E(_1Bp);}}else{return E(_1BC);}}else{return E(_1Br);}},_1BG=function(_1BH){return E(E(_1BH)[2]);},_1BI=function(_1BJ,_1BK,_1BL){while(1){var _1BM=E(_1BK);if(!_1BM[0]){return E(_1BL)[0]==0?1:0;}else{var _1BN=E(_1BL);if(!_1BN[0]){return 2;}else{var _1BO=B(A(_1BG,[_1BJ,_1BM[1],_1BN[1]]));if(_1BO==1){_1BK=_1BM[2];_1BL=_1BN[2];continue;}else{return E(_1BO);}}}}},_1BP=function(_1BQ){return E(E(_1BQ)[3]);},_1BR=function(_1BS,_1BT,_1BU,_1BV,_1BW){switch(B(_1BI(_1BS,_1BT,_1BV))){case 0:return true;case 1:return new F(function(){return A(_1BP,[_1BS,_1BU,_1BW]);});break;default:return false;}},_1BX=function(_1BY,_1BZ,_1C0,_1C1){var _1C2=E(_1C0),_1C3=E(_1C1);return new F(function(){return _1BR(_1BZ,_1C2[1],_1C2[2],_1C3[1],_1C3[2]);});},_1C4=function(_1C5){return E(E(_1C5)[6]);},_1C6=function(_1C7,_1C8,_1C9,_1Ca,_1Cb){switch(B(_1BI(_1C7,_1C8,_1Ca))){case 0:return true;case 1:return new F(function(){return A(_1C4,[_1C7,_1C9,_1Cb]);});break;default:return false;}},_1Cc=function(_1Cd,_1Ce,_1Cf,_1Cg){var _1Ch=E(_1Cf),_1Ci=E(_1Cg);return new F(function(){return _1C6(_1Ce,_1Ch[1],_1Ch[2],_1Ci[1],_1Ci[2]);});},_1Cj=function(_1Ck){return E(E(_1Ck)[5]);},_1Cl=function(_1Cm,_1Cn,_1Co,_1Cp,_1Cq){switch(B(_1BI(_1Cm,_1Cn,_1Cp))){case 0:return false;case 1:return new F(function(){return A(_1Cj,[_1Cm,_1Co,_1Cq]);});break;default:return true;}},_1Cr=function(_1Cs,_1Ct,_1Cu,_1Cv){var _1Cw=E(_1Cu),_1Cx=E(_1Cv);return new F(function(){return _1Cl(_1Ct,_1Cw[1],_1Cw[2],_1Cx[1],_1Cx[2]);});},_1Cy=function(_1Cz){return E(E(_1Cz)[4]);},_1CA=function(_1CB,_1CC,_1CD,_1CE,_1CF){switch(B(_1BI(_1CB,_1CC,_1CE))){case 0:return false;case 1:return new F(function(){return A(_1Cy,[_1CB,_1CD,_1CF]);});break;default:return true;}},_1CG=function(_1CH,_1CI,_1CJ,_1CK){var _1CL=E(_1CJ),_1CM=E(_1CK);return new F(function(){return _1CA(_1CI,_1CL[1],_1CL[2],_1CM[1],_1CM[2]);});},_1CN=function(_1CO,_1CP,_1CQ,_1CR,_1CS){switch(B(_1BI(_1CO,_1CP,_1CR))){case 0:return 0;case 1:return new F(function(){return A(_1BG,[_1CO,_1CQ,_1CS]);});break;default:return 2;}},_1CT=function(_1CU,_1CV,_1CW,_1CX){var _1CY=E(_1CW),_1CZ=E(_1CX);return new F(function(){return _1CN(_1CV,_1CY[1],_1CY[2],_1CZ[1],_1CZ[2]);});},_1D0=function(_1D1,_1D2,_1D3,_1D4){var _1D5=E(_1D3),_1D6=_1D5[1],_1D7=_1D5[2],_1D8=E(_1D4),_1D9=_1D8[1],_1Da=_1D8[2];switch(B(_1BI(_1D2,_1D6,_1D9))){case 0:return [0,_1D9,_1Da];case 1:return !B(A(_1C4,[_1D2,_1D7,_1Da]))?[0,_1D6,_1D7]:[0,_1D9,_1Da];default:return [0,_1D6,_1D7];}},_1Db=function(_1Dc,_1Dd,_1De,_1Df){var _1Dg=E(_1De),_1Dh=_1Dg[1],_1Di=_1Dg[2],_1Dj=E(_1Df),_1Dk=_1Dj[1],_1Dl=_1Dj[2];switch(B(_1BI(_1Dd,_1Dh,_1Dk))){case 0:return [0,_1Dh,_1Di];case 1:return !B(A(_1C4,[_1Dd,_1Di,_1Dl]))?[0,_1Dk,_1Dl]:[0,_1Dh,_1Di];default:return [0,_1Dk,_1Dl];}},_1Dm=function(_1Dn,_1Do){return [0,_1Dn,function(_ZT,_ZU){return new F(function(){return _1CT(_1Dn,_1Do,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1BX(_1Dn,_1Do,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1CG(_1Dn,_1Do,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Cr(_1Dn,_1Do,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Cc(_1Dn,_1Do,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1D0(_1Dn,_1Do,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Db(_1Dn,_1Do,_ZT,_ZU);});}];},_1Dp=function(_1Dq,_1Dr,_1Ds,_1Dt){return !B(A(_1Dq,[_1Ds,_1Dt]))?B(_d3(B(A(_1Dr,[_1Ds,_16H])),B(A(_1Dr,[_1Dt,_16H]))))==2?false:true:false;},_1Du=function(_1Dv,_1Dw,_1Dx,_1Dy){return new F(function(){return _1Dp(E(_1Dv)[1],_1Dw,_1Dx,_1Dy);});},_1Dz=function(_1DA,_1DB,_1DC,_1DD){return B(_d3(B(A(_1DB,[_1DC,_16H])),B(A(_1DB,[_1DD,_16H]))))==2?false:true;},_1DE=function(_1DF,_1DG,_1DH,_1DI){return !B(A(_1DF,[_1DH,_1DI]))?B(_d3(B(A(_1DG,[_1DH,_16H])),B(A(_1DG,[_1DI,_16H]))))==2?true:false:false;},_1DJ=function(_1DK,_1DL,_1DM,_1DN){return new F(function(){return _1DE(E(_1DK)[1],_1DL,_1DM,_1DN);});},_1DO=function(_1DP,_1DQ,_1DR,_1DS){return !B(A(_1DP,[_1DR,_1DS]))?B(_d3(B(A(_1DQ,[_1DR,_16H])),B(A(_1DQ,[_1DS,_16H]))))==2?true:false:true;},_1DT=function(_1DU,_1DV,_1DW,_1DX){return new F(function(){return _1DO(E(_1DU)[1],_1DV,_1DW,_1DX);});},_1DY=function(_1DZ,_1E0,_1E1,_1E2){return !B(A(_1DZ,[_1E1,_1E2]))?B(_d3(B(A(_1E0,[_1E1,_16H])),B(A(_1E0,[_1E2,_16H]))))==2?2:0:1;},_1E3=function(_1E4,_1E5,_1E6,_1E7){return new F(function(){return _1DY(E(_1E4)[1],_1E5,_1E6,_1E7);});},_1E8=function(_1E9,_1Ea,_1Eb,_1Ec){return B(_d3(B(A(_1Ea,[_1Eb,_16H])),B(A(_1Ea,[_1Ec,_16H]))))==2?E(_1Eb):E(_1Ec);},_1Ed=function(_1Ee,_1Ef,_1Eg,_1Eh){return B(_d3(B(A(_1Ef,[_1Eg,_16H])),B(A(_1Ef,[_1Eh,_16H]))))==2?E(_1Eh):E(_1Eg);},_1Ei=function(_1Ej,_1Ek){return [0,_1Ej,function(_44,_45){return new F(function(){return _1E3(_1Ej,_1Ek,_44,_45);});},function(_44,_45){return new F(function(){return _1Du(_1Ej,_1Ek,_44,_45);});},function(_44,_45){return new F(function(){return _1DT(_1Ej,_1Ek,_44,_45);});},function(_44,_45){return new F(function(){return _1DJ(_1Ej,_1Ek,_44,_45);});},function(_44,_45){return new F(function(){return _1Dz(_1Ej,_1Ek,_44,_45);});},function(_44,_45){return new F(function(){return _1E8(_1Ej,_1Ek,_44,_45);});},function(_44,_45){return new F(function(){return _1Ed(_1Ej,_1Ek,_44,_45);});}];},_1El=function(_1Em,_1En,_1Eo,_1Ep,_1Eq,_1Er,_1Es){var _1Et=function(_1Eu,_1Ev){return new F(function(){return _2W(_1Em,_1En,_1Eo,_1Eq,_1Ep,_1Es,_1Er,_1Eu);});};return function(_1Ew,_1Ex){var _1Ey=E(_1Ew);if(!_1Ey[0]){var _1Ez=E(_1Ex);return _1Ez[0]==0?B(_d3(B(_1r(_1Ey[1])),B(_1r(_1Ez[1]))))==2?false:true:true;}else{var _1EA=E(_1Ex);return _1EA[0]==0?false:B(_1BI(new T(function(){return B(_1Ei(new T(function(){return B(_16M(_1Et));}),_1Et));}),_1Ey[1],_1EA[1]))==2?false:true;}};},_1EB=function(_1EC,_1ED,_1EE,_1EF,_1EG,_1EH,_1EI,_1EJ,_1EK,_1EL){return !B(A(_1El,[_1ED,_1EE,_1EF,_1EG,_1EH,_1EI,_1EJ,_1EK,_1EL]))?E(_1EK):E(_1EL);},_1EM=function(_1EN,_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU,_1EV,_1EW){return !B(A(_1El,[_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU,_1EV,_1EW]))?E(_1EW):E(_1EV);},_1EX=function(_1EY,_1EZ,_1F0,_1F1,_1F2,_1F3,_1F4){var _1F5=function(_1F6,_1F7){return new F(function(){return _2W(_1EY,_1EZ,_1F0,_1F2,_1F1,_1F4,_1F3,_1F6);});};return function(_1F8,_1F9){var _1Fa=E(_1F8);if(!_1Fa[0]){var _1Fb=_1Fa[1],_1Fc=E(_1F9);if(!_1Fc[0]){var _1Fd=_1Fc[1];return B(_109(_1Fb,_1Fd,_1))[0]==0?B(_d3(B(_1r(_1Fb)),B(_1r(_1Fd))))==2?false:true:false;}else{return true;}}else{var _1Fe=E(_1F9);return _1Fe[0]==0?false:B(_1BI(new T(function(){return B(_1Ei(new T(function(){return B(_16M(_1F5));}),_1F5));}),_1Fa[1],_1Fe[1]))==0?true:false;}};},_1Ff=function(_1Fg,_1Fh,_1Fi,_1Fj,_1Fk,_1Fl,_1Fm){var _1Fn=function(_1Fo,_1Fp){return new F(function(){return _2W(_1Fg,_1Fh,_1Fi,_1Fk,_1Fj,_1Fm,_1Fl,_1Fo);});};return function(_1Fq,_1Fr){var _1Fs=E(_1Fq);if(!_1Fs[0]){var _1Ft=_1Fs[1],_1Fu=E(_1Fr);if(!_1Fu[0]){var _1Fv=_1Fu[1];return B(_109(_1Ft,_1Fv,_1))[0]==0?B(_d3(B(_1r(_1Ft)),B(_1r(_1Fv))))==2?true:false:false;}else{return false;}}else{var _1Fw=E(_1Fr);return _1Fw[0]==0?true:B(_1BI(new T(function(){return B(_1Ei(new T(function(){return B(_16M(_1Fn));}),_1Fn));}),_1Fs[1],_1Fw[1]))==2?true:false;}};},_1Fx=function(_1Fy,_1Fz,_1FA,_1FB,_1FC,_1FD,_1FE){var _1FF=function(_1FG,_1FH){return new F(function(){return _2W(_1Fy,_1Fz,_1FA,_1FC,_1FB,_1FE,_1FD,_1FG);});};return function(_1FI,_1FJ){var _1FK=E(_1FI);if(!_1FK[0]){var _1FL=_1FK[1],_1FM=E(_1FJ);if(!_1FM[0]){var _1FN=_1FM[1];return B(_109(_1FL,_1FN,_1))[0]==0?B(_d3(B(_1r(_1FL)),B(_1r(_1FN))))==2?true:false:true;}else{return false;}}else{var _1FO=E(_1FJ);return _1FO[0]==0?true:B(_1BI(new T(function(){return B(_1Ei(new T(function(){return B(_16M(_1FF));}),_1FF));}),_1FK[1],_1FO[1]))==0?false:true;}};},_1FP=function(_1FQ,_1FR,_1FS,_1FT,_1FU,_1FV,_1FW){var _1FX=function(_1FY,_1FZ){return new F(function(){return _2W(_1FQ,_1FR,_1FS,_1FU,_1FT,_1FW,_1FV,_1FY);});};return function(_1G0,_1G1){var _1G2=E(_1G0);if(!_1G2[0]){var _1G3=_1G2[1],_1G4=E(_1G1);if(!_1G4[0]){var _1G5=_1G4[1];return B(_109(_1G3,_1G5,_1))[0]==0?B(_d3(B(_1r(_1G3)),B(_1r(_1G5))))==2?2:0:1;}else{return 0;}}else{var _1G6=E(_1G1);return _1G6[0]==0?2:B(_1BI(new T(function(){return B(_1Ei(new T(function(){return B(_16M(_1FX));}),_1FX));}),_1G2[1],_1G6[1]));}};},_1G7=function(_1G8,_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf){return [0,_1G8,new T(function(){return B(_1FP(_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf));}),new T(function(){return B(_1EX(_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf));}),new T(function(){return B(_1Fx(_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf));}),new T(function(){return B(_1Ff(_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf));}),new T(function(){return B(_1El(_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf));}),function(_44,_45){return new F(function(){return _1EB(_1G8,_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf,_44,_45);});},function(_44,_45){return new F(function(){return _1EM(_1G8,_1G9,_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf,_44,_45);});}];},_1Gg=new T(function(){return B(_3W(_Q,_u,_Q,_Q,_N,_2,_15));}),_1Gh=new T(function(){return B(_1G7(_1Gg,_Q,_u,_Q,_Q,_N,_15,_2));}),_1Gi=new T(function(){return B(_107(_1Gg));}),_1Gj=new T(function(){return B(_1Dm(_1Gi,_1Gh));}),_1Gk=function(_1Gl,_1Gm,_1Gn,_1Go){var _1Gp=E(_1Gn),_1Gq=E(_1Go);return new F(function(){return _1BR(_1Gm,_1Gp[1],_1Gp[2],_1Gq[1],_1Gq[2]);});},_1Gr=function(_1Gs,_1Gt,_1Gu,_1Gv){var _1Gw=E(_1Gu),_1Gx=E(_1Gv);return new F(function(){return _1C6(_1Gt,_1Gw[1],_1Gw[2],_1Gx[1],_1Gx[2]);});},_1Gy=function(_1Gz,_1GA,_1GB,_1GC){var _1GD=E(_1GB),_1GE=E(_1GC);return new F(function(){return _1Cl(_1GA,_1GD[1],_1GD[2],_1GE[1],_1GE[2]);});},_1GF=function(_1GG,_1GH,_1GI,_1GJ){var _1GK=E(_1GI),_1GL=E(_1GJ);return new F(function(){return _1CA(_1GH,_1GK[1],_1GK[2],_1GL[1],_1GL[2]);});},_1GM=function(_1GN,_1GO,_1GP,_1GQ){var _1GR=E(_1GP),_1GS=E(_1GQ);return new F(function(){return _1CN(_1GO,_1GR[1],_1GR[2],_1GS[1],_1GS[2]);});},_1GT=function(_1GU,_1GV,_1GW,_1GX){var _1GY=E(_1GW),_1GZ=_1GY[1],_1H0=_1GY[2],_1H1=E(_1GX),_1H2=_1H1[1],_1H3=_1H1[2];switch(B(_1BI(_1GV,_1GZ,_1H2))){case 0:return [0,_1H2,_1H3];case 1:return !B(A(_1C4,[_1GV,_1H0,_1H3]))?[0,_1GZ,_1H0]:[0,_1H2,_1H3];default:return [0,_1GZ,_1H0];}},_1H4=function(_1H5,_1H6,_1H7,_1H8){var _1H9=E(_1H7),_1Ha=_1H9[1],_1Hb=_1H9[2],_1Hc=E(_1H8),_1Hd=_1Hc[1],_1He=_1Hc[2];switch(B(_1BI(_1H6,_1Ha,_1Hd))){case 0:return [0,_1Ha,_1Hb];case 1:return !B(A(_1C4,[_1H6,_1Hb,_1He]))?[0,_1Hd,_1He]:[0,_1Ha,_1Hb];default:return [0,_1Hd,_1He];}},_1Hf=function(_1Hg,_1Hh){return [0,_1Hg,function(_ZT,_ZU){return new F(function(){return _1GM(_1Hg,_1Hh,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Gk(_1Hg,_1Hh,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1GF(_1Hg,_1Hh,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Gy(_1Hg,_1Hh,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1Gr(_1Hg,_1Hh,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1GT(_1Hg,_1Hh,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1H4(_1Hg,_1Hh,_ZT,_ZU);});}];},_1Hi=function(_1Hj,_1Hk){return B(_d3(_1Hj,_1Hk))==0?false:true;},_1Hl=function(_1Hm){return E(E(_1Hm)[1]);},_1Hn=function(_1Ho){return function(_1Hp,_1Hq){var _1Hr=E(_1Hp),_1Hs=E(_1Hq);switch(B(_1BI(new T(function(){return B(_1Hf(new T(function(){return B(_ZR(new T(function(){return B(_1Hl(_1Ho));})));}),_1Ho));}),_1Hr[1],_1Hs[1]))){case 0:return false;case 1:return new F(function(){return _1Hi(_1Hr[2],_1Hs[2]);});break;default:return true;}};},_1Ht=new T(function(){return B(_1Hn(_1Gj));}),_1Hu=function(_1Hv,_1Hw){return B(_d3(_1Hv,_1Hw))==2?false:true;},_1Hx=function(_1Hy){return function(_1Hz,_1HA){var _1HB=E(_1Hz),_1HC=E(_1HA);switch(B(_1BI(new T(function(){return B(_1Hf(new T(function(){return B(_ZR(new T(function(){return B(_1Hl(_1Hy));})));}),_1Hy));}),_1HB[1],_1HC[1]))){case 0:return true;case 1:return new F(function(){return _1Hu(_1HB[2],_1HC[2]);});break;default:return false;}};},_1HD=function(_1HE,_1HF,_1HG,_1HH){return !B(A(_1Hx,[_1HF,_1HG,_1HH]))?E(_1HG):E(_1HH);},_1HI=function(_1HJ,_1HK,_1HL,_1HM){return !B(A(_1Hx,[_1HK,_1HL,_1HM]))?E(_1HM):E(_1HL);},_1HN=function(_1HO,_1HP){return B(_d3(_1HO,_1HP))==0?true:false;},_1HQ=function(_1HR){return function(_1HS,_1HT){var _1HU=E(_1HS),_1HV=E(_1HT);switch(B(_1BI(new T(function(){return B(_1Hf(new T(function(){return B(_ZR(new T(function(){return B(_1Hl(_1HR));})));}),_1HR));}),_1HU[1],_1HV[1]))){case 0:return true;case 1:return new F(function(){return _1HN(_1HU[2],_1HV[2]);});break;default:return false;}};},_1HW=function(_1HX,_1HY){return B(_d3(_1HX,_1HY))==2?true:false;},_1HZ=function(_1I0){return function(_1I1,_1I2){var _1I3=E(_1I1),_1I4=E(_1I2);switch(B(_1BI(new T(function(){return B(_1Hf(new T(function(){return B(_ZR(new T(function(){return B(_1Hl(_1I0));})));}),_1I0));}),_1I3[1],_1I4[1]))){case 0:return false;case 1:return new F(function(){return _1HW(_1I3[2],_1I4[2]);});break;default:return true;}};},_1I5=function(_1I6){return function(_1I7,_1I8){var _1I9=E(_1I7),_1Ia=E(_1I8);switch(B(_1BI(new T(function(){return B(_1Hf(new T(function(){return B(_ZR(new T(function(){return B(_1Hl(_1I6));})));}),_1I6));}),_1I9[1],_1Ia[1]))){case 0:return 0;case 1:return new F(function(){return _d3(_1I9[2],_1Ia[2]);});break;default:return 2;}};},_1Ib=function(_1Ic,_1Id){return [0,_1Ic,new T(function(){return B(_1I5(_1Id));}),new T(function(){return B(_1HQ(_1Id));}),new T(function(){return B(_1Hn(_1Id));}),new T(function(){return B(_1HZ(_1Id));}),new T(function(){return B(_1Hx(_1Id));}),function(_ZT,_ZU){return new F(function(){return _1HD(_1Ic,_1Id,_ZT,_ZU);});},function(_ZT,_ZU){return new F(function(){return _1HI(_1Ic,_1Id,_ZT,_ZU);});}];},_1Ie=function(_1If,_1Ig,_1Ih,_1Ii,_1Ij){return !B(_Zt(new T(function(){return B(_ZR(_1If));}),_1Ig,_1Ii))?true:!B(_3x(_1Ih,_1Ij))?true:false;},_1Ik=function(_1Il,_1Im,_1In){var _1Io=E(_1Im),_1Ip=E(_1In);return new F(function(){return _1Ie(_1Il,_1Io[1],_1Io[2],_1Ip[1],_1Ip[2]);});},_1Iq=function(_1Ir){return function(_1Is,_1It){var _1Iu=E(_1Is),_1Iv=E(_1It);return !B(_Zt(new T(function(){return B(_ZR(_1Ir));}),_1Iu[1],_1Iv[1]))?false:B(_3x(_1Iu[2],_1Iv[2]));};},_1Iw=function(_1Ix){return [0,new T(function(){return B(_1Iq(_1Ix));}),function(_ZT,_ZU){return new F(function(){return _1Ik(_1Ix,_ZT,_ZU);});}];},_1Iy=new T(function(){return B(_1Iw(_1Gi));}),_1Iz=new T(function(){return B(_1Ib(_1Iy,_1Gj));}),_1IA=function(_1IB,_1IC,_1ID){var _1IE=E(_1IC),_1IF=E(_1ID);if(!_1IF[0]){var _1IG=_1IF[2],_1IH=_1IF[3],_1II=_1IF[4];switch(B(A(_1BG,[_1IB,_1IE,_1IG]))){case 0:return new F(function(){return _1eu(_1IG,B(_1IA(_1IB,_1IE,_1IH)),_1II);});break;case 1:return [0,_1IF[1],E(_1IE),E(_1IH),E(_1II)];default:return new F(function(){return _1f6(_1IG,_1IH,B(_1IA(_1IB,_1IE,_1II)));});}}else{return [0,1,E(_1IE),E(_1ep),E(_1ep)];}},_1IJ=function(_1IK,_1IL){while(1){var _1IM=E(_1IL);if(!_1IM[0]){return E(_1IK);}else{var _1IN=B(_1IA(_1Iz,_1IM[1],_1IK));_1IL=_1IM[2];_1IK=_1IN;continue;}}},_1IO=function(_1IP,_1IQ){var _1IR=E(_1IQ);if(!_1IR[0]){return [0,_1ep,_9,_9];}else{var _1IS=_1IR[1],_1IT=E(_1IP);if(_1IT==1){var _1IU=E(_1IR[2]);return _1IU[0]==0?[0,new T(function(){return [0,1,E(E(_1IS)),E(_1ep),E(_1ep)];}),_9,_9]:!B(A(_1Ht,[_1IS,_1IU[1]]))?[0,new T(function(){return [0,1,E(E(_1IS)),E(_1ep),E(_1ep)];}),_1IU,_9]:[0,new T(function(){return [0,1,E(E(_1IS)),E(_1ep),E(_1ep)];}),_9,_1IU];}else{var _1IV=B(_1IO(_1IT>>1,_1IR)),_1IW=_1IV[1],_1IX=_1IV[3],_1IY=E(_1IV[2]);if(!_1IY[0]){return [0,_1IW,_9,_1IX];}else{var _1IZ=_1IY[1],_1J0=E(_1IY[2]);if(!_1J0[0]){return [0,new T(function(){return B(_1fM(_1IZ,_1IW));}),_9,_1IX];}else{if(!B(A(_1Ht,[_1IZ,_1J0[1]]))){var _1J1=B(_1IO(_1IT>>1,_1J0));return [0,new T(function(){return B(_1gq(_1IZ,_1IW,_1J1[1]));}),_1J1[2],_1J1[3]];}else{return [0,_1IW,_9,_1IY];}}}}}},_1J2=function(_1J3,_1J4,_1J5){while(1){var _1J6=E(_1J5);if(!_1J6[0]){return E(_1J4);}else{var _1J7=_1J6[1],_1J8=E(_1J6[2]);if(!_1J8[0]){return new F(function(){return _1fM(_1J7,_1J4);});}else{if(!B(A(_1Ht,[_1J7,_1J8[1]]))){var _1J9=B(_1IO(_1J3,_1J8)),_1Ja=_1J9[1],_1Jb=E(_1J9[3]);if(!_1Jb[0]){var _1Jc=_1J3<<1,_1Jd=B(_1gq(_1J7,_1J4,_1Ja));_1J5=_1J9[2];_1J3=_1Jc;_1J4=_1Jd;continue;}else{return new F(function(){return _1IJ(B(_1gq(_1J7,_1J4,_1Ja)),_1Jb);});}}else{return new F(function(){return _1IJ(_1J4,_1J6);});}}}}},_1Je=function(_1Jf){var _1Jg=E(_1Jf);if(!_1Jg[0]){return [1];}else{var _1Jh=_1Jg[1],_1Ji=E(_1Jg[2]);if(!_1Ji[0]){return [0,1,E(E(_1Jh)),E(_1ep),E(_1ep)];}else{if(!B(A(_1Ht,[_1Jh,_1Ji[1]]))){return new F(function(){return _1J2(1,[0,1,E(E(_1Jh)),E(_1ep),E(_1ep)],_1Ji);});}else{return new F(function(){return _1IJ([0,1,E(E(_1Jh)),E(_1ep),E(_1ep)],_1Ji);});}}}},_1Jj=new T(function(){return B(_F(0,1,_9));}),_1Jk=new T(function(){return B(unAppCStr("delta_",_1Jj));}),_1Jl=[9,_,_,_1Jk],_1Jm=[0,_1Jl],_1Jn=[1,_1Jm,_9],_1Jo=new T(function(){return B(unAppCStr("phi_",_1Jj));}),_1Jp=[3,_,_,_1Jo],_1Jq=[2,_,_1Jp],_1Jr=[1,_1Jq,_9],_1Js=[1,_1Jr],_1Jt=[0,_1Jn,_1Js],_1Ju=new T(function(){return B(_F(0,2,_9));}),_1Jv=new T(function(){return B(unAppCStr("phi_",_1Ju));}),_1Jw=[3,_,_,_1Jv],_1Jx=[2,_,_1Jw],_1Jy=[1,_1Jx,_9],_1Jz=[1,_1Jy],_1JA=new T(function(){return B(unAppCStr("delta_",_1Ju));}),_1JB=[9,_,_,_1JA],_1JC=[0,_1JB],_1JD=[1,_1JC,_9],_1JE=[0,_1JD,_1Jz],_1JF=[1,_1JE,_9],_1JG=[1,_1Jt,_1JF],_1JH=function(_1JI,_1JJ){var _1JK=E(_1JI);if(!_1JK[0]){return [0];}else{var _1JL=_1JK[1],_1JM=_1JK[2],_1JN=function(_1JO,_1JP,_1JQ){var _1JR=E(_1JP);if(!_1JR[0]){return [0,_1JM,_1JQ];}else{var _1JS=_1JR[1],_1JT=new T(function(){var _1JU=B(_1JN(function(_1JV){return new F(function(){return A(_1JO,[[1,_1JS,_1JV]]);});},_1JR[2],_1JQ));return [0,_1JU[1],_1JU[2]];}),_1JW=new T(function(){return E(E(_1JT)[1]);});return [0,[1,_1JS,_1JW],[1,new T(function(){return B(A(_1JO,[[1,_1JL,[1,_1JS,_1JW]]]));}),new T(function(){return E(E(_1JT)[2]);})]];}},_1JX=function(_1JY){var _1JZ=E(_1JY);return _1JZ[0]==0?E(new T(function(){return B(_1JH(_1JM,[1,_1JL,_1JJ]));})):E(B(_1JN(_6P,_1JZ[1],new T(function(){return B(_1JX(_1JZ[2]));})))[2]);};return new F(function(){return _1JX([1,_1JJ,new T(function(){return B(_1JH(_1JJ,_9));})]);});}},_1K0=new T(function(){return B(_1JH(_1JG,_9));}),_1K1=[1,_1JG,_1K0],_1K2=[9,_,_P8,_1Jq,_1Jx],_1K3=[1,_1K2,_9],_1K4=[1,_1K3],_1K5=[1,_1Jm,_1JD],_1K6=[0,_1K5,_1K4],_1K7=function(_1K8){return [0,_1K8,_1K6];},_1K9=new T(function(){return B(_3d(_1K7,_1K1));}),_1Ka=[0,_1K9,_1Bm],_1Kb=[1,_1Jt,_9],_1Kc=[9,_,_OK,_1Jq,_1Jx],_1Kd=[1,_1Kc,_9],_1Ke=[1,_1Kd],_1Kf=[0,_1Jn,_1Ke],_1Kg=[0,_1Kb,_1Kf],_1Kh=[9,_,_OK,_1Jx,_1Jq],_1Ki=[1,_1Kh,_9],_1Kj=[1,_1Ki],_1Kk=[0,_1Jn,_1Kj],_1Kl=[0,_1Kb,_1Kk],_1Km=[1,_1Kl,_9],_1Kn=[1,_1Kg,_1Km],_1Ko=[0,_1Kn,_1Bl],_1Kp=[1,_1Js,_1Jn],_1Kq=[0,_1Kp,_1Jz],_1Kr=[1,_1Js,_1JD],_1Ks=[7,_,_Pz,_1Jx],_1Kt=[1,_1Ks,_9],_1Ku=[1,_1Kt],_1Kv=[0,_1Kr,_1Ku],_1Kw=[1,_1Kv,_9],_1Kx=[1,_1Kq,_1Kw],_1Ky=new T(function(){return B(_1JH(_1Kx,_9));}),_1Kz=[1,_1Kx,_1Ky],_1KA=[7,_,_Pz,_1Jq],_1KB=[1,_1KA,_9],_1KC=[1,_1KB],_1KD=[0,_1K5,_1KC],_1KE=[0,_1K5,_1Js],_1KF=function(_1KG){return [0,_1KG,_1KE];},_1KH=[0,_1Jn,_1Jz],_1KI=[1,_1KH,_9],_1KJ=[0,_1JD,_1Ku],_1KK=[1,_1KJ,_1KI],_1KL=new T(function(){return B(_1JH(_1KK,_9));}),_1KM=[1,_1KK,_1KL],_1KN=new T(function(){return B(_3d(_1KF,_1KM));}),_1KO=function(_1KP){var _1KQ=E(_1KP);return _1KQ[0]==0?E(_1KN):[1,[0,_1KQ[1],_1KE],new T(function(){return B(_1KO(_1KQ[2]));})];},_1KR=[1,_1KC,_1JD],_1KS=[0,_1KR,_1Ku],_1KT=[1,_1KS,_1KI],_1KU=new T(function(){return B(_1JH(_1KT,_9));}),_1KV=[1,_1KT,_1KU],_1KW=new T(function(){return B(_1KO(_1KV));}),_1KX=function(_1KY){var _1KZ=E(_1KY);return _1KZ[0]==0?E(_1KW):[1,[0,_1KZ[1],_1KE],new T(function(){return B(_1KX(_1KZ[2]));})];},_1L0=[1,_1KC,_1Jn],_1L1=[0,_1L0,_1Jz],_1L2=[1,_1L1,_9],_1L3=[1,_1KJ,_1L2],_1L4=new T(function(){return B(_1JH(_1L3,_9));}),_1L5=[1,_1L3,_1L4],_1L6=new T(function(){return B(_1KX(_1L5));}),_1L7=function(_1L8){var _1L9=E(_1L8);return _1L9[0]==0?E(_1L6):[1,[0,_1L9[1],_1KE],new T(function(){return B(_1L7(_1L9[2]));})];},_1La=[1,_1KS,_1L2],_1Lb=new T(function(){return B(_1JH(_1La,_9));}),_1Lc=[1,_1La,_1Lb],_1Ld=new T(function(){return B(_1L7(_1Lc));}),_1Le=function(_1Lf){var _1Lg=E(_1Lf);return _1Lg[0]==0?E(_1Ld):[1,[0,_1Lg[1],_1KD],new T(function(){return B(_1Le(_1Lg[2]));})];},_1Lh=[1,_1KJ,_9],_1Li=[1,_1KH,_1Lh],_1Lj=new T(function(){return B(_1JH(_1Li,_9));}),_1Lk=[1,_1Li,_1Lj],_1Ll=new T(function(){return B(_1Le(_1Lk));}),_1Lm=function(_1Ln){var _1Lo=E(_1Ln);return _1Lo[0]==0?E(_1Ll):[1,[0,_1Lo[1],_1KD],new T(function(){return B(_1Lm(_1Lo[2]));})];},_1Lp=[1,_1Kq,_1Lh],_1Lq=new T(function(){return B(_1JH(_1Lp,_9));}),_1Lr=[1,_1Lp,_1Lq],_1Ls=new T(function(){return B(_1Lm(_1Lr));}),_1Lt=function(_1Lu){var _1Lv=E(_1Lu);return _1Lv[0]==0?E(_1Ls):[1,[0,_1Lv[1],_1KD],new T(function(){return B(_1Lt(_1Lv[2]));})];},_1Lw=[1,_1KH,_1Kw],_1Lx=new T(function(){return B(_1JH(_1Lw,_9));}),_1Ly=[1,_1Lw,_1Lx],_1Lz=new T(function(){return B(_1Lt(_1Ly));}),_1LA=function(_1LB){var _1LC=E(_1LB);return _1LC[0]==0?E(_1Lz):[1,[0,_1LC[1],_1KD],new T(function(){return B(_1LA(_1LC[2]));})];},_1LD=new T(function(){return B(_1LA(_1Kz));}),_1LE=[0,_1LD,_1Bw],_1LF=[1,_1LE,_9],_1LG=[1,_1Ko,_1LF],_1LH=[0,83],_1LI=[1,_1LH,_9],_1LJ=[0,_1Jn,_1K4],_1LK=[1,_1LJ,_9],_1LL=[0,_1LK,_1Jt],_1LM=[0,_1LK,_1KH],_1LN=[1,_1LM,_9],_1LO=[1,_1LL,_1LN],_1LP=[0,_1LO,_1LI],_1LQ=[1,_1LP,_1LG],_1LR=[1,_1Kk,_1Lh],_1LS=new T(function(){return B(_1JH(_1LR,_9));}),_1LT=[1,_1LR,_1LS],_1LU=[0,_1JD,_1KC],_1LV=[1,_1LU,_9],_1LW=[1,_1Kk,_1LV],_1LX=new T(function(){return B(_1JH(_1LW,_9));}),_1LY=[1,_1LW,_1LX],_1LZ=[0,_1K5,_1Jz],_1M0=function(_1M1){return [0,_1M1,_1LZ];},_1M2=new T(function(){return B(_3d(_1M0,_1LY));}),_1M3=function(_1M4){var _1M5=E(_1M4);return _1M5[0]==0?E(_1M2):[1,[0,_1M5[1],_1KE],new T(function(){return B(_1M3(_1M5[2]));})];},_1M6=new T(function(){return B(_1M3(_1LT));}),_1M7=[0,_1M6,_1Bu],_1M8=[1,_1M7,_1LQ],_1M9=[9,_,_Ny,_1Jq,_1Jx],_1Ma=[1,_1M9,_9],_1Mb=[1,_1Ma],_1Mc=[0,_1JD,_1Mb],_1Md=[1,_1Mc,_9],_1Me=[1,_1Jt,_1Md],_1Mf=new T(function(){return B(_1JH(_1Me,_9));}),_1Mg=[1,_1Me,_1Mf],_1Mh=new T(function(){return B(_3d(_1M0,_1Mg));}),_1Mi=[0,_1Mh,_1Bv],_1Mj=[1,_1Mi,_1M8],_1Mk=[0,_1Jn,_1Mb],_1Ml=[1,_1Kq,_9],_1Mm=[0,_1Ml,_1Mk],_1Mn=[0,_1KI,_1Mk],_1Mo=[1,_1Mn,_9],_1Mp=[1,_1Mm,_1Mo],_1Mq=[0,_1Mp,_1Bx],_1Mr=[1,_1Mq,_1Mj],_1Ms=[1,_1Ka,_1Mr],_1Mt=new T(function(){return B(_1Je(_1Ms));}),_1Mu=[0,_1BD,_1Mt],_1Mv=function(_){return new F(function(){return _1AY(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1Mu,_);});},_1Mw=function(_){return new F(function(){return _1Mv(_);});};
var hasteMain = function() {B(A(_1Mw, [0]));};window.onload = hasteMain;