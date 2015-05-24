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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr(" . "));}),_1r=function(_1s){var _1t=E(_1s);switch(_1t[0]){case 0:return E(_1t[3]);case 1:return E(_1t[3]);case 2:return E(_1t[3]);case 3:return E(_1t[3]);case 4:return E(_1t[3]);case 5:return E(_1t[3]);case 6:return E(_1t[3]);case 7:return E(_1t[3]);case 8:return E(_1t[3]);default:return E(_1t[3]);}},_1u=[0,41],_1v=[1,_1u,_9],_1w=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1x=new T(function(){return B(unCStr("base"));}),_1y=new T(function(){return B(unCStr("PatternMatchFail"));}),_1z=new T(function(){var _1A=hs_wordToWord64(18445595),_1B=_1A,_1C=hs_wordToWord64(52003073),_1D=_1C;return [0,_1B,_1D,[0,_1B,_1D,_1x,_1w,_1y],_9];}),_1E=function(_1F){return E(_1z);},_1G=function(_1H){return E(E(_1H)[1]);},_1I=function(_1J,_1K,_1L){var _1M=B(A(_1J,[_])),_1N=B(A(_1K,[_])),_1O=hs_eqWord64(_1M[1],_1N[1]),_1P=_1O;if(!E(_1P)){return [0];}else{var _1Q=hs_eqWord64(_1M[2],_1N[2]),_1R=_1Q;return E(_1R)==0?[0]:[1,_1L];}},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return _1I(B(_1G(_1U[1])),_1E,_1U[2]);});},_1V=function(_1W){return E(E(_1W)[1]);},_1X=function(_1Y,_1Z){return new F(function(){return _e(E(_1Y)[1],_1Z);});},_20=[0,44],_21=[0,93],_22=[0,91],_23=function(_24,_25,_26){var _27=E(_25);return _27[0]==0?B(unAppCStr("[]",_26)):[1,_22,new T(function(){return B(A(_24,[_27[1],new T(function(){var _28=function(_29){var _2a=E(_29);return _2a[0]==0?E([1,_21,_26]):[1,_20,new T(function(){return B(A(_24,[_2a[1],new T(function(){return B(_28(_2a[2]));})]));})];};return B(_28(_27[2]));})]));})];},_2b=function(_2c,_2d){return new F(function(){return _23(_1X,_2c,_2d);});},_2e=function(_2f,_2g,_2h){return new F(function(){return _e(E(_2g)[1],_2h);});},_2i=[0,_2e,_1V,_2b],_2j=new T(function(){return [0,_1E,_2i,_2k,_1S];}),_2k=function(_2l){return [0,_2j,_2l];},_2m=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_2n=function(_2o,_2p){return new F(function(){return die(new T(function(){return B(A(_2p,[_2o]));}));});},_2q=function(_2r,_2s){var _2t=E(_2s);if(!_2t[0]){return [0,_9,_9];}else{var _2u=_2t[1];if(!B(A(_2r,[_2u]))){return [0,_9,_2t];}else{var _2v=new T(function(){var _2w=B(_2q(_2r,_2t[2]));return [0,_2w[1],_2w[2]];});return [0,[1,_2u,new T(function(){return E(E(_2v)[1]);})],new T(function(){return E(E(_2v)[2]);})];}}},_2x=[0,32],_2y=[0,10],_2z=[1,_2y,_9],_2A=function(_2B){return E(E(_2B)[1])==124?false:true;},_2C=function(_2D,_2E){var _2F=B(_2q(_2A,B(unCStr(_2D)))),_2G=_2F[1],_2H=function(_2I,_2J){return new F(function(){return _e(_2I,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_2E,new T(function(){return B(_e(_2J,_2z));},1)));})));},1));});},_2K=E(_2F[2]);if(!_2K[0]){return new F(function(){return _2H(_2G,_9);});}else{return E(E(_2K[1])[1])==124?B(_2H(_2G,[1,_2x,_2K[2]])):B(_2H(_2G,_9));}},_2L=function(_2M){return new F(function(){return _2n([0,new T(function(){return B(_2C(_2M,_2m));})],_2k);});},_2N=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_2O=[0,44],_2P=[0,40],_2Q=function(_2R,_2S,_2T){var _2U=E(_2T);switch(_2U[0]){case 0:return E(_2N);case 1:return new F(function(){return A(_2R,[_2U[2],_9]);});break;case 2:return new F(function(){return _1r(_2U[2]);});break;case 3:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2S,[_2U[2],[1,new T(function(){return B(_2Q(_2R,_2S,_2U[3]));}),[1,new T(function(){return B(_2Q(_2R,_2S,_2U[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_1r(_2U[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_2R,_2S,_2U[4])),_1v));})]));})]);});}},_2V=[0],_2W=function(_2X,_2Y,_2Z,_30,_31,_32,_33,_34){var _35=E(_34);switch(_35[0]){case 0:return [0];case 1:return new F(function(){return A(_30,[_35[2],_9]);});break;case 2:return new F(function(){return _1r(_35[2]);});break;case 3:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),_1v));})]);});break;case 5:return new F(function(){return A(_2X,[_35[2],[1,new T(function(){return B(_2Q(_30,_31,_35[3]));}),[1,new T(function(){return B(_2Q(_30,_31,_35[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_1r(_35[2])),[1,_2P,new T(function(){return B(_e(B(_2Q(_30,_31,_35[3])),[1,_2O,new T(function(){return B(_e(B(_2Q(_30,_31,_35[4])),_1v));})]));})]);});break;case 7:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_1r(_35[2])),new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));},1));});break;case 9:return new F(function(){return A(_2Y,[_35[2],[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4]));}),_9]]]);});break;case 10:return [1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[3])),new T(function(){return B(_e(B(_1r(_35[2])),new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,_35[4])),_1v));},1)));},1)));})];case 11:var _36=_35[2],_37=_35[3];return new F(function(){return A(_2Z,[_36,[1,new T(function(){return B(A(_32,[new T(function(){return B(A(_37,[_2V]));}),_36]));}),[1,new T(function(){return B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_37,[_2V]))));}),_9]]]);});break;default:var _38=_35[2],_39=_35[3];return new F(function(){return _e(B(_1r(_38)),new T(function(){return B(_e(B(A(_33,[new T(function(){return B(A(_39,[_2V]));}),_38])),[1,_2P,new T(function(){return B(_e(B(_2W(_2X,_2Y,_2Z,_30,_31,_32,_33,B(A(_39,[_2V])))),_1v));})]));},1));});}},_3a=function(_3b){var _3c=E(_3b);if(!_3c[0]){return [0];}else{return new F(function(){return _e(_3c[1],new T(function(){return B(_3a(_3c[2]));},1));});}},_3d=function(_3e,_3f){var _3g=E(_3f);return _3g[0]==0?[0]:[1,new T(function(){return B(A(_3e,[_3g[1]]));}),new T(function(){return B(_3d(_3e,_3g[2]));})];},_3h=function(_3i,_3j){var _3k=E(_3j);return _3k[0]==0?[0]:[1,_3i,[1,_3k[1],new T(function(){return B(_3h(_3i,_3k[2]));})]];},_3l=function(_3m,_3n,_3o,_3p,_3q,_3r,_3s,_3t){var _3u=E(_3t);if(!_3u[0]){return new F(function(){return _1r(_3u[1]);});}else{var _3v=B(_3d(function(_3w){return new F(function(){return _2W(_3m,_3n,_3o,_3q,_3p,_3r,_3s,_3w);});},_3u[1]));return _3v[0]==0?[0]:B(_3a([1,_3v[1],new T(function(){return B(_3h(_1q,_3v[2]));})]));}},_3x=function(_3y,_3z){while(1){var _3A=E(_3y);if(!_3A[0]){return E(_3z)[0]==0?true:false;}else{var _3B=E(_3z);if(!_3B[0]){return false;}else{if(E(_3A[1])[1]!=E(_3B[1])[1]){return false;}else{_3y=_3A[2];_3z=_3B[2];continue;}}}}},_3C=function(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K,_3L){return new F(function(){return _3x(B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3K)),B(_3l(_3D,_3E,_3F,_3G,_3H,_3I,_3J,_3L)));});},_3M=function(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V){return !B(_3C(_3N,_3O,_3P,_3Q,_3R,_3S,_3T,_3U,_3V))?true:false;},_3W=function(_3X,_3Y,_3Z,_40,_41,_42,_43){return [0,function(_44,_45){return new F(function(){return _3C(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});},function(_44,_45){return new F(function(){return _3M(_3X,_3Y,_3Z,_40,_41,_42,_43,_44,_45);});}];},_46=new T(function(){return B(unCStr("wheel"));}),_47=new T(function(){return B(unCStr("mouseout"));}),_48=new T(function(){return B(unCStr("mouseover"));}),_49=new T(function(){return B(unCStr("mousemove"));}),_4a=new T(function(){return B(unCStr("blur"));}),_4b=new T(function(){return B(unCStr("focus"));}),_4c=new T(function(){return B(unCStr("change"));}),_4d=new T(function(){return B(unCStr("unload"));}),_4e=new T(function(){return B(unCStr("load"));}),_4f=new T(function(){return B(unCStr("submit"));}),_4g=new T(function(){return B(unCStr("keydown"));}),_4h=new T(function(){return B(unCStr("keyup"));}),_4i=new T(function(){return B(unCStr("keypress"));}),_4j=new T(function(){return B(unCStr("mouseup"));}),_4k=new T(function(){return B(unCStr("mousedown"));}),_4l=new T(function(){return B(unCStr("dblclick"));}),_4m=new T(function(){return B(unCStr("click"));}),_4n=function(_4o){switch(E(_4o)[0]){case 0:return E(_4e);case 1:return E(_4d);case 2:return E(_4c);case 3:return E(_4b);case 4:return E(_4a);case 5:return E(_49);case 6:return E(_48);case 7:return E(_47);case 8:return E(_4m);case 9:return E(_4l);case 10:return E(_4k);case 11:return E(_4j);case 12:return E(_4i);case 13:return E(_4h);case 14:return E(_4g);case 15:return E(_4f);default:return E(_46);}},_4p=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_4q=new T(function(){return B(unCStr("main"));}),_4r=new T(function(){return B(unCStr("EventData"));}),_4s=new T(function(){var _4t=hs_wordToWord64(3703396926),_4u=_4t,_4v=hs_wordToWord64(1660403598),_4w=_4v;return [0,_4u,_4w,[0,_4u,_4w,_4q,_4p,_4r],_9];}),_4x=[0,0],_4y=false,_4z=2,_4A=[1],_4B=new T(function(){return B(unCStr("Dynamic"));}),_4C=new T(function(){return B(unCStr("Data.Dynamic"));}),_4D=new T(function(){return B(unCStr("base"));}),_4E=new T(function(){var _4F=hs_wordToWord64(628307645),_4G=_4F,_4H=hs_wordToWord64(949574464),_4I=_4H;return [0,_4G,_4I,[0,_4G,_4I,_4D,_4C,_4B],_9];}),_4J=[0],_4K=new T(function(){return B(unCStr("OnLoad"));}),_4L=[0,_4K,_4J],_4M=[0,_4s,_4L],_4N=[0,_4E,_4M],_4O=[0],_4P=function(_){return _4O;},_4Q=function(_4R,_){return _4O;},_4S=[0,_4P,_4Q],_4T=[0,_9,_4x,_4z,_4S,_4y,_4N,_4A],_4U=function(_){var _=0,_4V=newMVar(),_4W=_4V,_=putMVar(_4W,_4T);return [0,_4W];},_4X=function(_4Y){var _4Z=B(A(_4Y,[_])),_50=_4Z;return E(_50);},_51=new T(function(){return B(_4X(_4U));}),_52=new T(function(){return B(_2L("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_53=[0,_4e,_4J],_54=[0,_4s,_53],_55=[0,_4d,_4J],_56=[0,_4s,_55],_57=[0,_4c,_4J],_58=[0,_4s,_57],_59=[0,_4b,_4J],_5a=[0,_4s,_59],_5b=[0,_4a,_4J],_5c=[0,_4s,_5b],_5d=[3],_5e=[0,_47,_5d],_5f=[0,_4s,_5e],_5g=function(_5h,_5i){switch(E(_5h)[0]){case 0:return function(_){var _5j=E(_51)[1],_5k=takeMVar(_5j),_5l=_5k,_=putMVar(_5j,new T(function(){var _5m=E(_5l);return [0,_5m[1],_5m[2],_5m[3],_5m[4],_5m[5],_54,_5m[7]];}));return new F(function(){return A(_5i,[_]);});};case 1:return function(_){var _5n=E(_51)[1],_5o=takeMVar(_5n),_5p=_5o,_=putMVar(_5n,new T(function(){var _5q=E(_5p);return [0,_5q[1],_5q[2],_5q[3],_5q[4],_5q[5],_56,_5q[7]];}));return new F(function(){return A(_5i,[_]);});};case 2:return function(_){var _5r=E(_51)[1],_5s=takeMVar(_5r),_5t=_5s,_=putMVar(_5r,new T(function(){var _5u=E(_5t);return [0,_5u[1],_5u[2],_5u[3],_5u[4],_5u[5],_58,_5u[7]];}));return new F(function(){return A(_5i,[_]);});};case 3:return function(_){var _5v=E(_51)[1],_5w=takeMVar(_5v),_5x=_5w,_=putMVar(_5v,new T(function(){var _5y=E(_5x);return [0,_5y[1],_5y[2],_5y[3],_5y[4],_5y[5],_5a,_5y[7]];}));return new F(function(){return A(_5i,[_]);});};case 4:return function(_){var _5z=E(_51)[1],_5A=takeMVar(_5z),_5B=_5A,_=putMVar(_5z,new T(function(){var _5C=E(_5B);return [0,_5C[1],_5C[2],_5C[3],_5C[4],_5C[5],_5c,_5C[7]];}));return new F(function(){return A(_5i,[_]);});};case 5:return function(_5D){return function(_){var _5E=E(_51)[1],_5F=takeMVar(_5E),_5G=_5F,_=putMVar(_5E,new T(function(){var _5H=E(_5G);return [0,_5H[1],_5H[2],_5H[3],_5H[4],_5H[5],[0,_4s,[0,_49,[2,E(_5D)]]],_5H[7]];}));return new F(function(){return A(_5i,[_]);});};};case 6:return function(_5I){return function(_){var _5J=E(_51)[1],_5K=takeMVar(_5J),_5L=_5K,_=putMVar(_5J,new T(function(){var _5M=E(_5L);return [0,_5M[1],_5M[2],_5M[3],_5M[4],_5M[5],[0,_4s,[0,_48,[2,E(_5I)]]],_5M[7]];}));return new F(function(){return A(_5i,[_]);});};};case 7:return function(_){var _5N=E(_51)[1],_5O=takeMVar(_5N),_5P=_5O,_=putMVar(_5N,new T(function(){var _5Q=E(_5P);return [0,_5Q[1],_5Q[2],_5Q[3],_5Q[4],_5Q[5],_5f,_5Q[7]];}));return new F(function(){return A(_5i,[_]);});};case 8:return function(_5R,_5S){return function(_){var _5T=E(_51)[1],_5U=takeMVar(_5T),_5V=_5U,_=putMVar(_5T,new T(function(){var _5W=E(_5V);return [0,_5W[1],_5W[2],_5W[3],_5W[4],_5W[5],[0,_4s,[0,_4m,[1,_5R,E(_5S)]]],_5W[7]];}));return new F(function(){return A(_5i,[_]);});};};case 9:return function(_5X,_5Y){return function(_){var _5Z=E(_51)[1],_60=takeMVar(_5Z),_61=_60,_=putMVar(_5Z,new T(function(){var _62=E(_61);return [0,_62[1],_62[2],_62[3],_62[4],_62[5],[0,_4s,[0,_4l,[1,_5X,E(_5Y)]]],_62[7]];}));return new F(function(){return A(_5i,[_]);});};};case 10:return function(_63,_64){return function(_){var _65=E(_51)[1],_66=takeMVar(_65),_67=_66,_=putMVar(_65,new T(function(){var _68=E(_67);return [0,_68[1],_68[2],_68[3],_68[4],_68[5],[0,_4s,[0,_4k,[1,_63,E(_64)]]],_68[7]];}));return new F(function(){return A(_5i,[_]);});};};case 11:return function(_69,_6a){return function(_){var _6b=E(_51)[1],_6c=takeMVar(_6b),_6d=_6c,_=putMVar(_6b,new T(function(){var _6e=E(_6d);return [0,_6e[1],_6e[2],_6e[3],_6e[4],_6e[5],[0,_4s,[0,_4j,[1,_69,E(_6a)]]],_6e[7]];}));return new F(function(){return A(_5i,[_]);});};};case 12:return function(_6f,_){var _6g=E(_51)[1],_6h=takeMVar(_6g),_6i=_6h,_=putMVar(_6g,new T(function(){var _6j=E(_6i);return [0,_6j[1],_6j[2],_6j[3],_6j[4],_6j[5],[0,_4s,[0,_4i,[4,_6f]]],_6j[7]];}));return new F(function(){return A(_5i,[_]);});};case 13:return function(_6k,_){var _6l=E(_51)[1],_6m=takeMVar(_6l),_6n=_6m,_=putMVar(_6l,new T(function(){var _6o=E(_6n);return [0,_6o[1],_6o[2],_6o[3],_6o[4],_6o[5],[0,_4s,[0,_4h,[4,_6k]]],_6o[7]];}));return new F(function(){return A(_5i,[_]);});};case 14:return function(_6p,_){var _6q=E(_51)[1],_6r=takeMVar(_6q),_6s=_6r,_=putMVar(_6q,new T(function(){var _6t=E(_6s);return [0,_6t[1],_6t[2],_6t[3],_6t[4],_6t[5],[0,_4s,[0,_4g,[4,_6p]]],_6t[7]];}));return new F(function(){return A(_5i,[_]);});};default:return E(_52);}},_6u=[0,_4n,_5g],_6v=function(_6w,_6x,_){var _6y=jsCreateTextNode(toJSStr(E(_6w))),_6z=_6y,_6A=jsAppendChild(_6z,E(_6x)[1]);return [0,_6z];},_6B=0,_6C=function(_6D,_6E,_6F,_6G){return new F(function(){return A(_6D,[function(_){var _6H=jsSetAttr(E(_6E)[1],toJSStr(E(_6F)),toJSStr(E(_6G)));return _6B;}]);});},_6I=[0,112],_6J=function(_6K){var _6L=new T(function(){return E(E(_6K)[2]);});return function(_6M,_){return [0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_6L)[1],_9)),new T(function(){return E(E(_6K)[1]);},1)));})],new T(function(){var _6N=E(_6K);return [0,_6N[1],new T(function(){return [0,E(_6L)[1]+1|0];}),_6N[3],_6N[4],_6N[5],_6N[6],_6N[7]];})];};},_6O=new T(function(){return B(unCStr("id"));}),_6P=function(_6Q){return E(_6Q);},_6R=new T(function(){return B(unCStr("noid"));}),_6S=function(_6T,_){return _6T;},_6U=function(_6V,_6W,_){var _6X=jsFind(toJSStr(E(_6W))),_6Y=_6X,_6Z=E(_6Y);if(!_6Z[0]){var _70=E(_51)[1],_71=takeMVar(_70),_72=_71,_73=B(A(_6V,[_72,_])),_74=_73,_75=E(_74),_=putMVar(_70,_75[2]);return E(_75[1])[2];}else{var _76=E(_6Z[1]),_77=jsClearChildren(_76[1]),_78=E(_51)[1],_79=takeMVar(_78),_7a=_79,_7b=B(A(_6V,[_7a,_])),_7c=_7b,_7d=E(_7c),_7e=E(_7d[1]),_=putMVar(_78,_7d[2]),_7f=B(A(_7e[1],[_76,_])),_7g=_7f;return _7e[2];}},_7h=new T(function(){return B(unCStr("span"));}),_7i=function(_7j,_7k,_7l,_){var _7m=jsCreateElem(toJSStr(E(_7h))),_7n=_7m,_7o=jsAppendChild(_7n,E(_7l)[1]),_7p=[0,_7n],_7q=B(A(_7j,[_7k,_7p,_])),_7r=_7q;return _7p;},_7s=function(_7t){return E(_7t);},_7u=function(_7v,_7w,_7x,_){var _7y=B(A(_6J,[_7x,_7x,_])),_7z=_7y,_7A=E(_7z),_7B=_7A[1],_7C=E(_7A[2]),_7D=_7C[2],_7E=E(_7C[4]),_7F=B(A(_7v,[[0,_7C[1],_7D,_7C[3],[0,function(_){return new F(function(){return _6U(function(_7G,_){var _7H=B(A(_7v,[new T(function(){var _7I=E(_7G);return [0,_7I[1],_7D,_7I[3],_7I[4],_7I[5],_7I[6],_7I[7]];}),_])),_7J=_7H;return [0,[0,_6S,E(E(_7J)[1])[2]],_7G];},_6R,_);});},function(_7K,_){var _7L=B(_6U(new T(function(){return B(A(_7w,[_7K]));},1),_7B,_)),_7M=_7L,_7N=E(_7M);return _7N[0]==0?_4O:B(A(_7E[2],[_7N[1],_]));}],_7C[5],_7C[6],_7C[7]],_])),_7O=_7F,_7P=E(_7O),_7Q=_7P[2],_7R=E(_7P[1]),_7S=_7R[1],_7T=E(_7R[2]);if(!_7T[0]){return [0,[0,function(_7U,_){var _7V=B(A(_7S,[_7U,_])),_7W=_7V;if(!E(E(_7x)[5])){var _7X=B(_7i(_7s,_6S,_7U,_)),_7Y=_7X,_7Z=B(A(_6C,[_6P,_7Y,_6O,_7B,_])),_80=_7Z;return _7U;}else{return _7U;}},_4O],new T(function(){var _81=E(_7Q);return [0,_81[1],_81[2],_81[3],_7E,_81[5],_81[6],_81[7]];})];}else{var _82=B(A(_7w,[_7T[1],new T(function(){var _83=E(_7Q);return [0,_83[1],_83[2],_83[3],_7E,_83[5],_83[6],_83[7]];}),_])),_84=_82,_85=E(_84),_86=E(_85[1]),_87=_86[1];return [0,[0,function(_88,_){var _89=B(A(_7S,[_88,_])),_8a=_89;if(!E(E(_7x)[5])){var _8b=B(_7i(_7s,_87,_88,_)),_8c=_8b,_8d=B(A(_6C,[_6P,_8c,_6O,_7B,_])),_8e=_8d;return _88;}else{var _8f=B(A(_87,[_88,_])),_8g=_8f;return _88;}},_86[2]],_85[2]];}},_8h=function(_8i,_8j){switch(E(_8i)[0]){case 0:switch(E(_8j)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_8j)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_8j)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_8j)[0]==3?1:2;}},_8k=new T(function(){return B(unCStr("end of input"));}),_8l=new T(function(){return B(unCStr("unexpected"));}),_8m=new T(function(){return B(unCStr("expecting"));}),_8n=new T(function(){return B(unCStr("unknown parse error"));}),_8o=new T(function(){return B(unCStr("or"));}),_8p=[0,58],_8q=[0,34],_8r=[0,41],_8s=[1,_8r,_9],_8t=function(_8u,_8v,_8w){var _8x=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_8v,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_8w,_9)),_8s));})));},1)));})));}),_8y=E(_8u);return _8y[0]==0?E(_8x):[1,_8q,new T(function(){return B(_e(_8y,new T(function(){return B(unAppCStr("\" ",_8x));},1)));})];},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C[0]){return E(_8B)[0]==0?true:false;}else{var _8D=E(_8B);if(!_8D[0]){return false;}else{if(E(_8C[1])[1]!=E(_8D[1])[1]){return false;}else{_8A=_8C[2];_8B=_8D[2];continue;}}}}},_8E=function(_8F,_8G){return !B(_8z(_8F,_8G))?true:false;},_8H=[0,_8z,_8E],_8I=function(_8J,_8K,_8L){var _8M=E(_8L);if(!_8M[0]){return E(_8K);}else{return new F(function(){return _e(_8K,new T(function(){return B(_e(_8J,new T(function(){return B(_8I(_8J,_8M[1],_8M[2]));},1)));},1));});}},_8N=function(_8O){return E(_8O)[0]==0?false:true;},_8P=new T(function(){return B(unCStr(", "));}),_8Q=function(_8R){var _8S=E(_8R);if(!_8S[0]){return [0];}else{return new F(function(){return _e(_8S[1],new T(function(){return B(_8Q(_8S[2]));},1));});}},_8T=function(_8U,_8V){while(1){var _8W=(function(_8X,_8Y){var _8Z=E(_8Y);if(!_8Z[0]){return [0];}else{var _90=_8Z[1],_91=_8Z[2];if(!B(A(_8X,[_90]))){var _92=_8X;_8V=_91;_8U=_92;return null;}else{return [1,_90,new T(function(){return B(_8T(_8X,_91));})];}}})(_8U,_8V);if(_8W!=null){return _8W;}}},_93=function(_94,_95){var _96=E(_95);return _96[0]==0?[0]:[1,_94,new T(function(){return B(_93(_96[1],_96[2]));})];},_97=function(_98,_99){while(1){var _9a=E(_99);if(!_9a[0]){return E(_98);}else{_98=_9a[1];_99=_9a[2];continue;}}},_9b=function(_9c){switch(E(_9c)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_9d=function(_9e){return E(_9e)[0]==1?true:false;},_9f=function(_9g){return E(_9g)[0]==2?true:false;},_9h=[0,10],_9i=[1,_9h,_9],_9j=function(_9k){return new F(function(){return _e(_9i,_9k);});},_9l=[0,32],_9m=function(_9n){var _9o=E(_9n);switch(_9o[0]){case 0:return E(_9o[1]);case 1:return E(_9o[1]);case 2:return E(_9o[1]);default:return E(_9o[1]);}},_9p=function(_9q){return E(E(_9q)[1]);},_9r=function(_9s,_9t,_9u){while(1){var _9v=E(_9u);if(!_9v[0]){return false;}else{if(!B(A(_9p,[_9s,_9t,_9v[1]]))){_9u=_9v[2];continue;}else{return true;}}}},_9w=function(_9x,_9y){var _9z=function(_9A,_9B){while(1){var _9C=(function(_9D,_9E){var _9F=E(_9D);if(!_9F[0]){return [0];}else{var _9G=_9F[1],_9H=_9F[2];if(!B(_9r(_9x,_9G,_9E))){return [1,_9G,new T(function(){return B(_9z(_9H,[1,_9G,_9E]));})];}else{_9A=_9H;var _9I=_9E;_9B=_9I;return null;}}})(_9A,_9B);if(_9C!=null){return _9C;}}};return new F(function(){return _9z(_9y,_9);});},_9J=function(_9K,_9L,_9M,_9N,_9O,_9P){var _9Q=E(_9P);if(!_9Q[0]){return E(_9L);}else{var _9R=new T(function(){var _9S=B(_2q(_9b,_9Q));return [0,_9S[1],_9S[2]];}),_9T=new T(function(){var _9U=B(_2q(_9d,E(_9R)[2]));return [0,_9U[1],_9U[2]];}),_9V=new T(function(){return E(E(_9T)[1]);}),_9W=function(_9X,_9Y){var _9Z=E(_9Y);if(!_9Z[0]){return E(_9X);}else{var _a0=new T(function(){return B(_e(_9K,[1,_9l,new T(function(){return B(_97(_9X,_9Z));})]));}),_a1=B(_9w(_8H,B(_8T(_8N,B(_93(_9X,_9Z))))));if(!_a1[0]){return new F(function(){return _e(_9,[1,_9l,_a0]);});}else{var _a2=_a1[1],_a3=E(_a1[2]);if(!_a3[0]){return new F(function(){return _e(_a2,[1,_9l,_a0]);});}else{return new F(function(){return _e(B(_e(_a2,new T(function(){return B(_e(_8P,new T(function(){return B(_8I(_8P,_a3[1],_a3[2]));},1)));},1))),[1,_9l,_a0]);});}}}},_a4=function(_a5,_a6){var _a7=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_a6))))));if(!_a7[0]){return [0];}else{var _a8=_a7[1],_a9=_a7[2],_aa=E(_a5);return _aa[0]==0?B(_9W(_a8,_a9)):B(_e(_aa,[1,_9l,new T(function(){return B(_9W(_a8,_a9));})]));}},_ab=new T(function(){var _ac=B(_2q(_9f,E(_9T)[2]));return [0,_ac[1],_ac[2]];});return new F(function(){return _8Q(B(_3d(_9j,B(_9w(_8H,B(_8T(_8N,[1,new T(function(){if(!E(_9V)[0]){var _ad=E(E(_9R)[1]);if(!_ad[0]){var _ae=[0];}else{var _af=E(_ad[1]);switch(_af[0]){case 0:var _ag=E(_af[1]),_ah=_ag[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ag]));break;case 1:var _ai=E(_af[1]),_ah=_ai[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ai]));break;case 2:var _aj=E(_af[1]),_ah=_aj[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_aj]));break;default:var _ak=E(_af[1]),_ah=_ak[0]==0?B(_e(_9N,[1,_9l,_9O])):B(_e(_9N,[1,_9l,_ak]));}var _ae=_ah;}var _al=_ae,_am=_al;}else{var _am=[0];}return _am;}),[1,new T(function(){return B(_a4(_9N,_9V));}),[1,new T(function(){return B(_a4(_9M,E(_ab)[1]));}),[1,new T(function(){return B((function(_an){var _ao=B(_9w(_8H,B(_8T(_8N,B(_3d(_9m,_an))))));return _ao[0]==0?[0]:B(_9W(_ao[1],_ao[2]));})(E(_ab)[2]));}),_9]]]])))))));});}},_ap=[1,_9,_9],_aq=function(_ar,_as){var _at=function(_au,_av){var _aw=E(_au);if(!_aw[0]){return E(_av);}else{var _ax=_aw[1],_ay=E(_av);if(!_ay[0]){return E(_aw);}else{var _az=_ay[1];return B(A(_ar,[_ax,_az]))==2?[1,_az,new T(function(){return B(_at(_aw,_ay[2]));})]:[1,_ax,new T(function(){return B(_at(_aw[2],_ay));})];}}},_aA=function(_aB){var _aC=E(_aB);if(!_aC[0]){return [0];}else{var _aD=E(_aC[2]);return _aD[0]==0?E(_aC):[1,new T(function(){return B(_at(_aC[1],_aD[1]));}),new T(function(){return B(_aA(_aD[2]));})];}},_aE=function(_aF){while(1){var _aG=E(_aF);if(!_aG[0]){return E(new T(function(){return B(_aE(B(_aA(_9))));}));}else{if(!E(_aG[2])[0]){return E(_aG[1]);}else{_aF=B(_aA(_aG));continue;}}}},_aH=new T(function(){return B(_aI(_9));}),_aI=function(_aJ){var _aK=E(_aJ);if(!_aK[0]){return E(_ap);}else{var _aL=_aK[1],_aM=E(_aK[2]);if(!_aM[0]){return [1,_aK,_9];}else{var _aN=_aM[1],_aO=_aM[2];if(B(A(_ar,[_aL,_aN]))==2){return new F(function(){return (function(_aP,_aQ,_aR){while(1){var _aS=(function(_aT,_aU,_aV){var _aW=E(_aV);if(!_aW[0]){return [1,[1,_aT,_aU],_aH];}else{var _aX=_aW[1];if(B(A(_ar,[_aT,_aX]))==2){_aP=_aX;var _aY=[1,_aT,_aU];_aR=_aW[2];_aQ=_aY;return null;}else{return [1,[1,_aT,_aU],new T(function(){return B(_aI(_aW));})];}}})(_aP,_aQ,_aR);if(_aS!=null){return _aS;}}})(_aN,[1,_aL,_9],_aO);});}else{return new F(function(){return (function(_aZ,_b0,_b1){while(1){var _b2=(function(_b3,_b4,_b5){var _b6=E(_b5);if(!_b6[0]){return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),_aH];}else{var _b7=_b6[1],_b8=_b6[2];switch(B(A(_ar,[_b3,_b7]))){case 0:_aZ=_b7;_b0=function(_b9){return new F(function(){return A(_b4,[[1,_b3,_b9]]);});};_b1=_b8;return null;case 1:_aZ=_b7;_b0=function(_ba){return new F(function(){return A(_b4,[[1,_b3,_ba]]);});};_b1=_b8;return null;default:return [1,new T(function(){return B(A(_b4,[[1,_b3,_9]]));}),new T(function(){return B(_aI(_b6));})];}}})(_aZ,_b0,_b1);if(_b2!=null){return _b2;}}})(_aN,function(_bb){return [1,_aL,_bb];},_aO);});}}}};return new F(function(){return _aE(B(_aI(_as)));});},_bc=function(_bd,_be,_bf,_bg){return new F(function(){return _e(B(_8t(_bd,_be,_bf)),[1,_8p,new T(function(){return B(_9J(_8o,_8n,_8m,_8l,_8k,B(_aq(_8h,_bg))));})]);});},_bh=function(_bi){var _bj=E(_bi),_bk=E(_bj[1]);return new F(function(){return _bc(_bk[1],_bk[2],_bk[3],_bj[2]);});},_bl=function(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bt,_bu){return new F(function(){return _23(function(_bv,_bw){return new F(function(){return _e(B(_3l(_bm,_bn,_bo,_bp,_bq,_br,_bs,_bv)),_bw);});},_bt,_bu);});},_bx=function(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bF,_bG,_bH){return new F(function(){return _e(B(_3l(_by,_bz,_bA,_bB,_bC,_bD,_bE,_bG)),_bH);});},_bI=function(_bJ,_bK,_bL,_bM,_bN,_bO,_bP){return [0,function(_bQ,_44,_45){return new F(function(){return _bx(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_bQ,_44,_45);});},function(_45){return new F(function(){return _3l(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_45);});},function(_44,_45){return new F(function(){return _bl(_bJ,_bK,_bL,_bM,_bN,_bO,_bP,_44,_45);});}];},_bR=new T(function(){return B(unCStr(" . "));}),_bS=new T(function(){return B(unCStr(" \u2234 "));}),_bT=function(_bU){return E(E(_bU)[2]);},_bV=function(_bW,_bX,_bY,_bZ){var _c0=B(_3d(new T(function(){return B(_bT(_bW));}),B(_9w(_bX,_bY))));if(!_c0[0]){return new F(function(){return _e(_bS,new T(function(){return B(A(_bT,[_bW,_bZ]));},1));});}else{return new F(function(){return _e(B(_3a([1,_c0[1],new T(function(){return B(_3h(_bR,_c0[2]));})])),new T(function(){return B(_e(_bS,new T(function(){return B(A(_bT,[_bW,_bZ]));},1)));},1));});}},_c1=function(_c2,_c3,_c4){while(1){var _c5=E(_c3);if(!_c5[0]){return E(_c4)[0]==0?true:false;}else{var _c6=E(_c4);if(!_c6[0]){return false;}else{if(!B(A(_9p,[_c2,_c5[1],_c6[1]]))){return false;}else{_c3=_c5[2];_c4=_c6[2];continue;}}}}},_c7=function(_c8,_c9,_ca){var _cb=E(_c9),_cc=E(_ca);return !B(_c1(_c8,_cb[1],_cc[1]))?true:!B(A(_9p,[_c8,_cb[2],_cc[2]]))?true:false;},_cd=function(_ce,_cf,_cg,_ch,_ci){return !B(_c1(_ce,_cf,_ch))?false:B(A(_9p,[_ce,_cg,_ci]));},_cj=function(_ck,_cl,_cm){var _cn=E(_cl),_co=E(_cm);return new F(function(){return _cd(_ck,_cn[1],_cn[2],_co[1],_co[2]);});},_cp=function(_cq){return [0,function(_cr,_cs){return new F(function(){return _cj(_cq,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _c7(_cq,_cr,_cs);});}];},_ct=function(_cu,_cv,_cw){var _cx=E(_cv),_cy=E(_cw);return !B(_c1(_cu,_cx[1],_cy[1]))?true:!B(A(_9p,[_cu,_cx[2],_cy[2]]))?true:false;},_cz=function(_cA,_cB,_cC){var _cD=E(_cB),_cE=E(_cC);return new F(function(){return _cd(_cA,_cD[1],_cD[2],_cE[1],_cE[2]);});},_cF=function(_cG){return [0,function(_cr,_cs){return new F(function(){return _cz(_cG,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _ct(_cG,_cr,_cs);});}];},_cH=function(_cI,_cJ,_cK){var _cL=E(_cI);switch(_cL[0]){case 0:var _cM=E(_cJ);return _cM[0]==0?!B(_3x(_cL[3],_cM[3]))?[0]:[1,_cK]:[0];case 1:var _cN=E(_cJ);return _cN[0]==1?!B(_3x(_cL[3],_cN[3]))?[0]:[1,_cK]:[0];case 2:var _cO=E(_cJ);return _cO[0]==2?!B(_3x(_cL[3],_cO[3]))?[0]:[1,_cK]:[0];case 3:var _cP=E(_cJ);return _cP[0]==3?!B(_3x(_cL[3],_cP[3]))?[0]:[1,_cK]:[0];case 4:var _cQ=E(_cJ);return _cQ[0]==4?!B(_3x(_cL[3],_cQ[3]))?[0]:[1,_cK]:[0];case 5:var _cR=E(_cJ);return _cR[0]==5?!B(_3x(_cL[3],_cR[3]))?[0]:[1,_cK]:[0];case 6:var _cS=E(_cJ);return _cS[0]==6?!B(_3x(_cL[3],_cS[3]))?[0]:[1,_cK]:[0];case 7:var _cT=E(_cJ);return _cT[0]==7?!B(_3x(_cL[3],_cT[3]))?[0]:[1,_cK]:[0];case 8:var _cU=E(_cJ);return _cU[0]==8?!B(_3x(_cL[3],_cU[3]))?[0]:[1,_cK]:[0];default:var _cV=E(_cJ);return _cV[0]==9?!B(_3x(_cL[3],_cV[3]))?[0]:[1,_cK]:[0];}},_cW=new T(function(){return B(_2L("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_cX=function(_cY,_cZ,_d0){return [5,_,_cY,_cZ,_d0];},_d1=function(_d2,_d3,_d4){return [10,_,_d2,_d3,_d4];},_d5=function(_d6,_d7,_d8){return [6,_,_d6,_d7,_d8];},_d9=function(_da,_db){return [12,_,_da,_db];},_dc=function(_dd,_de){return [3,_,_dd,_de];},_df=function(_dg,_dh){return [8,_,_dg,_dh];},_di=function(_dj,_dk){return [4,_,_dj,_dk];},_dl=function(_dm,_dn,_do){while(1){var _dp=E(_do);if(!_dp[0]){return [0];}else{var _dq=E(_dp[1]),_dr=B(A(_dm,[_dn,_dq[2],_dq[3]]));if(!_dr[0]){_do=_dp[2];continue;}else{return E(_dr);}}}},_ds=function(_dt,_du){while(1){var _dv=(function(_dw,_dx){var _dy=E(_dx);switch(_dy[0]){case 2:var _dz=B(_dl(_cH,_dy[2],_dw));if(!_dz[0]){return E(_dy);}else{var _dA=_dw;_du=_dz[1];_dt=_dA;return null;}break;case 4:var _dB=_dy[3],_dC=B(_dl(_cH,_dy[2],_dw));if(!_dC[0]){return E(_dy);}else{var _dD=E(_dC[1]);switch(_dD[0]){case 3:return E(_dD[3])[0]==0?B(_dc(_dD[2],_dB)):E(_dy);case 4:if(!E(_dD[3])[0]){var _dA=_dw;_du=B(_di(_dD[2],_dB));_dt=_dA;return null;}else{return E(_dy);}break;default:return E(_dy);}}break;case 6:var _dE=_dy[3],_dF=_dy[4],_dG=B(_dl(_cH,_dy[2],_dw));if(!_dG[0]){return E(_dy);}else{var _dH=E(_dG[1]);switch(_dH[0]){case 5:if(!E(_dH[3])[0]){if(!E(_dH[4])[0]){var _dA=_dw;_du=B(_cX(_dH[2],_dE,_dF));_dt=_dA;return null;}else{return E(_dy);}}else{return E(_dy);}break;case 6:if(!E(_dH[3])[0]){if(!E(_dH[4])[0]){var _dA=_dw;_du=B(_d5(_dH[2],_dE,_dF));_dt=_dA;return null;}else{return E(_dy);}}else{return E(_dy);}break;default:return E(_dy);}}break;case 7:return [7,_,_dy[2],new T(function(){return B(_ds(_dw,_dy[3]));})];case 8:var _dI=_dy[2],_dJ=_dy[3],_dK=B(_dl(_cH,_dI,_dw));if(!_dK[0]){return [8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];}else{var _dL=E(_dK[1]);switch(_dL[0]){case 7:return E(_dL[3])[0]==0?[7,_,_dL[2],new T(function(){return B(_ds(_dw,_dJ));})]:[8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];case 8:if(!E(_dL[3])[0]){var _dA=_dw;_du=B(_df(_dL[2],_dJ));_dt=_dA;return null;}else{return [8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];}break;default:return [8,_,_dI,new T(function(){return B(_ds(_dw,_dJ));})];}}break;case 9:return [9,_,_dy[2],new T(function(){return B(_ds(_dw,_dy[3]));}),new T(function(){return B(_ds(_dw,_dy[4]));})];case 10:var _dM=_dy[2],_dN=_dy[3],_dO=_dy[4],_dP=B(_dl(_cH,_dM,_dw));if(!_dP[0]){return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}else{var _dQ=E(_dP[1]);switch(_dQ[0]){case 9:if(!E(_dQ[3])[0]){if(!E(_dQ[4])[0]){var _dA=_dw;_du=[9,_,_dQ[2],new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];_dt=_dA;return null;}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}break;case 10:if(!E(_dQ[3])[0]){if(!E(_dQ[4])[0]){var _dA=_dw;_du=B(_d1(_dQ[2],_dN,_dO));_dt=_dA;return null;}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}}else{return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}break;default:return [10,_,_dM,new T(function(){return B(_ds(_dw,_dN));}),new T(function(){return B(_ds(_dw,_dO));})];}}break;case 11:return [11,_,_dy[2],function(_dR){return new F(function(){return _ds(_dw,B(A(_dy[3],[_dR])));});}];case 12:var _dS=_dy[2],_dT=_dy[3],_dU=B(_dl(_cH,_dS,_dw));if(!_dU[0]){return [12,_,_dS,function(_dV){return new F(function(){return _ds(_dw,B(A(_dT,[_dV])));});}];}else{var _dW=E(_dU[1]);switch(_dW[0]){case 11:return [11,_,_dW[2],function(_dX){return new F(function(){return _ds(_dw,B(A(_dT,[_dX])));});}];case 12:var _dA=_dw;_du=B(_d9(_dW[2],_dT));_dt=_dA;return null;default:return [12,_,_dS,function(_dY){return new F(function(){return _ds(_dw,B(A(_dT,[_dY])));});}];}}break;default:return E(_dy);}})(_dt,_du);if(_dv!=null){return _dv;}}},_dZ=function(_e0,_e1){var _e2=E(_e1);if(!_e2[0]){var _e3=B(_dl(_cH,_e2[1],_e0));if(!_e3[0]){return E(_e2);}else{var _e4=E(_e3[1]);return _e4[0]==0?E(_cW):[1,new T(function(){return B(_3d(function(_e5){return new F(function(){return _ds(_e0,_e5);});},_e4[1]));})];}}else{return [1,new T(function(){return B(_3d(function(_e6){return new F(function(){return _ds(_e0,_e6);});},_e2[1]));})];}},_e7=function(_e8,_e9,_ea,_eb,_ec,_ed,_ee,_ef,_eg){var _eh=E(_eg);return [0,new T(function(){return B(_3d(function(_ei){return new F(function(){return _dZ(_ef,_ei);});},_eh[1]));}),new T(function(){return B(_dZ(_ef,_eh[2]));})];},_ej=function(_ek,_el,_em,_en,_eo,_ep,_eq,_er,_es){var _et=E(_es);return [0,new T(function(){return B(_3d(function(_eu){return new F(function(){return _e7(_ek,_el,_em,_en,_eo,_ep,_eq,_er,_eu);});},_et[1]));}),new T(function(){return B(_e7(_ek,_el,_em,_en,_eo,_ep,_eq,_er,_et[2]));})];},_ev=function(_ew){return E(E(_ew)[1]);},_ex=function(_ey,_ez){var _eA=E(_ez);return new F(function(){return A(_ev,[_eA[1],E(_ey)[2],_eA[2]]);});},_eB=function(_eC,_eD,_eE){var _eF=E(_eE);if(!_eF[0]){return [0];}else{var _eG=_eF[1],_eH=_eF[2];return !B(A(_eC,[_eD,_eG]))?[1,_eG,new T(function(){return B(_eB(_eC,_eD,_eH));})]:E(_eH);}},_eI=function(_eJ,_eK,_eL){while(1){var _eM=E(_eL);if(!_eM[0]){return false;}else{if(!B(A(_eJ,[_eK,_eM[1]]))){_eL=_eM[2];continue;}else{return true;}}}},_eN=function(_eO,_eP){var _eQ=function(_eR,_eS){while(1){var _eT=(function(_eU,_eV){var _eW=E(_eU);if(!_eW[0]){return [0];}else{var _eX=_eW[1],_eY=_eW[2];if(!B(_eI(_eO,_eX,_eV))){return [1,_eX,new T(function(){return B(_eQ(_eY,[1,_eX,_eV]));})];}else{_eR=_eY;var _eZ=_eV;_eS=_eZ;return null;}}})(_eR,_eS);if(_eT!=null){return _eT;}}};return new F(function(){return _eQ(_eP,_9);});},_f0=function(_f1,_f2,_f3){return new F(function(){return _e(_f2,new T(function(){return B((function(_f4,_f5){while(1){var _f6=E(_f5);if(!_f6[0]){return E(_f4);}else{var _f7=B(_eB(_f1,_f6[1],_f4));_f5=_f6[2];_f4=_f7;continue;}}})(B(_eN(_f1,_f3)),_f2));},1));});},_f8=function(_f9,_fa){while(1){var _fb=(function(_fc,_fd){var _fe=E(_fd);switch(_fe[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_fc,_fe[2]],_9];case 3:var _ff=_fc;_fa=_fe[3];_f9=_ff;return null;case 4:return new F(function(){return _f0(_ex,[1,[0,_fc,_fe[2]],_9],new T(function(){return B(_f8(_fc,_fe[3]));},1));});break;case 5:return new F(function(){return _f0(_ex,B(_f8(_fc,_fe[3])),new T(function(){return B(_f8(_fc,_fe[4]));},1));});break;default:return new F(function(){return _f0(_ex,B(_f0(_ex,[1,[0,_fc,_fe[2]],_9],new T(function(){return B(_f8(_fc,_fe[3]));},1))),new T(function(){return B(_f8(_fc,_fe[4]));},1));});}})(_f9,_fa);if(_fb!=null){return _fb;}}},_fg=function(_fh,_fi,_fj,_fk){while(1){var _fl=(function(_fm,_fn,_fo,_fp){var _fq=E(_fp);switch(_fq[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_fm,_fq[2]],_9];case 3:return new F(function(){return _f8(_fm,_fq[3]);});break;case 4:return new F(function(){return _f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_f8(_fm,_fq[3]));},1));});break;case 5:return new F(function(){return _f0(_ex,B(_f8(_fm,_fq[3])),new T(function(){return B(_f8(_fm,_fq[4]));},1));});break;case 6:return new F(function(){return _f0(_ex,B(_f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_f8(_fm,_fq[3]));},1))),new T(function(){return B(_f8(_fm,_fq[4]));},1));});break;case 7:var _fr=_fm,_fs=_fn,_ft=_fo;_fk=_fq[3];_fh=_fr;_fi=_fs;_fj=_ft;return null;case 8:return new F(function(){return _f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_fg(_fm,_fn,_fo,_fq[3]));},1));});break;case 9:return new F(function(){return _f0(_ex,B(_fg(_fm,_fn,_fo,_fq[3])),new T(function(){return B(_fg(_fm,_fn,_fo,_fq[4]));},1));});break;case 10:return new F(function(){return _f0(_ex,B(_f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_fg(_fm,_fn,_fo,_fq[3]));},1))),new T(function(){return B(_fg(_fm,_fn,_fo,_fq[4]));},1));});break;case 11:var _fr=_fm,_fs=_fn,_ft=_fo;_fk=B(A(_fq[3],[_2V]));_fh=_fr;_fi=_fs;_fj=_ft;return null;default:return new F(function(){return _f0(_ex,[1,[0,_fm,_fq[2]],_9],new T(function(){return B(_fg(_fm,_fn,_fo,B(A(_fq[3],[_2V]))));},1));});}})(_fh,_fi,_fj,_fk);if(_fl!=null){return _fl;}}},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=function(_fB){return new F(function(){return _fg(_fv,_fw,_fx,_fB);});};return new F(function(){return _e(B(_8Q(B(_3d(function(_fC){var _fD=E(_fC);if(!_fD[0]){return [1,[0,_fv,_fD[1]],_9];}else{return new F(function(){return _8Q(B(_3d(_fA,_fD[1])));});}},_fy)))),new T(function(){var _fE=E(_fz);if(!_fE[0]){var _fF=[1,[0,_fv,_fE[1]],_9];}else{var _fF=B(_8Q(B(_3d(_fA,_fE[1]))));}return _fF;},1));});},_fG=function(_fH,_fI,_fJ,_fK,_fL,_fM,_fN,_fO,_fP){var _fQ=E(_fP);return new F(function(){return _e(B(_8Q(B(_3d(function(_fR){var _fS=E(_fR);return new F(function(){return _fu(_fH,_fL,_fM,_fS[1],_fS[2]);});},_fQ[1])))),new T(function(){var _fT=E(_fQ[2]);return B(_fu(_fH,_fL,_fM,_fT[1],_fT[2]));},1));});},_fU=function(_fV,_fW,_fX,_fY,_fZ,_g0,_g1,_g2,_g3,_g4,_g5){return [0,_fV,_fW,_fX,_fY,function(_eu){return new F(function(){return _fG(_fV,_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_eu);});},function(_g6,_eu){return new F(function(){return _ej(_fZ,_g0,_g1,_g2,_g3,_g4,_g5,_g6,_eu);});}];},_g7=function(_g8){return E(E(_g8)[2]);},_g9=function(_ga){return E(E(_ga)[1]);},_gb=[0,_g9,_g7],_gc=[0,125],_gd=new T(function(){return B(unCStr("given = "));}),_ge=new T(function(){return B(unCStr(", "));}),_gf=new T(function(){return B(unCStr("needed = "));}),_gg=new T(function(){return B(unCStr("AbsRule {"));}),_gh=[0,0],_gi=function(_gj){return E(E(_gj)[3]);},_gk=function(_gl){return E(E(_gl)[1]);},_gm=function(_gn,_go,_gp,_gq){var _gr=function(_gs){return new F(function(){return _e(_gg,new T(function(){return B(_e(_gf,new T(function(){return B(A(new T(function(){return B(A(_gi,[_gn,_gp]));}),[new T(function(){return B(_e(_ge,new T(function(){return B(_e(_gd,new T(function(){return B(A(new T(function(){return B(A(_gk,[_gn,_gh,_gq]));}),[[1,_gc,_gs]]));},1)));},1)));})]));},1)));},1));});};return _go<11?E(_gr):function(_gt){return [1,_E,new T(function(){return B(_gr([1,_D,_gt]));})];};},_gu=function(_gv,_gw){var _gx=E(_gw);return new F(function(){return A(_gm,[_gv,0,_gx[1],_gx[2],_9]);});},_gy=function(_gz,_gA,_gB){return new F(function(){return _23(function(_gC){var _gD=E(_gC);return new F(function(){return _gm(_gz,0,_gD[1],_gD[2]);});},_gA,_gB);});},_gE=function(_gF,_gG,_gH){var _gI=E(_gH);return new F(function(){return _gm(_gF,E(_gG)[1],_gI[1],_gI[2]);});},_gJ=function(_gK){return [0,function(_cr,_cs){return new F(function(){return _gE(_gK,_cr,_cs);});},function(_cs){return new F(function(){return _gu(_gK,_cs);});},function(_cr,_cs){return new F(function(){return _gy(_gK,_cr,_cs);});}];},_gL=new T(function(){return B(unCStr("Sequent "));}),_gM=[0,11],_gN=[0,32],_gO=function(_gP,_gQ,_gR,_gS){var _gT=new T(function(){return B(A(_gk,[_gP,_gM,_gS]));}),_gU=new T(function(){return B(A(_gi,[_gP,_gR]));});return _gQ<11?function(_gV){return new F(function(){return _e(_gL,new T(function(){return B(A(_gU,[[1,_gN,new T(function(){return B(A(_gT,[_gV]));})]]));},1));});}:function(_gW){return [1,_E,new T(function(){return B(_e(_gL,new T(function(){return B(A(_gU,[[1,_gN,new T(function(){return B(A(_gT,[[1,_D,_gW]]));})]]));},1)));})];};},_gX=function(_gY,_gZ){var _h0=E(_gZ);return new F(function(){return A(_gO,[_gY,0,_h0[1],_h0[2],_9]);});},_h1=function(_h2,_h3,_h4){return new F(function(){return _23(function(_h5){var _h6=E(_h5);return new F(function(){return _gO(_h2,0,_h6[1],_h6[2]);});},_h3,_h4);});},_h7=function(_h8,_h9,_ha){var _hb=E(_ha);return new F(function(){return _gO(_h8,E(_h9)[1],_hb[1],_hb[2]);});},_hc=function(_hd){return [0,function(_cr,_cs){return new F(function(){return _h7(_hd,_cr,_cs);});},function(_cs){return new F(function(){return _gX(_hd,_cs);});},function(_cr,_cs){return new F(function(){return _h1(_hd,_cr,_cs);});}];},_he=function(_hf,_hg){return new F(function(){return _e(B(_1r(_hf)),_hg);});},_hh=function(_hi,_hj){return new F(function(){return _23(_he,_hi,_hj);});},_hk=function(_hl,_hm,_hn){return new F(function(){return _e(B(_1r(_hm)),_hn);});},_ho=[0,_hk,_1r,_hh],_hp=function(_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_hB){var _hC=E(_hB);return new F(function(){return _fu(_hq,_hx,_hy,_hC[1],_hC[2]);});},_hD=function(_hE,_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN,_hO){return [0,_hE,_hF,_hG,_hH,function(_eu){return new F(function(){return _hp(_hE,_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_eu);});},function(_g6,_eu){return new F(function(){return _e7(_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_g6,_eu);});}];},_hP=function(_hQ,_hR){return [0];},_hS=function(_hT,_hU,_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4,_i5,_i6){return [0,_hT,_hU,_hP,_1];},_i7=function(_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_ii,_ij){var _ik=E(_ij);if(!_ik[0]){return [1,[0,_i8,_ik[1]],_9];}else{return new F(function(){return _8Q(B(_3d(function(_il){return new F(function(){return _fg(_i8,_if,_ig,_il);});},_ik[1])));});}},_im=function(_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv,_iw,_ix){return [0,_in,_io,_ip,_iq,function(_eu){return new F(function(){return _i7(_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv,_iw,_ix,_eu);});},_dZ];},_iy=function(_iz){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_iz));}))));});},_iA=new T(function(){return B(_iy("w_sz9V{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r156}\n                  sv{tv ayNY} [tv] quant{tv ayNW} [tv]"));}),_iB=new T(function(){return B(_iy("w_sz9U{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv ayNW} [tv]"));}),_iC=new T(function(){return B(_iy("w_sz9T{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv ayNV} [tv]"));}),_iD=new T(function(){return B(_iy("w_sz9S{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv ayNY} [tv]"));}),_iE=new T(function(){return B(_iy("w_sz9R{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv ayNU} [tv]"));}),_iF=new T(function(){return B(_iy("w_sz9Q{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv ayNX} [tv]"));}),_iG=new T(function(){return B(_iy("w_sz9W{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14g}\n                  sv{tv ayNY} [tv]"));}),_iH=new T(function(){return B(_iy("w_sz9P{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayNW} [tv]"));}),_iI=new T(function(){return B(_iy("w_sz9O{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv ayNV} [tv]"));}),_iJ=new T(function(){return B(_iy("w_sz9N{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv ayNY} [tv]"));}),_iK=new T(function(){return B(_iy("w_sz9M{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv ayNU} [tv]"));}),_iL=new T(function(){return B(_iy("w_sz9L{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayNX} [tv]"));}),_iM=function(_iN,_iO){return function(_iP,_iQ){var _iR=E(_iP);return _iR[0]==0?[1,[0,new T(function(){return B(_iS(_iN,_iO,_iL,_iK,_iJ,_iI,_iH,_iF,_iE,_iD,_iC,_iB,_iA,_iG));}),_iR[1],_iQ]]:[0];};},_iT=function(_iU){return [0,E(_iU)];},_iS=function(_iV,_iW,_iX,_iY,_iZ,_j0,_j1,_j2,_j3,_j4,_j5,_j6,_j7,_j8){return [0,_iV,_iW,new T(function(){return B(_iM(_iV,_iW));}),_iT];},_j9=[1,_9],_ja=function(_jb,_jc){while(1){var _jd=E(_jb);if(!_jd[0]){return E(_jc);}else{_jb=_jd[2];var _je=_jc+1|0;_jc=_je;continue;}}},_jf=[0,95],_jg=[1,_jf,_9],_jh=[1,_jg,_9],_ji=function(_jj,_jk,_jl){return !B(_3x(B(A(_jj,[_jk,_jh])),B(A(_jj,[_jl,_jh]))))?true:false;},_jm=function(_jn){return [0,function(_jo,_jp){return new F(function(){return _3x(B(A(_jn,[_jo,_jh])),B(A(_jn,[_jp,_jh])));});},function(_44,_45){return new F(function(){return _ji(_jn,_44,_45);});}];},_jq=function(_jr,_js){return new F(function(){return _ds(_jr,_js);});},_jt=function(_ju,_jv,_jw,_jx,_jy,_jz,_jA,_jB,_jC,_jD,_jE){return [0,_ju,_jv,_jw,_jx,function(_jF){return new F(function(){return _fg(_ju,_jB,_jC,_jF);});},_jq];},_jG=new T(function(){return B(_iy("w_soRr{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r156}\n                  sv{tv alOC} [tv] quant{tv alOA} [tv]"));}),_jH=new T(function(){return B(_iy("w_soRq{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv alOA} [tv]"));}),_jI=new T(function(){return B(_iy("w_soRp{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv alOz} [tv]"));}),_jJ=new T(function(){return B(_iy("w_soRo{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv alOC} [tv]"));}),_jK=new T(function(){return B(_iy("w_soRn{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv alOy} [tv]"));}),_jL=new T(function(){return B(_iy("w_soRm{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv alOB} [tv]"));}),_jM=new T(function(){return B(_iy("w_soRs{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r14g}\n                  sv{tv alOC} [tv]"));}),_jN=new T(function(){return B(_iy("w_soRl{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv alOA} [tv]"));}),_jO=new T(function(){return B(_iy("w_soRk{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv alOz} [tv]"));}),_jP=new T(function(){return B(_iy("w_soRj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv alOC} [tv]"));}),_jQ=new T(function(){return B(_iy("w_soRi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv alOy} [tv]"));}),_jR=new T(function(){return B(_iy("w_soRh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv alOB} [tv]"));}),_jS=function(_jT,_jU,_jV,_jW){var _jX=E(_jV);switch(_jX[0]){case 2:return [1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_jX[2],_jW]];case 4:var _jZ=_jX[2];if(!E(_jX[3])[0]){var _k0=E(_jW);switch(_k0[0]){case 3:return E(_k0[3])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_jZ,_k0]]:[0];case 4:return E(_k0[3])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_jZ,_k0]]:[0];default:return [0];}}else{return [0];}break;case 6:var _k1=_jX[2];if(!E(_jX[3])[0]){if(!E(_jX[4])[0]){var _k2=E(_jW);switch(_k2[0]){case 5:return E(_k2[3])[0]==0?E(_k2[4])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_k1,_k2]]:[0]:[0];case 6:return E(_k2[3])[0]==0?E(_k2[4])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_k1,_k2]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _k3=_jX[2];if(!E(_jX[3])[0]){var _k4=E(_jW);switch(_k4[0]){case 7:return E(_k4[3])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_k3,_k4]]:[0];case 8:return E(_k4[3])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_k3,_k4]]:[0];default:return [0];}}else{return [0];}break;case 10:var _k5=_jX[2];if(!E(_jX[3])[0]){if(!E(_jX[4])[0]){var _k6=E(_jW);switch(_k6[0]){case 9:return E(_k6[3])[0]==0?E(_k6[4])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_k5,_k6]]:[0]:[0];case 10:return E(_k6[3])[0]==0?E(_k6[4])[0]==0?[1,[0,new T(function(){return B(_jY(_jT,_jU,_jR,_jQ,_jP,_jO,_jN,_jL,_jK,_jJ,_jI,_jH,_jG,_jM));}),_k5,_k6]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_k7=new T(function(){return B(_2L("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_k8=function(_k9){var _ka=E(_k9);switch(_ka[0]){case 3:return [2,_,_ka];case 4:return [4,_,_ka,_V];case 5:return [6,_,_ka,_V,_V];case 6:return [8,_,_ka,_S];case 7:return [10,_,_ka,_S,_S];default:return E(_k7);}},_jY=function(_kb,_kc,_kd,_ke,_kf,_kg,_kh,_ki,_kj,_kk,_kl,_km,_kn,_ko){return [0,_kb,_kc,function(_kp,_kq){return new F(function(){return _jS(_kb,_kc,_kp,_kq);});},_k8];},_kr=function(_ks,_kt,_ku){return new F(function(){return _23(function(_kv,_kw){return new F(function(){return _e(B(A(_ks,[_kv,_jh])),_kw);});},_kt,_ku);});},_kx=function(_ky){return [0,function(_kz,_kA,_kB){return new F(function(){return _e(B(A(_ky,[_kA,_jh])),_kB);});},function(_kC){return new F(function(){return A(_ky,[_kC,_jh]);});},function(_44,_45){return new F(function(){return _kr(_ky,_44,_45);});}];},_kD=[1,_9],_kE=function(_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_kP,_kQ){var _kR=E(_kP);if(_kR[0]==2){return E(_kD);}else{var _kS=E(_kQ);if(_kS[0]==2){return E(_kD);}else{var _kT=function(_kU){var _kV=function(_kW){var _kX=function(_kY){var _kZ=function(_l0){var _l1=function(_l2){var _l3=function(_l4){var _l5=function(_l6){var _l7=function(_l8){var _l9=function(_la){var _lb=function(_lc){var _ld=function(_le){var _lf=function(_lg){var _lh=E(_kR);switch(_lh[0]){case 1:var _li=E(_kS);return _li[0]==1?!B(A(_kG,[_lh[2],_li[2]]))?[0]:E(_kD):[0];case 3:var _lj=E(_kS);return _lj[0]==3?!B(A(_kF,[_lh[2],_lj[2]]))?[0]:E(_kD):[0];case 4:var _lk=_lh[2],_ll=E(_kS);switch(_ll[0]){case 3:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[4,_,_lk,_V],[3,_,_ll[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[4,_,_lk,_V],[4,_,_ll[2],_V]]));}),_9]];default:return [0];}break;case 5:var _ln=E(_kS);return _ln[0]==5?!B(A(_kF,[_lh[2],_ln[2]]))?[0]:E(_kD):[0];case 6:var _lo=_lh[2],_lp=E(_kS);switch(_lp[0]){case 5:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[6,_,_lo,_V,_V],[5,_,_lp[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[6,_,_lo,_V,_V],[6,_,_lp[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _lq=E(_kS);return _lq[0]==7?!B(A(_kH,[_lh[2],_lq[2]]))?[0]:[1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lh[3],_lq[3]]));}),_9]]:[0];case 8:var _lr=_lh[2],_ls=_lh[3],_lt=E(_kS);switch(_lt[0]){case 7:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[8,_,_lr,_S],[7,_,_lt[2],_S]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_ls,_lt[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[8,_,_lr,_S],[8,_,_lt[2],_S]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_ls,_lt[3]]));}),_9]]];default:return [0];}break;case 9:var _lu=E(_kS);return _lu[0]==9?!B(A(_kH,[_lh[2],_lu[2]]))?[0]:[1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lh[3],_lu[3]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lh[4],_lu[4]]));}),_9]]]:[0];case 10:var _lv=_lh[2],_lw=_lh[3],_lx=_lh[4],_ly=function(_lz){var _lA=E(_kS);switch(_lA[0]){case 9:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[10,_,_lv,_S,_S],[9,_,_lA[2],_S,_S]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lw,_lA[3]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lx,_lA[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,[10,_,_lv,_S,_S],[10,_,_lA[2],_S,_S]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lw,_lA[3]]));}),[1,new T(function(){return B(A(_lm,[_kF,_kG,_kH,_kI,_kJ,_kK,_kL,_kM,_kN,_kO,_lx,_lA[4]]));}),_9]]]];default:return [0];}};return E(_lw)[0]==0?E(_lx)[0]==0?E(_kD):B(_ly(_)):B(_ly(_));default:return [0];}},_lB=E(_kS);return _lB[0]==10?E(_lB[3])[0]==0?E(_lB[4])[0]==0?E(_kD):B(_lf(_)):B(_lf(_)):B(_lf(_));},_lC=E(_kR);return _lC[0]==8?E(_lC[3])[0]==0?E(_kD):B(_ld(_)):B(_ld(_));},_lD=E(_kS);switch(_lD[0]){case 6:return E(_lD[3])[0]==0?E(_lD[4])[0]==0?E(_kD):B(_lb(_)):B(_lb(_));case 8:return E(_lD[3])[0]==0?E(_kD):B(_lb(_));default:return new F(function(){return _lb(_);});}},_lE=E(_kR);return _lE[0]==6?E(_lE[3])[0]==0?E(_lE[4])[0]==0?E(_kD):B(_l9(_)):B(_l9(_)):B(_l9(_));},_lF=E(_kS);return _lF[0]==4?E(_lF[3])[0]==0?E(_kD):B(_l7(_)):B(_l7(_));},_lG=E(_kR);switch(_lG[0]){case 4:return E(_lG[3])[0]==0?E(_kD):B(_l5(_));case 9:return E(_lG[3])[0]==0?E(_lG[4])[0]==0?E(_kD):B(_l5(_)):B(_l5(_));default:return new F(function(){return _l5(_);});}},_lH=E(_kS);return _lH[0]==9?E(_lH[3])[0]==0?E(_lH[4])[0]==0?E(_kD):B(_l3(_)):B(_l3(_)):B(_l3(_));},_lI=E(_kR);return _lI[0]==7?E(_lI[3])[0]==0?E(_kD):B(_l1(_)):B(_l1(_));},_lJ=E(_kS);switch(_lJ[0]){case 5:return E(_lJ[3])[0]==0?E(_lJ[4])[0]==0?E(_kD):B(_kZ(_)):B(_kZ(_));case 7:return E(_lJ[3])[0]==0?E(_kD):B(_kZ(_));default:return new F(function(){return _kZ(_);});}},_lK=E(_kR);return _lK[0]==5?E(_lK[3])[0]==0?E(_lK[4])[0]==0?E(_kD):B(_kX(_)):B(_kX(_)):B(_kX(_));},_lL=E(_kS);return _lL[0]==3?E(_lL[3])[0]==0?E(_kD):B(_kV(_)):B(_kV(_));},_lM=E(_kR);return _lM[0]==3?E(_lM[3])[0]==0?E(_kD):B(_kT(_)):B(_kT(_));}}},_lN=function(_lO,_lP,_lQ){return [0,_lO,_lP,_lQ];},_lR=new T(function(){return B(_iy("w_soRA{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv alNX} [tv]"));}),_lS=new T(function(){return B(_iy("w_soRw{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv alNY} [tv]"));}),_lT=function(_lU){return [0,function(_lV,_lW){return B(A(_lU,[_lV,_lW,_1]))[0]==0?false:true;},function(_lX,_lY){return B(A(_lU,[_lX,_lY,_1]))[0]==0?true:false;}];},_lZ=new T(function(){return B(_lT(_cH));}),_lm=function(_m0,_m1,_m2,_m3,_m4,_m5,_m6,_m7,_m8,_m9){var _ma=function(_mb,_mc){return new F(function(){return _2W(_m4,_m6,_m7,_m5,_m3,_m8,_m9,_mb);});};return function(_md,_me){return new F(function(){return _lN(new T(function(){return B(_jY(function(_mf,_mg){return new F(function(){return _kE(_m0,_m1,_m2,_m3,_m4,_m5,_m6,_m7,_m8,_m9,_mf,_mg);});},new T(function(){return B(_jt(_lZ,_ho,new T(function(){return B(_jm(_ma));}),new T(function(){return B(_kx(_ma));}),_m4,_m6,_m7,_m3,_m5,_m8,_m9));}),_lS,_m0,_m1,_m2,_lR,_m3,_m4,_m5,_m6,_m7,_m8,_m9));}),_md,_me);});};},_mh=function(_mi,_mj,_mk){var _ml=E(_mj);if(!_ml[0]){return [0];}else{var _mm=E(_mk);return _mm[0]==0?[0]:[1,new T(function(){return B(A(_mi,[_ml[1],_mm[1]]));}),new T(function(){return B(_mh(_mi,_ml[2],_mm[2]));})];}},_mn=function(_mo,_mp,_mq,_mr,_ms,_mt,_mu,_mv,_mw,_mx,_my,_mz){var _mA=E(_my);if(!_mA[0]){return E(_j9);}else{var _mB=_mA[1],_mC=E(_mz);if(!_mC[0]){return E(_j9);}else{var _mD=_mC[1];return B(_ja(_mB,0))!=B(_ja(_mD,0))?[0]:[1,new T(function(){return B(_mh(new T(function(){return B(_lm(_mo,_mp,_mq,_mr,_ms,_mt,_mu,_mv,_mw,_mx));}),_mB,_mD));})];}}},_mE=new T(function(){return B(_iy("w_szaG{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayNE} [tv]"));}),_mF=new T(function(){return B(_iy("w_szaK{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayND} [tv]"));}),_mG=new T(function(){return B(_lT(_cH));}),_mH=function(_mI,_mJ,_mK,_mL,_mM,_mN,_mO,_mP,_mQ,_mR){var _mS=new T(function(){return B(_iS(function(_mT,_mU){return new F(function(){return _mn(_mI,_mJ,_mK,_mL,_mM,_mN,_mO,_mP,_mQ,_mR,_mT,_mU);});},new T(function(){return B(_im(_mG,_ho,new T(function(){return B(_3W(_mM,_mO,_mP,_mL,_mN,_mQ,_mR));}),new T(function(){return B(_bI(_mM,_mO,_mP,_mL,_mN,_mQ,_mR));}),_mM,_mO,_mP,_mL,_mN,_mQ,_mR));}),_mE,_mI,_mJ,_mK,_mF,_mL,_mM,_mN,_mO,_mP,_mQ,_mR));});return function(_mV,_mW){var _mX=E(_mV),_mY=_mX[1],_mZ=E(_mW),_n0=_mZ[1];return B(_ja(_mY,0))!=B(_ja(_n0,0))?[0]:[1,[1,[0,_mS,_mX[2],_mZ[2]],new T(function(){return B(_mh(function(_g6,_eu){return [0,_mS,_g6,_eu];},_mY,_n0));})]];};},_n1=new T(function(){return B(_iy("w_szdi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ayNb} [tv]"));}),_n2=new T(function(){return B(_iy("w_szdm{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ayNa} [tv]"));}),_n3=function(_n4,_n5,_n6,_n7,_n8,_n9,_na,_nb,_nc,_nd){var _ne=new T(function(){return B(_hS(new T(function(){return B(_mH(_n4,_n5,_n6,_n7,_n8,_n9,_na,_nb,_nc,_nd));}),new T(function(){return B(_hD(_mG,_ho,new T(function(){return B(_cF(new T(function(){return B(_3W(_n8,_na,_nb,_n7,_n9,_nc,_nd));})));}),new T(function(){return B(_hc(new T(function(){return B(_bI(_n8,_na,_nb,_n7,_n9,_nc,_nd));})));}),_n8,_na,_nb,_n7,_n9,_nc,_nd));}),_n1,_n4,_n5,_n6,_n2,_n7,_n8,_n9,_na,_nb,_nc,_nd));});return function(_nf,_ng){var _nh=E(_nf),_ni=_nh[1],_nj=E(_ng),_nk=_nj[1];return B(_ja(_ni,0))!=B(_ja(_nk,0))?[0]:[1,[1,[0,_ne,_nh[2],_nj[2]],new T(function(){return B(_mh(function(_g6,_eu){return [0,_ne,_g6,_eu];},_ni,_nk));})]];};},_nl=function(_nm,_nn){while(1){var _no=E(_nn);if(!_no[0]){return false;}else{var _np=E(_no[1]);if(!B(A(_ev,[_np[1],_nm,_np[2]]))){_nn=_no[2];continue;}else{return true;}}}},_nq=[1,_9],_nr=function(_ns,_nt,_nu,_nv,_nw,_nx,_ny,_nz,_nA,_nB,_nC){var _nD=E(_nv);return !B(A(_nD[1],[new T(function(){return B(A(_nA,[_nB]));}),_nC]))?!B(_nl(_nB,B(A(_nx,[_nC]))))?[1,[1,[0,[0,_ns,[0,_nt,_nu,_nD,_nw,_nx,_ny],_nz,_nA],_nB,_nC],_9]]:[0,[1,_,[0,_ns,[0,_nt,_nu,_nD,_nw,_nx,_ny],_nz,_nA],[3,_nu,_nw,_nB,_nC]]]:E(_nq);},_nE=function(_nF){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(55,15)-(57,42)|case");});},_nG=new T(function(){return B(_nE(_));}),_nH=new T(function(){return B(unCStr(": empty list"));}),_nI=new T(function(){return B(unCStr("Prelude."));}),_nJ=function(_nK){return new F(function(){return err(B(_e(_nI,new T(function(){return B(_e(_nK,_nH));},1))));});},_nL=new T(function(){return B(unCStr("head"));}),_nM=new T(function(){return B(_nJ(_nL));}),_nN=function(_nO){return E(E(_nO)[2]);},_nP=function(_nQ,_nR){while(1){var _nS=E(_nQ);if(!_nS){return E(_nR);}else{var _nT=E(_nR);if(!_nT[0]){return [0];}else{_nQ=_nS-1|0;_nR=_nT[2];continue;}}}},_nU=function(_nV,_nW){var _nX=E(_nV)[1];return _nX>=0?B(_nP(_nX,_nW)):E(_nW);},_nY=function(_nZ){return new F(function(){return _2L("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:97:31-64|function conc");});},_o0=new T(function(){return B(_nY(_));}),_o1=function(_o2){var _o3=E(_o2);switch(_o3[0]){case 3:return [2,_,_o3];case 4:return [4,_,_o3,_V];case 5:return [6,_,_o3,_V,_V];case 6:return [8,_,_o3,_S];case 7:return [10,_,_o3,_S,_S];default:return E(_k7);}},_o4=function(_o5){var _o6=E(_o5);if(!_o6[0]){return [0];}else{var _o7=E(_o6[1]);if(!_o7[0]){return [0];}else{return new F(function(){return _e(_o7[1],new T(function(){return B(_o4(_o6[2]));},1));});}}},_o8=function(_o9){var _oa=E(_o9);return [0,[1,[1,new T(function(){return B(_o4(_oa[1]));})],_9],_oa[2]];},_ob=function(_oc,_od,_oe){return !B(_9r(_oc,_od,_oe))?E(_oe):[1,_od,new T(function(){return B(_8T(function(_of){return !B(A(_9p,[_oc,_of,_od]))?true:false;},_oe));})];},_og=function(_oh,_oi,_oj,_ok,_ol,_om,_on){return function(_oo,_op){var _oq=E(_oo);if(!_oq[0]){return new F(function(){return _o8(_op);});}else{var _or=E(_op);return [0,[1,[1,new T(function(){return B(_ob(new T(function(){return B(_jm(function(_os,_ot){return new F(function(){return _2W(_on,_om,_ol,_oj,_ok,_oh,_oi,_os);});}));}),_oq[1],B(_o4(_or[1]))));})],_9],_or[2]];}};},_ou=new T(function(){return B(_lT(_cH));}),_ov=function(_ow){return E(E(_ow)[1]);},_ox=function(_oy,_oz){var _oA=E(_oy);if(!_oA){return [0];}else{var _oB=E(_oz);return _oB[0]==0?[0]:[1,_oB[1],new T(function(){return B(_ox(_oA-1|0,_oB[2]));})];}},_oC=function(_oD,_oE){return _oD<0?[0]:B(_ox(_oD,_oE));},_oF=function(_oG,_oH){var _oI=E(_oG)[1];return _oI>0?B(_oC(_oI,_oH)):[0];},_oJ=function(_oK,_oL){return [1,_,_oK,_oL];},_oM=function(_oN){return E(E(_oN)[2]);},_oO=function(_oP){return E(E(_oP)[4]);},_oQ=function(_oR,_oS,_oT){var _oU=E(_oR),_oV=E(_oU[2]);return new F(function(){return _nr(_oU[1],_oV[1],_oV[2],_oV[3],_oV[4],_oV[5],_oV[6],_oU[3],_oU[4],_oS,_oT);});},_oW=function(_oX,_oY,_oZ,_p0,_p1,_p2){var _p3=B(A(_oZ,[_p1,_p2]));if(!_p3[0]){var _p4=B(A(_oZ,[_p2,_p1]));if(!_p4[0]){var _p5=B(A(_oX,[_p1,_p2]));if(!_p5[0]){return [0,[0,new T(function(){return B(_oO(_oY));}),_p1,_p2]];}else{var _p6=B(_p7([0,_oX,_oY,_oZ,_p0],_p5[1]));return _p6[0]==0?[0,[2,new T(function(){return B(_oO(_oY));}),_p6[1],_p1,_p2]]:E(_p6);}}else{var _p8=E(_p4[1]);return new F(function(){return _oQ(_p8[1],_p8[2],_p8[3]);});}}else{var _p9=E(_p3[1]);return new F(function(){return _oQ(_p9[1],_p9[2],_p9[3]);});}},_pa=function(_pb){return E(E(_pb)[6]);},_p7=function(_pc,_pd){var _pe=E(_pd);if(!_pe[0]){return E(_nq);}else{var _pf=E(_pe[1]),_pg=E(_pf[1]),_ph=B(_oW(_pg[1],_pg[2],_pg[3],_pg[4],_pf[2],_pf[3]));if(!_ph[0]){return [0,[1,_,_pg,_ph[1]]];}else{var _pi=_ph[1],_pj=B(_p7(_pc,B(_3d(function(_pk){var _pl=E(_pk),_pm=_pl[1];return [0,_pm,new T(function(){return B(A(_pa,[B(_oM(_pm)),_pi,_pl[2]]));}),new T(function(){return B(A(_pa,[B(_oM(_pm)),_pi,_pl[3]]));})];},_pe[2]))));if(!_pj[0]){return [0,new T(function(){return B(_oJ(_pc,_pj[1]));})];}else{var _pn=_pj[1];return [1,new T(function(){var _po=function(_pp){var _pq=E(_pp);return _pq[0]==0?E(_pn):[1,new T(function(){var _pr=E(_pq[1]),_ps=_pr[1];return [0,_ps,_pr[2],new T(function(){return B(A(_pa,[B(_oM(_ps)),_pn,_pr[3]]));})];}),new T(function(){return B(_po(_pq[2]));})];};return B(_po(_pi));})];}}}},_pt=function(_pu,_pv,_pw,_px,_py,_pz,_pA,_pB,_pC,_pD,_pE,_pF){var _pG=new T(function(){return B(_nN(_pF));}),_pH=function(_pI,_pJ){return new F(function(){return _2W(_pA,_pz,_py,_pw,_px,_pu,_pv,_pI);});},_pK=new T(function(){return B(_jt(_ou,_ho,new T(function(){return B(_jm(_pH));}),new T(function(){return B(_kx(_pH));}),_pA,_pz,_py,_px,_pw,_pu,_pv));}),_pL=function(_pM,_pN){return new F(function(){return _kE(_pE,_pC,_pD,_px,_pA,_pw,_pz,_py,_pu,_pv,_pM,_pN);});};return function(_pO,_pP,_pQ){var _pR=new T(function(){return B(A(_pB,[_pQ]));});return [0,new T(function(){return B(_mh(function(_pS,_pT){var _pU=B(A(new T(function(){return B(_og(_pu,_pv,_pw,_px,_py,_pz,_pA));}),[new T(function(){var _pV=E(E(_pT)[1]);if(!_pV[0]){var _pW=[0];}else{var _pX=E(_pV[1]),_pW=_pX[0]==0?[0]:[1,new T(function(){var _pY=E(_pX[1]);return _pY[0]==0?E(_nM):B(_ds(new T(function(){var _pZ=E(B(A(_pG,[_pO]))[2]);if(!_pZ[0]){var _q0=E(_o0);}else{var _q1=E(_pZ[1]);if(!_q1[0]){var _q2=E(_o0);}else{var _q3=_q1[1];if(!E(_q1[2])[0]){var _q4=B(_jS(_pL,_pK,_q3,_pR));if(!_q4[0]){var _q5=B(_jS(_pL,_pK,_pR,_q3));if(!_q5[0]){var _q6=B(_pL(_q3,_pR));if(!_q6[0]){var _q7=[0];}else{var _q8=B(_p7([0,_pL,_pK,function(_q9,_qa){return new F(function(){return _jS(_pL,_pK,_q9,_qa);});},_o1],_q6[1])),_q7=_q8[0]==0?[0]:E(_q8[1]);}var _qb=_q7;}else{var _qc=E(_q5[1]),_qd=E(_qc[1]),_qe=E(_qd[2]),_qf=B(_nr(_qd[1],_qe[1],_qe[2],_qe[3],_qe[4],_qe[5],_qe[6],_qd[3],_qd[4],_qc[2],_qc[3])),_qb=_qf[0]==0?[0]:E(_qf[1]);}var _qg=_qb;}else{var _qh=E(_q4[1]),_qi=E(_qh[1]),_qj=E(_qi[2]),_qk=B(_nr(_qi[1],_qj[1],_qj[2],_qj[3],_qj[4],_qj[5],_qj[6],_qi[3],_qi[4],_qh[2],_qh[3])),_qg=_qk[0]==0?[0]:E(_qk[1]);}var _ql=_qg;}else{var _ql=E(_o0);}var _q2=_ql;}var _q0=_q2;}var _qm=_q0;return _qm;}),_pY[1]));})];}var _qn=_pW;return _qn;}),_pS])),_qo=_pU[2],_qp=E(E(_pT)[1]);if(!_qp[0]){return E(_nG);}else{var _qq=E(_qp[1]);if(!_qq[0]){return E(_qp[2])[0]==0?E(_pU):E(_nG);}else{var _qr=E(_pU[1]);if(!_qr[0]){return [0,_9,_qo];}else{var _qs=E(_qr[1]);if(!_qs[0]){return E(_pU);}else{var _qt=_qs[1],_qu=new T(function(){return [0,B(_ja(_qq[1],0))];});return [0,[1,[1,new T(function(){return B(_oF(_qu,_qt));})],[1,[1,new T(function(){return B(_nU(_qu,_qt));})],_qr[2]]],_qo];}}}}},_pP,new T(function(){return B(A(new T(function(){return B(_ov(_pF));}),[_pO]));},1)));}),[0,new T(function(){return E(B(A(_pG,[_pO]))[1]);}),[1,[1,_pR,_9]]]];};},_qv=function(_qw){var _qx=E(_qw);return _qx[0]==0?E(_qx[1]):E(_1);},_qy=function(_qz,_qA){return [0];},_qB=function(_qC){while(1){var _qD=(function(_qE){var _qF=E(_qE);if(!_qF[0]){return [0];}else{var _qG=_qF[2],_qH=E(_qF[1]);if(!_qH[0]){_qC=_qG;return null;}else{return [1,_qH[1],new T(function(){return B(_qB(_qG));})];}}})(_qC);if(_qD!=null){return _qD;}}},_qI=function(_qJ,_qK,_qL,_qM,_qN,_qO,_qP,_qQ,_qR,_qS,_qT){var _qU=new T(function(){return B(_pt(_qJ,_qK,_qL,_qM,_qN,_qO,_qP,_qQ,_qR,_qS,_qT,_gb));}),_qV=new T(function(){return B(_n3(_qT,_qR,_qS,_qM,_qP,_qL,_qO,_qN,_qJ,_qK));}),_qW=new T(function(){return B(_gJ(new T(function(){return B(_hc(new T(function(){return B(_bI(_qP,_qO,_qN,_qM,_qL,_qJ,_qK));})));})));}),_qX=[0,_qV,new T(function(){return B(_fU(_ou,_ho,new T(function(){return B(_cp(new T(function(){return B(_cF(new T(function(){return B(_3W(_qP,_qO,_qN,_qM,_qL,_qJ,_qK));})));})));}),_qW,_qP,_qO,_qN,_qM,_qL,_qJ,_qK));}),_qy,_1];return function(_qY,_qZ,_r0){var _r1=B(_3d(function(_r2){var _r3=new T(function(){return B(A(_qU,[_r2,_qZ,_r0]));}),_r4=B(A(_qV,[_r3,_r2]));if(!_r4[0]){return [0,[0,_qW,_r3,_r2]];}else{var _r5=B(_p7(_qX,_r4[1]));return _r5[0]==0?[0,[2,_qW,_r5[1],_r3,_r2]]:[1,_r2];}},E(_qY)[1])),_r6=B(_qB(_r1));if(!_r6[0]){return [0,new T(function(){return B(_3d(_qv,_r1));})];}else{var _r7=_r6[1],_r8=new T(function(){return B(A(_qU,[_r7,_qZ,_r0]));}),_r9=B(A(_qV,[_r7,_r8]));if(!_r9[0]){return [0,[1,[0,_qW,_r7,_r8],_9]];}else{var _ra=B(_p7(_qX,_r9[1]));if(!_ra[0]){return [0,[1,[2,_qW,_ra[1],_r7,_r8],_9]];}else{var _rb=_ra[1];return [1,new T(function(){var _rc=E(E(_r8)[2]);return [0,new T(function(){return B(_3d(function(_rd){return new F(function(){return _dZ(_rb,_rd);});},_rc[1]));}),new T(function(){return B(_dZ(_rb,_rc[2]));})];})];}}}};},_re=[1,_9],_rf=[1],_rg=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_rh=function(_ri){return new F(function(){return err(_rg);});},_rj=new T(function(){return B(_rh(_));}),_rk=function(_rl,_rm,_rn){var _ro=E(_rn);if(!_ro[0]){var _rp=_ro[1],_rq=E(_rm);if(!_rq[0]){var _rr=_rq[1],_rs=_rq[2];if(_rr<=(imul(3,_rp)|0)){return [0,(1+_rr|0)+_rp|0,E(E(_rl)),E(_rq),E(_ro)];}else{var _rt=E(_rq[3]);if(!_rt[0]){var _ru=_rt[1],_rv=E(_rq[4]);if(!_rv[0]){var _rw=_rv[1],_rx=_rv[2],_ry=_rv[3];if(_rw>=(imul(2,_ru)|0)){var _rz=function(_rA){var _rB=E(_rv[4]);return _rB[0]==0?[0,(1+_rr|0)+_rp|0,E(_rx),E([0,(1+_ru|0)+_rA|0,E(_rs),E(_rt),E(_ry)]),E([0,(1+_rp|0)+_rB[1]|0,E(E(_rl)),E(_rB),E(_ro)])]:[0,(1+_rr|0)+_rp|0,E(_rx),E([0,(1+_ru|0)+_rA|0,E(_rs),E(_rt),E(_ry)]),E([0,1+_rp|0,E(E(_rl)),E(_rf),E(_ro)])];},_rC=E(_ry);return _rC[0]==0?B(_rz(_rC[1])):B(_rz(0));}else{return [0,(1+_rr|0)+_rp|0,E(_rs),E(_rt),E([0,(1+_rp|0)+_rw|0,E(E(_rl)),E(_rv),E(_ro)])];}}else{return E(_rj);}}else{return E(_rj);}}}else{return [0,1+_rp|0,E(E(_rl)),E(_rf),E(_ro)];}}else{var _rD=E(_rm);if(!_rD[0]){var _rE=_rD[1],_rF=_rD[2],_rG=_rD[4],_rH=E(_rD[3]);if(!_rH[0]){var _rI=_rH[1],_rJ=E(_rG);if(!_rJ[0]){var _rK=_rJ[1],_rL=_rJ[2],_rM=_rJ[3];if(_rK>=(imul(2,_rI)|0)){var _rN=function(_rO){var _rP=E(_rJ[4]);return _rP[0]==0?[0,1+_rE|0,E(_rL),E([0,(1+_rI|0)+_rO|0,E(_rF),E(_rH),E(_rM)]),E([0,1+_rP[1]|0,E(E(_rl)),E(_rP),E(_rf)])]:[0,1+_rE|0,E(_rL),E([0,(1+_rI|0)+_rO|0,E(_rF),E(_rH),E(_rM)]),E([0,1,E(E(_rl)),E(_rf),E(_rf)])];},_rQ=E(_rM);return _rQ[0]==0?B(_rN(_rQ[1])):B(_rN(0));}else{return [0,1+_rE|0,E(_rF),E(_rH),E([0,1+_rK|0,E(E(_rl)),E(_rJ),E(_rf)])];}}else{return [0,3,E(_rF),E(_rH),E([0,1,E(E(_rl)),E(_rf),E(_rf)])];}}else{var _rR=E(_rG);return _rR[0]==0?[0,3,E(_rR[2]),E([0,1,E(_rF),E(_rf),E(_rf)]),E([0,1,E(E(_rl)),E(_rf),E(_rf)])]:[0,2,E(E(_rl)),E(_rD),E(_rf)];}}else{return [0,1,E(E(_rl)),E(_rf),E(_rf)];}}},_rS=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_rT=function(_rU){return new F(function(){return err(_rS);});},_rV=new T(function(){return B(_rT(_));}),_rW=function(_rX,_rY,_rZ){var _s0=E(_rY);if(!_s0[0]){var _s1=_s0[1],_s2=E(_rZ);if(!_s2[0]){var _s3=_s2[1],_s4=_s2[2];if(_s3<=(imul(3,_s1)|0)){return [0,(1+_s1|0)+_s3|0,E(E(_rX)),E(_s0),E(_s2)];}else{var _s5=E(_s2[3]);if(!_s5[0]){var _s6=_s5[1],_s7=_s5[2],_s8=_s5[3],_s9=E(_s2[4]);if(!_s9[0]){var _sa=_s9[1];if(_s6>=(imul(2,_sa)|0)){var _sb=function(_sc){var _sd=E(_rX),_se=E(_s5[4]);return _se[0]==0?[0,(1+_s1|0)+_s3|0,E(_s7),E([0,(1+_s1|0)+_sc|0,E(_sd),E(_s0),E(_s8)]),E([0,(1+_sa|0)+_se[1]|0,E(_s4),E(_se),E(_s9)])]:[0,(1+_s1|0)+_s3|0,E(_s7),E([0,(1+_s1|0)+_sc|0,E(_sd),E(_s0),E(_s8)]),E([0,1+_sa|0,E(_s4),E(_rf),E(_s9)])];},_sf=E(_s8);return _sf[0]==0?B(_sb(_sf[1])):B(_sb(0));}else{return [0,(1+_s1|0)+_s3|0,E(_s4),E([0,(1+_s1|0)+_s6|0,E(E(_rX)),E(_s0),E(_s5)]),E(_s9)];}}else{return E(_rV);}}else{return E(_rV);}}}else{return [0,1+_s1|0,E(E(_rX)),E(_s0),E(_rf)];}}else{var _sg=E(_rZ);if(!_sg[0]){var _sh=_sg[1],_si=_sg[2],_sj=_sg[4],_sk=E(_sg[3]);if(!_sk[0]){var _sl=_sk[1],_sm=_sk[2],_sn=_sk[3],_so=E(_sj);if(!_so[0]){var _sp=_so[1];if(_sl>=(imul(2,_sp)|0)){var _sq=function(_sr){var _ss=E(_rX),_st=E(_sk[4]);return _st[0]==0?[0,1+_sh|0,E(_sm),E([0,1+_sr|0,E(_ss),E(_rf),E(_sn)]),E([0,(1+_sp|0)+_st[1]|0,E(_si),E(_st),E(_so)])]:[0,1+_sh|0,E(_sm),E([0,1+_sr|0,E(_ss),E(_rf),E(_sn)]),E([0,1+_sp|0,E(_si),E(_rf),E(_so)])];},_su=E(_sn);return _su[0]==0?B(_sq(_su[1])):B(_sq(0));}else{return [0,1+_sh|0,E(_si),E([0,1+_sl|0,E(E(_rX)),E(_rf),E(_sk)]),E(_so)];}}else{return [0,3,E(_sm),E([0,1,E(E(_rX)),E(_rf),E(_rf)]),E([0,1,E(_si),E(_rf),E(_rf)])];}}else{var _sv=E(_sj);return _sv[0]==0?[0,3,E(_si),E([0,1,E(E(_rX)),E(_rf),E(_rf)]),E(_sv)]:[0,2,E(E(_rX)),E(_rf),E(_sg)];}}else{return [0,1,E(E(_rX)),E(_rf),E(_rf)];}}},_sw=function(_sx){return [0,1,E(E(_sx)),E(_rf),E(_rf)];},_sy=function(_sz,_sA){var _sB=E(_sA);if(!_sB[0]){return new F(function(){return _rk(_sB[2],B(_sy(_sz,_sB[3])),_sB[4]);});}else{return new F(function(){return _sw(_sz);});}},_sC=function(_sD,_sE){var _sF=E(_sE);if(!_sF[0]){return new F(function(){return _rW(_sF[2],_sF[3],B(_sC(_sD,_sF[4])));});}else{return new F(function(){return _sw(_sD);});}},_sG=function(_sH,_sI,_sJ,_sK,_sL){return new F(function(){return _rW(_sJ,_sK,B(_sC(_sH,_sL)));});},_sM=function(_sN,_sO,_sP,_sQ,_sR){return new F(function(){return _rk(_sP,B(_sy(_sN,_sQ)),_sR);});},_sS=function(_sT,_sU,_sV,_sW,_sX,_sY){var _sZ=E(_sU);if(!_sZ[0]){var _t0=_sZ[1],_t1=_sZ[2],_t2=_sZ[3],_t3=_sZ[4];if((imul(3,_t0)|0)>=_sV){if((imul(3,_sV)|0)>=_t0){return [0,(_t0+_sV|0)+1|0,E(E(_sT)),E(_sZ),E([0,_sV,E(_sW),E(_sX),E(_sY)])];}else{return new F(function(){return _rW(_t1,_t2,B(_sS(_sT,_t3,_sV,_sW,_sX,_sY)));});}}else{return new F(function(){return _rk(_sW,B(_t4(_sT,_t0,_t1,_t2,_t3,_sX)),_sY);});}}else{return new F(function(){return _sM(_sT,_sV,_sW,_sX,_sY);});}},_t4=function(_t5,_t6,_t7,_t8,_t9,_ta){var _tb=E(_ta);if(!_tb[0]){var _tc=_tb[1],_td=_tb[2],_te=_tb[3],_tf=_tb[4];if((imul(3,_t6)|0)>=_tc){if((imul(3,_tc)|0)>=_t6){return [0,(_t6+_tc|0)+1|0,E(E(_t5)),E([0,_t6,E(_t7),E(_t8),E(_t9)]),E(_tb)];}else{return new F(function(){return _rW(_t7,_t8,B(_sS(_t5,_t9,_tc,_td,_te,_tf)));});}}else{return new F(function(){return _rk(_td,B(_t4(_t5,_t6,_t7,_t8,_t9,_te)),_tf);});}}else{return new F(function(){return _sG(_t5,_t6,_t7,_t8,_t9);});}},_tg=function(_th,_ti,_tj){var _tk=E(_ti);if(!_tk[0]){var _tl=_tk[1],_tm=_tk[2],_tn=_tk[3],_to=_tk[4],_tp=E(_tj);if(!_tp[0]){var _tq=_tp[1],_tr=_tp[2],_ts=_tp[3],_tt=_tp[4];if((imul(3,_tl)|0)>=_tq){if((imul(3,_tq)|0)>=_tl){return [0,(_tl+_tq|0)+1|0,E(E(_th)),E(_tk),E(_tp)];}else{return new F(function(){return _rW(_tm,_tn,B(_sS(_th,_to,_tq,_tr,_ts,_tt)));});}}else{return new F(function(){return _rk(_tr,B(_t4(_th,_tl,_tm,_tn,_to,_ts)),_tt);});}}else{return new F(function(){return _sG(_th,_tl,_tm,_tn,_to);});}}else{return new F(function(){return _sy(_th,_tj);});}},_tu=function(_tv,_tw,_tx,_ty){var _tz=E(_ty);if(!_tz[0]){var _tA=new T(function(){var _tB=B(_tu(_tz[1],_tz[2],_tz[3],_tz[4]));return [0,_tB[1],_tB[2]];});return [0,new T(function(){return E(E(_tA)[1]);}),new T(function(){return B(_rk(_tw,_tx,E(_tA)[2]));})];}else{return [0,_tw,_tx];}},_tC=function(_tD,_tE,_tF,_tG){var _tH=E(_tF);if(!_tH[0]){var _tI=new T(function(){var _tJ=B(_tC(_tH[1],_tH[2],_tH[3],_tH[4]));return [0,_tJ[1],_tJ[2]];});return [0,new T(function(){return E(E(_tI)[1]);}),new T(function(){return B(_rW(_tE,E(_tI)[2],_tG));})];}else{return [0,_tE,_tG];}},_tK=function(_tL,_tM){var _tN=E(_tL);if(!_tN[0]){var _tO=_tN[1],_tP=E(_tM);if(!_tP[0]){var _tQ=_tP[1];if(_tO<=_tQ){var _tR=B(_tC(_tQ,_tP[2],_tP[3],_tP[4]));return new F(function(){return _rk(_tR[1],_tN,_tR[2]);});}else{var _tS=B(_tu(_tO,_tN[2],_tN[3],_tN[4]));return new F(function(){return _rW(_tS[1],_tS[2],_tP);});}}else{return E(_tN);}}else{return E(_tM);}},_tT=function(_tU,_tV,_tW,_tX,_tY){var _tZ=E(_tU);if(!_tZ[0]){var _u0=_tZ[1],_u1=_tZ[2],_u2=_tZ[3],_u3=_tZ[4];if((imul(3,_u0)|0)>=_tV){if((imul(3,_tV)|0)>=_u0){return new F(function(){return _tK(_tZ,[0,_tV,E(_tW),E(_tX),E(_tY)]);});}else{return new F(function(){return _rW(_u1,_u2,B(_tT(_u3,_tV,_tW,_tX,_tY)));});}}else{return new F(function(){return _rk(_tW,B(_u4(_u0,_u1,_u2,_u3,_tX)),_tY);});}}else{return [0,_tV,E(_tW),E(_tX),E(_tY)];}},_u4=function(_u5,_u6,_u7,_u8,_u9){var _ua=E(_u9);if(!_ua[0]){var _ub=_ua[1],_uc=_ua[2],_ud=_ua[3],_ue=_ua[4];if((imul(3,_u5)|0)>=_ub){if((imul(3,_ub)|0)>=_u5){return new F(function(){return _tK([0,_u5,E(_u6),E(_u7),E(_u8)],_ua);});}else{return new F(function(){return _rW(_u6,_u7,B(_tT(_u8,_ub,_uc,_ud,_ue)));});}}else{return new F(function(){return _rk(_uc,B(_u4(_u5,_u6,_u7,_u8,_ud)),_ue);});}}else{return [0,_u5,E(_u6),E(_u7),E(_u8)];}},_uf=function(_ug,_uh){var _ui=E(_ug);if(!_ui[0]){var _uj=_ui[1],_uk=_ui[2],_ul=_ui[3],_um=_ui[4],_un=E(_uh);if(!_un[0]){var _uo=_un[1],_up=_un[2],_uq=_un[3],_ur=_un[4];if((imul(3,_uj)|0)>=_uo){if((imul(3,_uo)|0)>=_uj){return new F(function(){return _tK(_ui,_un);});}else{return new F(function(){return _rW(_uk,_ul,B(_tT(_um,_uo,_up,_uq,_ur)));});}}else{return new F(function(){return _rk(_up,B(_u4(_uj,_uk,_ul,_um,_uq)),_ur);});}}else{return E(_ui);}}else{return E(_uh);}},_us=function(_ut,_uu){var _uv=E(_uu);if(!_uv[0]){var _uw=_uv[2],_ux=_uv[3],_uy=_uv[4];if(!B(A(_ut,[_uw]))){return new F(function(){return _uf(B(_us(_ut,_ux)),B(_us(_ut,_uy)));});}else{return new F(function(){return _tg(_uw,B(_us(_ut,_ux)),B(_us(_ut,_uy)));});}}else{return [1];}},_uz=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_uA=new T(function(){return B(err(_uz));}),_uB=function(_uC,_uD,_uE,_uF){while(1){var _uG=E(_uE);if(!_uG[0]){_uC=_uG[1];_uD=_uG[2];_uE=_uG[3];_uF=_uG[4];continue;}else{return E(_uD);}}},_uH=function(_uI,_uJ){var _uK=B(_us(function(_uL){return new F(function(){return _3x(E(_uL)[2],_uI);});},_uJ));if(!_uK[0]){var _uM=E(_uK[3]);return _uM[0]==0?B(_uB(_uM[1],_uM[2],_uM[3],_uM[4])):E(_uK[2]);}else{return E(_uA);}},_uN=function(_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ,_v0,_v1){var _v2=function(_v3,_v4,_v5){var _v6=E(_v5);if(!_v6[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_uV,[_v4]));}),_9]],_9],[1,[1,new T(function(){return B(A(_uV,[_v4]));}),_9]]]];}else{var _v7=function(_v8){var _v9=E(_v8);if(!_v9[0]){return E(_re);}else{var _va=E(_v9[1]),_vb=B(_v2(_v3,_va[1],_va[2]));if(!_vb[0]){return [0,_vb[1]];}else{var _vc=B(_v7(_v9[2]));return _vc[0]==0?E(_vc):[1,[1,_vb[1],_vc[1]]];}}},_vd=B(_v7(_v6[2]));return _vd[0]==0?[0,_vd[1]]:B(A(new T(function(){return B(_qI(_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY));}),[new T(function(){return B(_uH(_v6[1],_v3));}),_vd[1],_v4]));}};return new F(function(){return _v2(_uZ,_v0,_v1);});},_ve=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_vf=new T(function(){return B(err(_ve));}),_vg=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_vh=new T(function(){return B(err(_vg));}),_vi=function(_vj,_vk){while(1){var _vl=E(_vj);if(!_vl[0]){return E(_vh);}else{var _vm=E(_vk);if(!_vm){return E(_vl[1]);}else{_vj=_vl[2];_vk=_vm-1|0;continue;}}}},_vn=function(_vo,_vp){while(1){var _vq=E(_vp);if(!_vq[0]){return true;}else{if(!B(A(_vo,[_vq[1]]))){return false;}else{_vp=_vq[2];continue;}}}},_vr=[3],_vs=function(_vt){var _vu=E(_vt);switch(_vu[0]){case 1:return [0,_vu[1]];case 3:return [3];default:return E(_vu);}},_vv=function(_vw,_vx){return [0,_vr,new T(function(){var _vy=B(_ja(_vx,0))-E(_vw)[1]|0,_vz=new T(function(){return _vy>=0?B(_nP(_vy,_vx)):E(_vx);});if(_vy>0){var _vA=function(_vB,_vC){var _vD=E(_vB);if(!_vD[0]){return E(_vz);}else{var _vE=_vD[1];return _vC>1?[1,new T(function(){return B(_vs(_vE));}),new T(function(){return B(_vA(_vD[2],_vC-1|0));})]:[1,new T(function(){return B(_vs(_vE));}),_vz];}},_vF=B(_vA(_vx,_vy));}else{var _vF=E(_vz);}var _vG=_vF,_vH=_vG,_vI=_vH,_vJ=_vI;return _vJ;})];},_vK=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_vL=[2,_vK],_vM=new T(function(){return B(unCStr(" is closed, and can\'t be used"));}),_vN=function(_vO){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_vO)[1],_9)),_vM));}));});},_vP=new T(function(){return B(unCStr(" has nothing on it"));}),_vQ=function(_vR){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_vR)[1],_9)),_vP));}));});},_vS=new T(function(){return B(unCStr(" depends on something not-well-formed, and can\'t be used"));}),_vT=function(_vU){return new F(function(){return unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,E(_vU)[1],_9)),_vS));}));});},_vV=function(_vW,_vX,_vY,_vZ,_w0,_w1,_w2){var _w3=E(_vW);if(_w3[0]==1){var _w4=E(_vX);return _w4[0]==1?[0,[1,[0,_vY,[1,_w1,[1,_w3[1],[1,_w4[1],_9]]]]],_w2]:[0,[2,new T(function(){switch(E(_w4)[0]){case 0:var _w5=B(_vN(_w0));break;case 2:var _w5=B(_vT(_w0));break;default:var _w5=B(_vQ(_w0));}return _w5;})],_w2];}else{var _w6=E(_vX);return _w6[0]==1?[0,[2,new T(function(){switch(E(_w3)[0]){case 0:var _w7=B(_vN(_vZ));break;case 2:var _w7=B(_vT(_vZ));break;default:var _w7=B(_vQ(_vZ));}return _w7;})],_w2]:[0,[2,new T(function(){var _w8=new T(function(){return B(unAppCStr(" and ",new T(function(){switch(E(_w6)[0]){case 0:var _w9=B(_vN(_w0));break;case 2:var _w9=B(_vT(_w0));break;default:var _w9=B(_vQ(_w0));}return _w9;})));},1);switch(E(_w3)[0]){case 0:var _wa=B(_e(B(_vN(_vZ)),_w8));break;case 2:var _wa=B(_e(B(_vT(_vZ)),_w8));break;default:var _wa=B(_e(B(_vQ(_vZ)),_w8));}return _wa;})],_w2];}},_wb=function(_wc,_wd){while(1){var _we=E(_wc);if(!_we[0]){return E(_wd);}else{_wc=_we[2];var _wf=[1,_we[1],_wd];_wd=_wf;continue;}}},_wg=function(_wh){return new F(function(){return _wb(_wh,_9);});},_wi=function(_wj,_wk){return _wj<=B(_ja(_wk,0))?[1,new T(function(){var _wl=_wj-1|0;if(_wl>=0){var _wm=B(_vi(B(_wg(_wk)),_wl));}else{var _wm=E(_vf);}var _wn=_wm,_wo=_wn;return _wo;})]:[0];},_wp=new T(function(){return B(unCStr(" is unavailable"));}),_wq=new T(function(){return B(unCStr(" are unavailable"));}),_wr=function(_ws,_wt,_wu,_wv,_ww,_wx,_wy){var _wz=B(_wA(_ws,_wt,[1,_vr,_wy])),_wB=B(_wi(_wv,_wz));if(!_wB[0]){return B(_wi(_ww,_wz))[0]==0?B(_wA(_ws,_wt,[1,[2,new T(function(){return B(unAppCStr("The lines ",new T(function(){return B(_e(B(_F(0,_wv,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_ww,_9)),_wq));})));},1)));})));})],_wy])):B(_wA(_ws,_wt,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_wv,_9)),_wp));})));})],_wy]));}else{var _wC=B(_wi(_ww,_wz));return _wC[0]==0?B(_wA(_ws,_wt,[1,[2,new T(function(){return B(unAppCStr("The line ",new T(function(){return B(_e(B(_F(0,_ww,_9)),_wp));})));})],_wy])):B(_wA(_ws,_wt,new T(function(){var _wD=B(_vV(_wB[1],_wC[1],_wu,[0,_wv],[0,_ww],_wx,_wy));return [1,_wD[1],_wD[2]];})));}},_wE=function(_wF,_wG,_wH,_wI,_wJ,_wK,_wL){return new F(function(){return _wr(_wF,_wG,_wH,E(_wI)[1],E(_wJ)[1],_wK,_wL);});},_wM=new T(function(){return B(unCStr("wrong number of lines cited"));}),_wN=[2,_wM],_wO=function(_wP,_wQ,_wR,_wS,_wT,_wU){var _wV=E(_wT);if(!_wV[0]){return new F(function(){return _wA(_wP,_wQ,[1,_wN,_wU]);});}else{var _wW=E(_wV[2]);return _wW[0]==0?B(_wA(_wP,_wQ,[1,_wN,_wU])):E(_wW[2])[0]==0?B(_wE(_wP,_wQ,_wR,_wV[1],_wW[1],_wS,_wU)):B(_wA(_wP,_wQ,[1,_wN,_wU]));}},_wX=new T(function(){return B(unCStr("Open Subproof"));}),_wY=[2,_wX],_wZ=new T(function(){return B(unCStr("Impossible Error 2"));}),_x0=[2,_wZ],_x1=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_x2=[2,_x1],_x3=new T(function(){return B(unCStr("SHOW"));}),_x4=function(_x5,_x6,_x7,_x8,_x9,_xa){var _xb=new T(function(){return B(_wA(_x5,_x6,[1,_vr,_xa]));});if(_x8<=B(_ja(_xb,0))){var _xc=_x8-1|0;if(_xc>=0){var _xd=B(_vi(B(_wg(_xb)),_xc));switch(_xd[0]){case 0:return new F(function(){return _wA(_x5,_x6,[1,[2,new T(function(){return B(_vN([0,_x8]));})],_xa]);});break;case 1:return new F(function(){return _wA(_x5,_x6,[1,[1,[0,_x7,[1,_x9,[1,_xd[1],_9]]]],_xa]);});break;case 2:return new F(function(){return _wA(_x5,_x6,[1,[2,new T(function(){return B(_vT([0,_x8]));})],_xa]);});break;default:return new F(function(){return _wA(_x5,_x6,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_x8,_9)),_vP));})));})],_xa]);});}}else{return E(_vf);}}else{return new F(function(){return _wA(_x5,_x6,[1,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_x8,_9)),_wp));})));})],_xa]);});}},_xe=function(_xf,_xg,_xh,_xi,_xj,_xk){return new F(function(){return _x4(_xf,_xg,_xh,E(_xi)[1],_xj,_xk);});},_xl=function(_xm,_xn,_xo,_xp,_xq,_xr){var _xs=E(_xq);return _xs[0]==0?B(_wA(_xm,_xn,[1,_wN,_xr])):E(_xs[2])[0]==0?B(_xe(_xm,_xn,_xo,_xs[1],_xp,_xr)):B(_wA(_xm,_xn,[1,_wN,_xr]));},_xt=function(_xu,_xv,_xw,_xx,_xy,_xz){if(!B(_3x(_xv,_x3))){var _xA=B(A(_xx,[_xv]));if(!_xA[0]){return [0,_vL,_xz];}else{var _xB=E(_xA[1]);if(!_xB[0]){return [0,_x2,_xz];}else{switch(E(E(_xB[1])[1])){case 1:return new F(function(){return _vv(new T(function(){return [0,B(_ja(_xz,0))+1|0];},1),new T(function(){return B(_xl(_xy,_xx,_xu,_xv,_xw,_xz));}));});break;case 2:return new F(function(){return _vv(new T(function(){return [0,B(_ja(_xz,0))+1|0];},1),new T(function(){return B(_wO(_xy,_xx,_xu,_xv,_xw,_xz));}));});break;default:return [0,_x0,_xz];}}}}else{return new F(function(){return _vv(new T(function(){return [0,B(_ja(_xz,0))+1|0];},1),new T(function(){return B(_wA(_xy,_xx,[1,_wY,_xz]));}));});}},_xC=[0],_xD=new T(function(){return B(unCStr("PR"));}),_xE=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_xF=[2,_xE],_xG=new T(function(){return B(unCStr("Impossible Error 1"));}),_xH=[2,_xG],_xI=function(_xJ,_xK,_xL,_xM,_xN){var _xO=B(_wi(_xK,_xN));if(!_xO[0]){return B(_wi(_xL,_xN))[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the lines ",new T(function(){return B(_e(B(_F(0,_xK,_9)),new T(function(){return B(unAppCStr(" and ",new T(function(){return B(_e(B(_F(0,_xL,_9)),_wq));})));},1)));})));})],_xN]:[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_xK,_9)),_wp));})));})],_xN];}else{var _xP=B(_wi(_xL,_xN));return _xP[0]==0?[0,[2,new T(function(){return B(unAppCStr(" the line ",new T(function(){return B(_e(B(_F(0,_xL,_9)),_wp));})));})],_xN]:B(_vV(_xO[1],_xP[1],_xJ,[0,_xK],[0,_xL],_xM,_xN));}},_xQ=new T(function(){return B(unCStr("wrong number of premises"));}),_xR=[2,_xQ],_xS=function(_xT,_xU,_xV,_xW){var _xX=E(_xV);if(!_xX[0]){return [1,_xR,_xW];}else{var _xY=E(_xX[2]);if(!_xY[0]){return [1,_xR,_xW];}else{if(!E(_xY[2])[0]){var _xZ=B(_xI(_xT,E(_xX[1])[1],E(_xY[1])[1],_xU,_xW));return [1,_xZ[1],_xZ[2]];}else{return [1,_xR,_xW];}}}},_y0=new T(function(){return B(unCStr("has nothing on it"));}),_y1=new T(function(){return B(unCStr("is unavailable"));}),_y2=function(_y3,_y4,_y5,_y6){var _y7=B(_wi(_y4,_y6));if(!_y7[0]){return [0,[2,new T(function(){return B(unAppCStr("line",new T(function(){return B(_e(B(_F(0,_y4,_9)),_y1));})));})],_y6];}else{var _y8=E(_y7[1]);switch(_y8[0]){case 0:return [0,[2,new T(function(){return B(_vN([0,_y4]));})],_y6];case 1:return [0,[1,[0,_y3,[1,_y5,[1,_y8[1],_9]]]],_y6];case 2:return [0,[2,new T(function(){return B(_vT([0,_y4]));})],_y6];default:return [0,[2,new T(function(){return B(unAppCStr("line ",new T(function(){return B(_e(B(_F(0,_y4,_9)),_y0));})));})],_y6];}}},_y9=function(_ya,_yb,_yc,_yd){var _ye=B(_y2(_ya,E(_yb)[1],_yc,_yd));return [1,_ye[1],_ye[2]];},_yf=function(_yg,_yh,_yi,_yj){var _yk=E(_yi);return _yk[0]==0?[1,_xR,_yj]:E(_yk[2])[0]==0?B(_y9(_yg,_yk[1],_yh,_yj)):[1,_xR,_yj];},_yl=function(_ym,_yn,_yo,_yp,_yq){var _yr=function(_ys){var _yt=B(A(_yp,[_yn]));if(!_yt[0]){return [1,_vL,_yq];}else{var _yu=E(_yt[1]);if(!_yu[0]){switch(E(E(_yu[1])[1])){case 1:return new F(function(){return _yf(_ym,_yn,_yo,_yq);});break;case 2:return new F(function(){return _xS(_ym,_yn,_yo,_yq);});break;default:return [1,_xH,_yq];}}else{return [1,_xF,_yq];}}};return !B(_3x(_yn,_xD))?B(_yr(_)):E(_yo)[0]==0?[1,[1,[0,_ym,_xC]],_yq]:B(_yr(_));},_yv=function(_yw,_yx,_yy){var _yz=E(_yw);return new F(function(){return _yl(_yz[1],_yz[2],_yz[3],_yx,_yy);});},_yA=new T(function(){return B(unCStr("shouldn\'t happen"));}),_yB=[2,_yA],_yC=new T(function(){return B(unCStr("incomplete line"));}),_yD=[2,_yC],_yE=function(_yF,_yG,_yH,_yI){var _yJ=E(_yF);if(!_yJ[0]){return E(_yG)[0]==0?[1,_yD,_yI]:[1,_yB,_yI];}else{var _yK=_yJ[1],_yL=E(_yG);if(!_yL[0]){return new F(function(){return _yv(_yK,_yH,_yI);});}else{var _yM=E(_yK),_yN=B(_xt(_yM[1],_yM[2],_yM[3],_yH,_yL,_yI));return [1,_yN[1],_yN[2]];}}},_yO=function(_yP,_yQ,_yR){var _yS=E(_yP);return new F(function(){return _yE(_yS[1],_yS[2],_yQ,_yR);});},_wA=function(_yT,_yU,_yV){return new F(function(){return (function(_yW,_yX){while(1){var _yY=(function(_yZ,_z0){var _z1=E(_z0);if(!_z1[0]){return E(_yZ);}else{_yW=new T(function(){return B(_yO(_z1[1],_yU,_yZ));});_yX=_z1[2];return null;}})(_yW,_yX);if(_yY!=null){return _yY;}}})(_yV,_yT);});},_z2=[0,666],_z3=[0,_,_z2],_z4=[1,_z3],_z5=[0,_z4,_xC],_z6=function(_z7,_z8,_z9,_za,_zb,_zc,_zd,_ze,_zf,_zg,_zh,_zi,_zj,_zk){var _zl=B(_wA(_zi,_zj,_9)),_zm=function(_zn,_zo,_zp){return B(_uN(_z7,_z8,_z9,_za,_zb,_zc,_zd,_zn,_zf,_zg,_zh,_zk,_zo,_zp))[0]==0?false:true;};return !B(_vn(function(_zq){var _zr=E(_zq);switch(_zr[0]){case 0:var _zs=E(_zr[1]);return new F(function(){return _zm(_ze,_zs[1],_zs[2]);});break;case 1:var _zt=E(_zr[1]);return new F(function(){return _zm(_ze,_zt[1],_zt[2]);});break;case 2:return false;default:return true;}},_zl))?[0,_zl]:[1,new T(function(){var _zu=B(_ja(_zi,0))-1|0;if(_zu>=0){var _zv=B(_vi(B(_wg(_zl)),_zu)),_zw=_zv[0]==1?E(_zv[1]):E(_z5);}else{var _zw=E(_vf);}var _zx=_zw,_zy=_zx,_zz=_zy;return _zz;})];},_zA=function(_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI,_zJ,_zK,_zL,_zM,_zN,_zO){var _zP=B(_z6(_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI,_zJ,_zK,_zL,_zM,_zN,_zO));return _zP[0]==0?[0,_zP[1]]:[1,new T(function(){var _zQ=E(_zP[1]);return B(_uN(_zB,_zC,_zD,_zE,_zF,_zG,_zH,_zI,_zJ,_zK,_zL,_zO,_zQ[1],_zQ[2]));})];},_zR=2,_zS=new T(function(){return B(unCStr("class"));}),_zT=new T(function(){return B(unCStr("lined"));}),_zU=function(_zV,_){return [0,[0,_6S,[1,_zV]],_zV];},_zW=function(_zX){return function(_zY,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _zZ=E(_zX);return B(_e(B(_F(0,E(_zZ[2])[1],_9)),_zZ[1]));})]]],_zY];};},_A0=function(_A1,_){return new F(function(){return _7u(_zU,_zW,_A1,_);});},_A2=function(_A3){return function(_A4,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _A5=E(_A3);return B(_e(B(_F(0,E(_A5[2])[1],_9)),_A5[1]));})]]],_A4];};},_A6=function(_A1,_){return new F(function(){return _7u(_zU,_A2,_A1,_);});},_A7=function(_A8){return function(_A9,_){return [0,[0,_6S,[1,[1,_6I,new T(function(){var _Aa=E(_A8);return B(_e(B(_F(0,E(_Aa[2])[1],_9)),_Aa[1]));})]]],_A9];};},_Ab=function(_A1,_){return new F(function(){return _7u(_zU,_A7,_A1,_);});},_Ac=new T(function(){return B(unCStr("rslt"));}),_Ad=new T(function(){return B(unCStr("root"));}),_Ae=new T(function(){return B(unCStr("analysis"));}),_Af=new T(function(){return B(unCStr("invalid"));}),_Ag=function(_A1,_){return new F(function(){return _7i(_6v,_Af,_A1,_);});},_Ah=[1,_6B],_Ai=[0,_Ag,_Ah],_Aj=function(_Ak,_){return [0,_Ai,_Ak];},_Al=new T(function(){return B(unCStr("span"));}),_Am=function(_An,_Ao,_Ap,_Aq,_){var _Ar=B(A(_Ap,[_Aq,_])),_As=_Ar,_At=E(_As),_Au=E(_At[1]),_Av=_Au[1];return [0,[0,function(_Aw,_){var _Ax=jsFind(toJSStr(E(_An))),_Ay=_Ax,_Az=E(_Ay);if(!_Az[0]){return _Aw;}else{var _AA=_Az[1];switch(E(_Ao)){case 0:var _AB=B(A(_Av,[_AA,_])),_AC=_AB;return _Aw;case 1:var _AD=E(_AA),_AE=_AD[1],_AF=jsGetChildren(_AE),_AG=_AF,_AH=E(_AG);if(!_AH[0]){var _AI=B(A(_Av,[_AD,_])),_AJ=_AI;return _Aw;}else{var _AK=jsCreateElem(toJSStr(E(_Al))),_AL=_AK,_AM=jsAddChildBefore(_AL,_AE,E(_AH[1])[1]),_AN=B(A(_Av,[[0,_AL],_])),_AO=_AN;return _Aw;}break;default:var _AP=E(_AA),_AQ=jsClearChildren(_AP[1]),_AR=B(A(_Av,[_AP,_])),_AS=_AR;return _Aw;}}},_Au[2]],_At[2]];},_AT=function(_AU,_AV){while(1){var _AW=E(_AU);if(!_AW[0]){return E(_AV)[0]==0?1:0;}else{var _AX=E(_AV);if(!_AX[0]){return 2;}else{var _AY=E(_AW[1])[1],_AZ=E(_AX[1])[1];if(_AY!=_AZ){return _AY>_AZ?2:0;}else{_AU=_AW[2];_AV=_AX[2];continue;}}}}},_B0=new T(function(){return B(_e(_9,_9));}),_B1=function(_B2,_B3,_B4,_B5,_B6,_B7,_B8,_B9){var _Ba=[0,_B2,_B3,_B4],_Bb=function(_Bc){var _Bd=E(_B5);if(!_Bd[0]){var _Be=E(_B9);if(!_Be[0]){switch(B(_AT(_B2,_B6))){case 0:return [0,[0,_B6,_B7,_B8],_9];case 1:return _B3>=_B7?_B3!=_B7?[0,_Ba,_9]:_B4>=_B8?_B4!=_B8?[0,_Ba,_9]:[0,_Ba,_B0]:[0,[0,_B6,_B7,_B8],_9]:[0,[0,_B6,_B7,_B8],_9];default:return [0,_Ba,_9];}}else{return [0,[0,_B6,_B7,_B8],_Be];}}else{switch(B(_AT(_B2,_B6))){case 0:return [0,[0,_B6,_B7,_B8],_B9];case 1:return _B3>=_B7?_B3!=_B7?[0,_Ba,_Bd]:_B4>=_B8?_B4!=_B8?[0,_Ba,_Bd]:[0,_Ba,new T(function(){return B(_e(_Bd,_B9));})]:[0,[0,_B6,_B7,_B8],_B9]:[0,[0,_B6,_B7,_B8],_B9];default:return [0,_Ba,_Bd];}}};if(!E(_B9)[0]){var _Bf=E(_B5);return _Bf[0]==0?B(_Bb(_)):[0,_Ba,_Bf];}else{return new F(function(){return _Bb(_);});}},_Bg=new T(function(){return B(_wb(_9,_9));}),_Bh=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_Bi=new T(function(){return B(err(_Bh));}),_Bj=function(_Bk,_Bl,_Bm,_Bn,_Bo){var _Bp=function(_Bq,_Br,_Bs){var _Bt=[1,_Br,_Bq];return new F(function(){return A(_Bk,[_Bs,new T(function(){var _Bu=E(_Bq);return function(_Bv,_Bw,_Bx){return new F(function(){return _Bp(_Bt,_Bv,_Bw);});};}),_Bn,_Bi,function(_By){return new F(function(){return A(_Bm,[new T(function(){return B(_wb(_Bt,_9));}),_Bs,new T(function(){var _Bz=E(E(_Bs)[2]),_BA=E(_By),_BB=E(_BA[1]),_BC=B(_B1(_BB[1],_BB[2],_BB[3],_BA[2],_Bz[1],_Bz[2],_Bz[3],_9));return [0,E(_BC[1]),_BC[2]];})]);});}]);});};return new F(function(){return A(_Bk,[_Bl,function(_BD,_BE,_BF){return new F(function(){return _Bp(_9,_BD,_BE);});},_Bn,_Bi,function(_BG){return new F(function(){return A(_Bo,[_Bg,_Bl,new T(function(){var _BH=E(E(_Bl)[2]),_BI=E(_BG),_BJ=E(_BI[1]),_BK=B(_B1(_BJ[1],_BJ[2],_BJ[3],_BI[2],_BH[1],_BH[2],_BH[3],_9));return [0,E(_BK[1]),_BK[2]];})]);});}]);});},_BL=function(_BM,_BN){var _BO=E(_BM),_BP=E(_BO[1]),_BQ=E(_BN),_BR=E(_BQ[1]),_BS=B(_B1(_BP[1],_BP[2],_BP[3],_BO[2],_BR[1],_BR[2],_BR[3],_BQ[2]));return [0,E(_BS[1]),_BS[2]];},_BT=function(_BU,_BV,_BW,_BX,_BY,_BZ){var _C0=function(_C1,_C2,_C3,_C4,_C5){return new F(function(){return _Bj(_BU,_C2,function(_C6,_C7,_C8){return new F(function(){return A(_C3,[[1,_C1,_C6],_C7,new T(function(){var _C9=E(E(_C7)[2]),_Ca=E(_C8),_Cb=E(_Ca[1]),_Cc=B(_B1(_Cb[1],_Cb[2],_Cb[3],_Ca[2],_C9[1],_C9[2],_C9[3],_9));return [0,E(_Cc[1]),_Cc[2]];})]);});},_C4,function(_Cd,_Ce,_Cf){return new F(function(){return A(_C5,[[1,_C1,_Cd],_Ce,new T(function(){var _Cg=E(E(_Ce)[2]),_Ch=E(_Cf),_Ci=E(_Ch[1]),_Cj=B(_B1(_Ci[1],_Ci[2],_Ci[3],_Ch[2],_Cg[1],_Cg[2],_Cg[3],_9));return [0,E(_Cj[1]),_Cj[2]];})]);});});});};return new F(function(){return A(_BU,[_BV,function(_Ck,_Cl,_Cm){return new F(function(){return _C0(_Ck,_Cl,_BW,_BX,function(_Cn,_Co,_Cp){return new F(function(){return A(_BW,[_Cn,_Co,new T(function(){return B(_BL(_Cm,_Cp));})]);});});});},_BX,function(_Cq,_Cr,_Cs){return new F(function(){return _C0(_Cq,_Cr,_BW,_BX,function(_Ct,_Cu,_Cv){return new F(function(){return A(_BY,[_Ct,_Cu,new T(function(){return B(_BL(_Cs,_Cv));})]);});});});},_BZ]);});},_Cw=function(_Cx,_Cy,_Cz,_CA,_CB){var _CC=function(_CD,_CE){return new F(function(){return A(_Cx,[_CE,new T(function(){var _CF=E(_CD);return function(_CG,_CH,_CI){return new F(function(){return _CC(_9,_CH);});};}),_CA,_Bi,function(_CJ){return new F(function(){return A(_Cz,[_6B,_CE,new T(function(){var _CK=E(E(_CE)[2]),_CL=E(_CJ),_CM=E(_CL[1]),_CN=B(_B1(_CM[1],_CM[2],_CM[3],_CL[2],_CK[1],_CK[2],_CK[3],_9));return [0,E(_CN[1]),_CN[2]];})]);});}]);});};return new F(function(){return A(_Cx,[_Cy,function(_CO,_CP,_CQ){return new F(function(){return _CC(_9,_CP);});},_CA,_Bi,function(_CR){return new F(function(){return A(_CB,[_6B,_Cy,new T(function(){var _CS=E(E(_Cy)[2]),_CT=E(_CR),_CU=E(_CT[1]),_CV=B(_B1(_CU[1],_CU[2],_CU[3],_CT[2],_CS[1],_CS[2],_CS[3],_9));return [0,E(_CV[1]),_CV[2]];})]);});}]);});},_CW=function(_CX,_CY,_CZ,_D0,_D1,_D2,_D3){var _D4=function(_D5,_D6,_D7,_D8,_D9){var _Da=[1,_D5,_9],_Db=function(_Dc,_Dd,_De,_Df){return new F(function(){return _CW(_CX,_CY,_Dc,function(_Dg,_Dh,_Di){return new F(function(){return A(_Dd,[[1,_D5,_Dg],_Dh,new T(function(){var _Dj=E(E(_Dh)[2]),_Dk=E(_Di),_Dl=E(_Dk[1]),_Dm=B(_B1(_Dl[1],_Dl[2],_Dl[3],_Dk[2],_Dj[1],_Dj[2],_Dj[3],_9));return [0,E(_Dm[1]),_Dm[2]];})]);});},_De,function(_Dn,_Do,_Dp){return new F(function(){return A(_Df,[[1,_D5,_Dn],_Do,new T(function(){var _Dq=E(E(_Do)[2]),_Dr=E(_Dp),_Ds=E(_Dr[1]),_Dt=B(_B1(_Ds[1],_Ds[2],_Ds[3],_Dr[2],_Dq[1],_Dq[2],_Dq[3],_9));return [0,E(_Dt[1]),_Dt[2]];})]);});},function(_Du){return new F(function(){return A(_Df,[_Da,_Dc,new T(function(){var _Dv=E(E(_Dc)[2]),_Dw=_Dv[1],_Dx=_Dv[2],_Dy=_Dv[3],_Dz=E(_Du),_DA=E(_Dz[1]),_DB=B(_B1(_DA[1],_DA[2],_DA[3],_Dz[2],_Dw,_Dx,_Dy,_9)),_DC=E(_DB[1]),_DD=B(_B1(_DC[1],_DC[2],_DC[3],_DB[2],_Dw,_Dx,_Dy,_9));return [0,E(_DD[1]),_DD[2]];})]);});});});};return new F(function(){return A(_CY,[_D6,function(_DE,_DF,_DG){return new F(function(){return _Db(_DF,_D7,_D8,function(_DH,_DI,_DJ){return new F(function(){return A(_D7,[_DH,_DI,new T(function(){return B(_BL(_DG,_DJ));})]);});});});},_D8,function(_DK,_DL,_DM){return new F(function(){return _Db(_DL,_D7,_D8,function(_DN,_DO,_DP){return new F(function(){return A(_D9,[_DN,_DO,new T(function(){return B(_BL(_DM,_DP));})]);});});});},function(_DQ){return new F(function(){return A(_D9,[_Da,_D6,new T(function(){var _DR=E(E(_D6)[2]),_DS=E(_DQ),_DT=E(_DS[1]),_DU=B(_B1(_DT[1],_DT[2],_DT[3],_DS[2],_DR[1],_DR[2],_DR[3],_9));return [0,E(_DU[1]),_DU[2]];})]);});}]);});};return new F(function(){return A(_CX,[_CZ,function(_DV,_DW,_DX){return new F(function(){return _D4(_DV,_DW,_D0,_D1,function(_DY,_DZ,_E0){return new F(function(){return A(_D0,[_DY,_DZ,new T(function(){return B(_BL(_DX,_E0));})]);});});});},_D1,function(_E1,_E2,_E3){return new F(function(){return _D4(_E1,_E2,_D0,_D1,function(_E4,_E5,_E6){return new F(function(){return A(_D2,[_E4,_E5,new T(function(){return B(_BL(_E3,_E6));})]);});});});},_D3]);});},_E7=function(_E8,_E9){return new F(function(){return A(_E9,[_E8]);});},_Ea=[0,34],_Eb=[1,_Ea,_9],_Ec=[0,E(_9)],_Ed=[1,_Ec,_9],_Ee=function(_Ef,_Eg){var _Eh=_Ef%_Eg;if(_Ef<=0){if(_Ef>=0){return E(_Eh);}else{if(_Eg<=0){return E(_Eh);}else{var _Ei=E(_Eh);return _Ei==0?0:_Ei+_Eg|0;}}}else{if(_Eg>=0){if(_Ef>=0){return E(_Eh);}else{if(_Eg<=0){return E(_Eh);}else{var _Ej=E(_Eh);return _Ej==0?0:_Ej+_Eg|0;}}}else{var _Ek=E(_Eh);return _Ek==0?0:_Ek+_Eg|0;}}},_El=new T(function(){return B(unCStr("ACK"));}),_Em=new T(function(){return B(unCStr("BEL"));}),_En=new T(function(){return B(unCStr("BS"));}),_Eo=new T(function(){return B(unCStr("SP"));}),_Ep=[1,_Eo,_9],_Eq=new T(function(){return B(unCStr("US"));}),_Er=[1,_Eq,_Ep],_Es=new T(function(){return B(unCStr("RS"));}),_Et=[1,_Es,_Er],_Eu=new T(function(){return B(unCStr("GS"));}),_Ev=[1,_Eu,_Et],_Ew=new T(function(){return B(unCStr("FS"));}),_Ex=[1,_Ew,_Ev],_Ey=new T(function(){return B(unCStr("ESC"));}),_Ez=[1,_Ey,_Ex],_EA=new T(function(){return B(unCStr("SUB"));}),_EB=[1,_EA,_Ez],_EC=new T(function(){return B(unCStr("EM"));}),_ED=[1,_EC,_EB],_EE=new T(function(){return B(unCStr("CAN"));}),_EF=[1,_EE,_ED],_EG=new T(function(){return B(unCStr("ETB"));}),_EH=[1,_EG,_EF],_EI=new T(function(){return B(unCStr("SYN"));}),_EJ=[1,_EI,_EH],_EK=new T(function(){return B(unCStr("NAK"));}),_EL=[1,_EK,_EJ],_EM=new T(function(){return B(unCStr("DC4"));}),_EN=[1,_EM,_EL],_EO=new T(function(){return B(unCStr("DC3"));}),_EP=[1,_EO,_EN],_EQ=new T(function(){return B(unCStr("DC2"));}),_ER=[1,_EQ,_EP],_ES=new T(function(){return B(unCStr("DC1"));}),_ET=[1,_ES,_ER],_EU=new T(function(){return B(unCStr("DLE"));}),_EV=[1,_EU,_ET],_EW=new T(function(){return B(unCStr("SI"));}),_EX=[1,_EW,_EV],_EY=new T(function(){return B(unCStr("SO"));}),_EZ=[1,_EY,_EX],_F0=new T(function(){return B(unCStr("CR"));}),_F1=[1,_F0,_EZ],_F2=new T(function(){return B(unCStr("FF"));}),_F3=[1,_F2,_F1],_F4=new T(function(){return B(unCStr("VT"));}),_F5=[1,_F4,_F3],_F6=new T(function(){return B(unCStr("LF"));}),_F7=[1,_F6,_F5],_F8=new T(function(){return B(unCStr("HT"));}),_F9=[1,_F8,_F7],_Fa=[1,_En,_F9],_Fb=[1,_Em,_Fa],_Fc=[1,_El,_Fb],_Fd=new T(function(){return B(unCStr("ENQ"));}),_Fe=[1,_Fd,_Fc],_Ff=new T(function(){return B(unCStr("EOT"));}),_Fg=[1,_Ff,_Fe],_Fh=new T(function(){return B(unCStr("ETX"));}),_Fi=[1,_Fh,_Fg],_Fj=new T(function(){return B(unCStr("STX"));}),_Fk=[1,_Fj,_Fi],_Fl=new T(function(){return B(unCStr("SOH"));}),_Fm=[1,_Fl,_Fk],_Fn=new T(function(){return B(unCStr("NUL"));}),_Fo=[1,_Fn,_Fm],_Fp=[0,92],_Fq=new T(function(){return B(unCStr("\\DEL"));}),_Fr=new T(function(){return B(unCStr("\\a"));}),_Fs=new T(function(){return B(unCStr("\\\\"));}),_Ft=new T(function(){return B(unCStr("\\SO"));}),_Fu=new T(function(){return B(unCStr("\\r"));}),_Fv=new T(function(){return B(unCStr("\\f"));}),_Fw=new T(function(){return B(unCStr("\\v"));}),_Fx=new T(function(){return B(unCStr("\\n"));}),_Fy=new T(function(){return B(unCStr("\\t"));}),_Fz=new T(function(){return B(unCStr("\\b"));}),_FA=function(_FB,_FC){if(_FB<=127){var _FD=E(_FB);switch(_FD){case 92:return new F(function(){return _e(_Fs,_FC);});break;case 127:return new F(function(){return _e(_Fq,_FC);});break;default:if(_FD<32){var _FE=E(_FD);switch(_FE){case 7:return new F(function(){return _e(_Fr,_FC);});break;case 8:return new F(function(){return _e(_Fz,_FC);});break;case 9:return new F(function(){return _e(_Fy,_FC);});break;case 10:return new F(function(){return _e(_Fx,_FC);});break;case 11:return new F(function(){return _e(_Fw,_FC);});break;case 12:return new F(function(){return _e(_Fv,_FC);});break;case 13:return new F(function(){return _e(_Fu,_FC);});break;case 14:return new F(function(){return _e(_Ft,new T(function(){var _FF=E(_FC);if(!_FF[0]){var _FG=[0];}else{var _FG=E(E(_FF[1])[1])==72?B(unAppCStr("\\&",_FF)):E(_FF);}return _FG;},1));});break;default:return new F(function(){return _e([1,_Fp,new T(function(){var _FH=_FE;return _FH>=0?B(_vi(_Fo,_FH)):E(_vf);})],_FC);});}}else{return [1,[0,_FD],_FC];}}}else{return [1,_Fp,new T(function(){var _FI=jsShowI(_FB),_FJ=_FI;return B(_e(fromJSStr(_FJ),new T(function(){var _FK=E(_FC);if(!_FK[0]){var _FL=[0];}else{var _FM=E(_FK[1])[1];if(_FM<48){var _FN=E(_FK);}else{var _FN=_FM>57?E(_FK):B(unAppCStr("\\&",_FK));}var _FO=_FN,_FP=_FO,_FL=_FP;}return _FL;},1)));})];}},_FQ=new T(function(){return B(unCStr("\\\""));}),_FR=function(_FS,_FT){var _FU=E(_FS);if(!_FU[0]){return E(_FT);}else{var _FV=_FU[2],_FW=E(E(_FU[1])[1]);if(_FW==34){return new F(function(){return _e(_FQ,new T(function(){return B(_FR(_FV,_FT));},1));});}else{return new F(function(){return _FA(_FW,new T(function(){return B(_FR(_FV,_FT));}));});}}},_FX=function(_FY,_FZ,_G0,_G1,_G2,_G3,_G4,_G5,_G6,_G7){var _G8=[0,_G2,_G3,_G4];return new F(function(){return A(_FY,[new T(function(){return B(A(_FZ,[_G1]));}),function(_G9){var _Ga=E(_G9);if(!_Ga[0]){return E(new T(function(){return B(A(_G7,[[0,E(_G8),_Ed]]));}));}else{var _Gb=E(_Ga[1]),_Gc=_Gb[1],_Gd=_Gb[2];if(!B(A(_G0,[_Gc]))){return new F(function(){return A(_G7,[[0,E(_G8),[1,[0,E([1,_Ea,new T(function(){return B(_FR([1,_Gc,_9],_Eb));})])],_9]]]);});}else{var _Ge=E(_Gc);switch(E(_Ge[1])){case 9:var _Gf=[0,_G2,_G3,(_G4+8|0)-B(_Ee(_G4-1|0,8))|0];break;case 10:var _Gf=E([0,_G2,_G3+1|0,1]);break;default:var _Gf=E([0,_G2,_G3,_G4+1|0]);}var _Gg=_Gf,_Gh=[0,E(_Gg),_9],_Gi=[0,_Gd,E(_Gg),E(_G5)];return new F(function(){return A(_G6,[_Ge,_Gi,_Gh]);});}}}]);});},_Gj=function(_Gk,_Gl){return E(_Gk)[1]!=E(_Gl)[1];},_Gm=function(_Gn,_Go){return E(_Gn)[1]==E(_Go)[1];},_Gp=[0,_Gm,_Gj],_Gq=new T(function(){return B(unCStr(" 	"));}),_Gr=function(_Gs){return new F(function(){return _9r(_Gp,_Gs,_Gq);});},_Gt=function(_Gu,_Gv){return E(_Gv);},_Gw=function(_Gx){return new F(function(){return err(_Gx);});},_Gy=function(_Gz){return E(_Gz);},_GA=[0,_E7,_Gt,_Gy,_Gw],_GB=function(_GC){return E(E(_GC)[3]);},_GD=function(_GE,_GF){var _GG=E(_GF);return _GG[0]==0?B(A(_GB,[_GE,_4O])):B(A(_GB,[_GE,[1,[0,_GG[1],_GG[2]]]]));},_GH=function(_GI){return new F(function(){return _GD(_GA,_GI);});},_GJ=function(_GK,_GL,_GM,_GN,_GO){var _GP=E(_GK),_GQ=E(_GP[2]);return new F(function(){return _FX(_E7,_GH,_Gr,_GP[1],_GQ[1],_GQ[2],_GQ[3],_GP[3],_GL,_GO);});},_GR=function(_GS){return [2,E(E(_GS))];},_GT=function(_GU,_GV){switch(E(_GU)[0]){case 0:switch(E(_GV)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_GV)[0]==1?false:true;case 2:return E(_GV)[0]==2?false:true;default:return E(_GV)[0]==3?false:true;}},_GW=[2,E(_9)],_GX=function(_GY){return new F(function(){return _GT(_GW,_GY);});},_GZ=function(_H0,_H1,_H2){var _H3=E(_H2);if(!_H3[0]){return [0,_H0,[1,_GW,new T(function(){return B(_8T(_GX,_H1));})]];}else{var _H4=_H3[1],_H5=E(_H3[2]);if(!_H5[0]){var _H6=new T(function(){return [2,E(E(_H4))];});return [0,_H0,[1,_H6,new T(function(){return B(_8T(function(_GY){return new F(function(){return _GT(_H6,_GY);});},_H1));})]];}else{var _H7=new T(function(){return [2,E(E(_H4))];}),_H8=function(_H9){var _Ha=E(_H9);if(!_Ha[0]){return [0,_H0,[1,_H7,new T(function(){return B(_8T(function(_GY){return new F(function(){return _GT(_H7,_GY);});},_H1));})]];}else{var _Hb=B(_H8(_Ha[2]));return [0,_Hb[1],[1,new T(function(){return B(_GR(_Ha[1]));}),_Hb[2]]];}};return new F(function(){return (function(_Hc,_Hd){var _He=B(_H8(_Hd));return [0,_He[1],[1,new T(function(){return B(_GR(_Hc));}),_He[2]]];})(_H5[1],_H5[2]);});}}},_Hf=function(_Hg,_Hh){var _Hi=E(_Hg),_Hj=B(_GZ(_Hi[1],_Hi[2],_Hh));return [0,E(_Hj[1]),_Hj[2]];},_Hk=function(_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr){return new F(function(){return A(_Hl,[_Hn,_Ho,_Hp,function(_Hs,_Ht,_Hu){return new F(function(){return A(_Hq,[_Hs,_Ht,new T(function(){var _Hv=E(_Hu),_Hw=E(_Hv[2]);if(!_Hw[0]){var _Hx=E(_Hv);}else{var _Hy=B(_GZ(_Hv[1],_Hw,_Hm)),_Hx=[0,E(_Hy[1]),_Hy[2]];}var _Hz=_Hx;return _Hz;})]);});},function(_HA){return new F(function(){return A(_Hr,[new T(function(){return B(_Hf(_HA,_Hm));})]);});}]);});},_HB=new T(function(){return B(unCStr("digit"));}),_HC=[1,_HB,_9],_HD=function(_HE){return new F(function(){return _GD(_GA,_HE);});},_HF=function(_HG){var _HH=E(_HG)[1];return _HH<48?false:_HH<=57;},_HI=function(_HJ,_HK,_HL,_HM,_HN){var _HO=E(_HJ),_HP=E(_HO[2]);return new F(function(){return _FX(_E7,_HD,_HF,_HO[1],_HP[1],_HP[2],_HP[3],_HO[3],_HK,_HN);});},_HQ=function(_HR,_HS,_HT,_HU,_HV){return new F(function(){return _Hk(_HI,_HC,_HR,_HS,_HT,_HU,_HV);});},_HW=function(_HX,_HY,_HZ,_I0,_I1){return new F(function(){return _BT(_HQ,_HX,_HY,_HZ,_I0,_I1);});},_I2=function(_I3){return [0,_I3,function(_GY){return new F(function(){return _GD(_I3,_GY);});}];},_I4=new T(function(){return B(_I2(_GA));}),_I5=function(_I6,_I7){return function(_I8,_I9,_Ia,_Ib,_Ic){return new F(function(){return _Hk(function(_Id,_Ie,_If,_Ig,_Ih){var _Ii=E(_I6),_Ij=E(_Id),_Ik=E(_Ij[2]);return new F(function(){return _FX(E(_Ii[1])[1],_Ii[2],function(_Il){return new F(function(){return _Gm(_Il,_I7);});},_Ij[1],_Ik[1],_Ik[2],_Ik[3],_Ij[3],_Ie,_Ih);});},[1,[1,_Ea,new T(function(){return B(_FR([1,_I7,_9],_Eb));})],_9],_I8,_I9,_Ia,_Ib,_Ic);});};},_Im=[0,44],_In=new T(function(){return B(_I5(_I4,_Im));}),_Io=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_Ip=new T(function(){return B(err(_Io));}),_Iq=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_Ir=new T(function(){return B(err(_Iq));}),_Is=new T(function(){return B(_2L("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_It=function(_Iu,_Iv){while(1){var _Iw=(function(_Ix,_Iy){var _Iz=E(_Ix);switch(_Iz[0]){case 0:var _IA=E(_Iy);if(!_IA[0]){return [0];}else{_Iu=B(A(_Iz[1],[_IA[1]]));_Iv=_IA[2];return null;}break;case 1:var _IB=B(A(_Iz[1],[_Iy])),_IC=_Iy;_Iu=_IB;_Iv=_IC;return null;case 2:return [0];case 3:return [1,[0,_Iz[1],_Iy],new T(function(){return B(_It(_Iz[2],_Iy));})];default:return E(_Iz[1]);}})(_Iu,_Iv);if(_Iw!=null){return _Iw;}}},_ID=function(_IE,_IF){var _IG=function(_IH){var _II=E(_IF);if(_II[0]==3){return [3,_II[1],new T(function(){return B(_ID(_IE,_II[2]));})];}else{var _IJ=E(_IE);if(_IJ[0]==2){return E(_II);}else{var _IK=E(_II);if(_IK[0]==2){return E(_IJ);}else{var _IL=function(_IM){var _IN=E(_IK);if(_IN[0]==4){return [1,function(_IO){return [4,new T(function(){return B(_e(B(_It(_IJ,_IO)),_IN[1]));})];}];}else{var _IP=E(_IJ);if(_IP[0]==1){var _IQ=_IP[1],_IR=E(_IN);return _IR[0]==0?[1,function(_IS){return new F(function(){return _ID(B(A(_IQ,[_IS])),_IR);});}]:[1,function(_IT){return new F(function(){return _ID(B(A(_IQ,[_IT])),new T(function(){return B(A(_IR[1],[_IT]));}));});}];}else{var _IU=E(_IN);return _IU[0]==0?E(_Is):[1,function(_IV){return new F(function(){return _ID(_IP,new T(function(){return B(A(_IU[1],[_IV]));}));});}];}}},_IW=E(_IJ);switch(_IW[0]){case 1:var _IX=E(_IK);if(_IX[0]==4){return [1,function(_IY){return [4,new T(function(){return B(_e(B(_It(B(A(_IW[1],[_IY])),_IY)),_IX[1]));})];}];}else{return new F(function(){return _IL(_);});}break;case 4:var _IZ=_IW[1],_J0=E(_IK);switch(_J0[0]){case 0:return [1,function(_J1){return [4,new T(function(){return B(_e(_IZ,new T(function(){return B(_It(_J0,_J1));},1)));})];}];case 1:return [1,function(_J2){return [4,new T(function(){return B(_e(_IZ,new T(function(){return B(_It(B(A(_J0[1],[_J2])),_J2));},1)));})];}];default:return [4,new T(function(){return B(_e(_IZ,_J0[1]));})];}break;default:return new F(function(){return _IL(_);});}}}}},_J3=E(_IE);switch(_J3[0]){case 0:var _J4=E(_IF);if(!_J4[0]){return [0,function(_J5){return new F(function(){return _ID(B(A(_J3[1],[_J5])),new T(function(){return B(A(_J4[1],[_J5]));}));});}];}else{return new F(function(){return _IG(_);});}break;case 3:return [3,_J3[1],new T(function(){return B(_ID(_J3[2],_IF));})];default:return new F(function(){return _IG(_);});}},_J6=[0,41],_J7=[1,_J6,_9],_J8=[0,40],_J9=[1,_J8,_9],_Ja=function(_Jb,_Jc){var _Jd=E(_Jb);switch(_Jd[0]){case 0:return [0,function(_Je){return new F(function(){return _Ja(B(A(_Jd[1],[_Je])),_Jc);});}];case 1:return [1,function(_Jf){return new F(function(){return _Ja(B(A(_Jd[1],[_Jf])),_Jc);});}];case 2:return [2];case 3:return new F(function(){return _ID(B(A(_Jc,[_Jd[1]])),new T(function(){return B(_Ja(_Jd[2],_Jc));}));});break;default:var _Jg=function(_Jh){var _Ji=E(_Jh);if(!_Ji[0]){return [0];}else{var _Jj=E(_Ji[1]);return new F(function(){return _e(B(_It(B(A(_Jc,[_Jj[1]])),_Jj[2])),new T(function(){return B(_Jg(_Ji[2]));},1));});}},_Jk=B(_Jg(_Jd[1]));return _Jk[0]==0?[2]:[4,_Jk];}},_Jl=[2],_Jm=function(_Jn){return [3,_Jn,_Jl];},_Jo=function(_Jp,_Jq){var _Jr=E(_Jp);if(!_Jr){return new F(function(){return A(_Jq,[_6B]);});}else{return [0,function(_Js){return E(new T(function(){return B(_Jo(_Jr-1|0,_Jq));}));}];}},_Jt=function(_Ju,_Jv,_Jw){return function(_Jx){return new F(function(){return A(function(_Jy,_Jz,_JA){while(1){var _JB=(function(_JC,_JD,_JE){var _JF=E(_JC);switch(_JF[0]){case 0:var _JG=E(_JD);if(!_JG[0]){return E(_Jv);}else{_Jy=B(A(_JF[1],[_JG[1]]));_Jz=_JG[2];var _JH=_JE+1|0;_JA=_JH;return null;}break;case 1:var _JI=B(A(_JF[1],[_JD])),_JJ=_JD,_JH=_JE;_Jy=_JI;_Jz=_JJ;_JA=_JH;return null;case 2:return E(_Jv);case 3:return function(_JK){return new F(function(){return _Jo(_JE,function(_JL){return E(new T(function(){return B(_Ja(_JF,_JK));}));});});};default:return function(_md){return new F(function(){return _Ja(_JF,_md);});};}})(_Jy,_Jz,_JA);if(_JB!=null){return _JB;}}},[new T(function(){return B(A(_Ju,[_Jm]));}),_Jx,0,_Jw]);});};},_JM=function(_JN){return new F(function(){return A(_JN,[_9]);});},_JO=function(_JP,_JQ){var _JR=function(_JS){var _JT=E(_JS);if(!_JT[0]){return E(_JM);}else{var _JU=_JT[1];return !B(A(_JP,[_JU]))?E(_JM):function(_JV){return [0,function(_JW){return E(new T(function(){return B(A(new T(function(){return B(_JR(_JT[2]));}),[function(_JX){return new F(function(){return A(_JV,[[1,_JU,_JX]]);});}]));}));}];};}};return function(_JY){return new F(function(){return A(_JR,[_JY,_JQ]);});};},_JZ=[6],_K0=new T(function(){return B(unCStr("valDig: Bad base"));}),_K1=new T(function(){return B(err(_K0));}),_K2=function(_K3,_K4){var _K5=function(_K6,_K7){var _K8=E(_K6);if(!_K8[0]){return function(_K9){return new F(function(){return A(_K9,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{var _Ka=E(_K8[1])[1],_Kb=function(_Kc){return function(_Kd){return [0,function(_Ke){return E(new T(function(){return B(A(new T(function(){return B(_K5(_K8[2],function(_Kf){return new F(function(){return A(_K7,[[1,_Kc,_Kf]]);});}));}),[_Kd]));}));}];};};switch(E(E(_K3)[1])){case 8:if(48>_Ka){return function(_Kg){return new F(function(){return A(_Kg,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{if(_Ka>55){return function(_Kh){return new F(function(){return A(_Kh,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{return new F(function(){return _Kb([0,_Ka-48|0]);});}}break;case 10:if(48>_Ka){return function(_Ki){return new F(function(){return A(_Ki,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{if(_Ka>57){return function(_Kj){return new F(function(){return A(_Kj,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{return new F(function(){return _Kb([0,_Ka-48|0]);});}}break;case 16:if(48>_Ka){if(97>_Ka){if(65>_Ka){return function(_Kk){return new F(function(){return A(_Kk,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{if(_Ka>70){return function(_Kl){return new F(function(){return A(_Kl,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{return new F(function(){return _Kb([0,(_Ka-65|0)+10|0]);});}}}else{if(_Ka>102){if(65>_Ka){return function(_Km){return new F(function(){return A(_Km,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{if(_Ka>70){return function(_Kn){return new F(function(){return A(_Kn,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{return new F(function(){return _Kb([0,(_Ka-65|0)+10|0]);});}}}else{return new F(function(){return _Kb([0,(_Ka-97|0)+10|0]);});}}}else{if(_Ka>57){if(97>_Ka){if(65>_Ka){return function(_Ko){return new F(function(){return A(_Ko,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{if(_Ka>70){return function(_Kp){return new F(function(){return A(_Kp,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{return new F(function(){return _Kb([0,(_Ka-65|0)+10|0]);});}}}else{if(_Ka>102){if(65>_Ka){return function(_Kq){return new F(function(){return A(_Kq,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{if(_Ka>70){return function(_Kr){return new F(function(){return A(_Kr,[new T(function(){return B(A(_K7,[_9]));})]);});};}else{return new F(function(){return _Kb([0,(_Ka-65|0)+10|0]);});}}}else{return new F(function(){return _Kb([0,(_Ka-97|0)+10|0]);});}}}else{return new F(function(){return _Kb([0,_Ka-48|0]);});}}break;default:return E(_K1);}}};return function(_Ks){return new F(function(){return A(_K5,[_Ks,_6P,function(_Kt){var _Ku=E(_Kt);return _Ku[0]==0?[2]:B(A(_K4,[_Ku]));}]);});};},_Kv=[0,10],_Kw=[0,1],_Kx=[0,2147483647],_Ky=function(_Kz,_KA){while(1){var _KB=E(_Kz);if(!_KB[0]){var _KC=_KB[1],_KD=E(_KA);if(!_KD[0]){var _KE=_KD[1],_KF=addC(_KC,_KE);if(!E(_KF[2])){return [0,_KF[1]];}else{_Kz=[1,I_fromInt(_KC)];_KA=[1,I_fromInt(_KE)];continue;}}else{_Kz=[1,I_fromInt(_KC)];_KA=_KD;continue;}}else{var _KG=E(_KA);if(!_KG[0]){_Kz=_KB;_KA=[1,I_fromInt(_KG[1])];continue;}else{return [1,I_add(_KB[1],_KG[1])];}}}},_KH=new T(function(){return B(_Ky(_Kx,_Kw));}),_KI=function(_KJ){var _KK=E(_KJ);if(!_KK[0]){var _KL=E(_KK[1]);return _KL==(-2147483648)?E(_KH):[0, -_KL];}else{return [1,I_negate(_KK[1])];}},_KM=[0,10],_KN=[0,0],_KO=function(_KP){return [0,_KP];},_KQ=function(_KR,_KS){while(1){var _KT=E(_KR);if(!_KT[0]){var _KU=_KT[1],_KV=E(_KS);if(!_KV[0]){var _KW=_KV[1];if(!(imul(_KU,_KW)|0)){return [0,imul(_KU,_KW)|0];}else{_KR=[1,I_fromInt(_KU)];_KS=[1,I_fromInt(_KW)];continue;}}else{_KR=[1,I_fromInt(_KU)];_KS=_KV;continue;}}else{var _KX=E(_KS);if(!_KX[0]){_KR=_KT;_KS=[1,I_fromInt(_KX[1])];continue;}else{return [1,I_mul(_KT[1],_KX[1])];}}}},_KY=function(_KZ,_L0,_L1){while(1){var _L2=E(_L1);if(!_L2[0]){return E(_L0);}else{var _L3=B(_Ky(B(_KQ(_L0,_KZ)),B(_KO(E(_L2[1])[1]))));_L1=_L2[2];_L0=_L3;continue;}}},_L4=function(_L5){var _L6=new T(function(){return B(_ID(B(_ID([0,function(_L7){return E(E(_L7)[1])==45?[1,B(_K2(_Kv,function(_L8){return new F(function(){return A(_L5,[[1,new T(function(){return B(_KI(B(_KY(_KM,_KN,_L8))));})]]);});}))]:[2];}],[0,function(_L9){return E(E(_L9)[1])==43?[1,B(_K2(_Kv,function(_La){return new F(function(){return A(_L5,[[1,new T(function(){return B(_KY(_KM,_KN,_La));})]]);});}))]:[2];}])),new T(function(){return [1,B(_K2(_Kv,function(_Lb){return new F(function(){return A(_L5,[[1,new T(function(){return B(_KY(_KM,_KN,_Lb));})]]);});}))];})));});return new F(function(){return _ID([0,function(_Lc){return E(E(_Lc)[1])==101?E(_L6):[2];}],[0,function(_Ld){return E(E(_Ld)[1])==69?E(_L6):[2];}]);});},_Le=function(_Lf){return new F(function(){return A(_Lf,[_4O]);});},_Lg=function(_Lh){return new F(function(){return A(_Lh,[_4O]);});},_Li=function(_Lj){return function(_Lk){return E(E(_Lk)[1])==46?[1,B(_K2(_Kv,function(_Ll){return new F(function(){return A(_Lj,[[1,_Ll]]);});}))]:[2];};},_Lm=function(_Ln){return [0,B(_Li(_Ln))];},_Lo=function(_Lp){return new F(function(){return _K2(_Kv,function(_Lq){return [1,B(_Jt(_Lm,_Le,function(_Lr){return [1,B(_Jt(_L4,_Lg,function(_Ls){return new F(function(){return A(_Lp,[[5,[1,_Lq,_Lr,_Ls]]]);});}))];}))];});});},_Lt=function(_Lu){return [1,B(_Lo(_Lu))];},_Lv=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_Lw=function(_Lx){return new F(function(){return _9r(_Gp,_Lx,_Lv);});},_Ly=[0,8],_Lz=[0,16],_LA=function(_LB){var _LC=function(_LD){return new F(function(){return A(_LB,[[5,[0,_Ly,_LD]]]);});},_LE=function(_LF){return new F(function(){return A(_LB,[[5,[0,_Lz,_LF]]]);});};return function(_LG){return E(E(_LG)[1])==48?E([0,function(_LH){switch(E(E(_LH)[1])){case 79:return [1,B(_K2(_Ly,_LC))];case 88:return [1,B(_K2(_Lz,_LE))];case 111:return [1,B(_K2(_Ly,_LC))];case 120:return [1,B(_K2(_Lz,_LE))];default:return [2];}}]):[2];};},_LI=function(_LJ){return [0,B(_LA(_LJ))];},_LK=true,_LL=function(_LM){var _LN=new T(function(){return B(A(_LM,[_Ly]));}),_LO=new T(function(){return B(A(_LM,[_Lz]));});return function(_LP){switch(E(E(_LP)[1])){case 79:return E(_LN);case 88:return E(_LO);case 111:return E(_LN);case 120:return E(_LO);default:return [2];}};},_LQ=function(_LR){return [0,B(_LL(_LR))];},_LS=[0,92],_LT=function(_LU){return new F(function(){return A(_LU,[_Kv]);});},_LV=function(_LW){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_LW,_9));}))));});},_LX=function(_LY){var _LZ=E(_LY);return _LZ[0]==0?E(_LZ[1]):I_toInt(_LZ[1]);},_M0=function(_M1,_M2){var _M3=E(_M1);if(!_M3[0]){var _M4=_M3[1],_M5=E(_M2);return _M5[0]==0?_M4<=_M5[1]:I_compareInt(_M5[1],_M4)>=0;}else{var _M6=_M3[1],_M7=E(_M2);return _M7[0]==0?I_compareInt(_M6,_M7[1])<=0:I_compare(_M6,_M7[1])<=0;}},_M8=function(_M9){return [2];},_Ma=function(_Mb){var _Mc=E(_Mb);if(!_Mc[0]){return E(_M8);}else{var _Md=_Mc[1],_Me=E(_Mc[2]);return _Me[0]==0?E(_Md):function(_Mf){return new F(function(){return _ID(B(A(_Md,[_Mf])),new T(function(){return B(A(new T(function(){return B(_Ma(_Me));}),[_Mf]));}));});};}},_Mg=function(_Mh){return [2];},_Mi=function(_Mj,_Mk){var _Ml=function(_Mm,_Mn){var _Mo=E(_Mm);if(!_Mo[0]){return function(_Mp){return new F(function(){return A(_Mp,[_Mj]);});};}else{var _Mq=E(_Mn);return _Mq[0]==0?E(_Mg):E(_Mo[1])[1]!=E(_Mq[1])[1]?E(_Mg):function(_Mr){return [0,function(_Ms){return E(new T(function(){return B(A(new T(function(){return B(_Ml(_Mo[2],_Mq[2]));}),[_Mr]));}));}];};}};return function(_Mt){return new F(function(){return A(_Ml,[_Mj,_Mt,_Mk]);});};},_Mu=new T(function(){return B(unCStr("SOH"));}),_Mv=[0,1],_Mw=function(_Mx){return [1,B(_Mi(_Mu,function(_My){return E(new T(function(){return B(A(_Mx,[_Mv]));}));}))];},_Mz=new T(function(){return B(unCStr("SO"));}),_MA=[0,14],_MB=function(_MC){return [1,B(_Mi(_Mz,function(_MD){return E(new T(function(){return B(A(_MC,[_MA]));}));}))];},_ME=function(_MF){return [1,B(_Jt(_Mw,_MB,_MF))];},_MG=new T(function(){return B(unCStr("NUL"));}),_MH=[0,0],_MI=function(_MJ){return [1,B(_Mi(_MG,function(_MK){return E(new T(function(){return B(A(_MJ,[_MH]));}));}))];},_ML=new T(function(){return B(unCStr("STX"));}),_MM=[0,2],_MN=function(_MO){return [1,B(_Mi(_ML,function(_MP){return E(new T(function(){return B(A(_MO,[_MM]));}));}))];},_MQ=new T(function(){return B(unCStr("ETX"));}),_MR=[0,3],_MS=function(_MT){return [1,B(_Mi(_MQ,function(_MU){return E(new T(function(){return B(A(_MT,[_MR]));}));}))];},_MV=new T(function(){return B(unCStr("EOT"));}),_MW=[0,4],_MX=function(_MY){return [1,B(_Mi(_MV,function(_MZ){return E(new T(function(){return B(A(_MY,[_MW]));}));}))];},_N0=new T(function(){return B(unCStr("ENQ"));}),_N1=[0,5],_N2=function(_N3){return [1,B(_Mi(_N0,function(_N4){return E(new T(function(){return B(A(_N3,[_N1]));}));}))];},_N5=new T(function(){return B(unCStr("ACK"));}),_N6=[0,6],_N7=function(_N8){return [1,B(_Mi(_N5,function(_N9){return E(new T(function(){return B(A(_N8,[_N6]));}));}))];},_Na=new T(function(){return B(unCStr("BEL"));}),_Nb=[0,7],_Nc=function(_Nd){return [1,B(_Mi(_Na,function(_Ne){return E(new T(function(){return B(A(_Nd,[_Nb]));}));}))];},_Nf=new T(function(){return B(unCStr("BS"));}),_Ng=[0,8],_Nh=function(_Ni){return [1,B(_Mi(_Nf,function(_Nj){return E(new T(function(){return B(A(_Ni,[_Ng]));}));}))];},_Nk=new T(function(){return B(unCStr("HT"));}),_Nl=[0,9],_Nm=function(_Nn){return [1,B(_Mi(_Nk,function(_No){return E(new T(function(){return B(A(_Nn,[_Nl]));}));}))];},_Np=new T(function(){return B(unCStr("LF"));}),_Nq=[0,10],_Nr=function(_Ns){return [1,B(_Mi(_Np,function(_Nt){return E(new T(function(){return B(A(_Ns,[_Nq]));}));}))];},_Nu=new T(function(){return B(unCStr("VT"));}),_Nv=[0,11],_Nw=function(_Nx){return [1,B(_Mi(_Nu,function(_Ny){return E(new T(function(){return B(A(_Nx,[_Nv]));}));}))];},_Nz=new T(function(){return B(unCStr("FF"));}),_NA=[0,12],_NB=function(_NC){return [1,B(_Mi(_Nz,function(_ND){return E(new T(function(){return B(A(_NC,[_NA]));}));}))];},_NE=new T(function(){return B(unCStr("CR"));}),_NF=[0,13],_NG=function(_NH){return [1,B(_Mi(_NE,function(_NI){return E(new T(function(){return B(A(_NH,[_NF]));}));}))];},_NJ=new T(function(){return B(unCStr("SI"));}),_NK=[0,15],_NL=function(_NM){return [1,B(_Mi(_NJ,function(_NN){return E(new T(function(){return B(A(_NM,[_NK]));}));}))];},_NO=new T(function(){return B(unCStr("DLE"));}),_NP=[0,16],_NQ=function(_NR){return [1,B(_Mi(_NO,function(_NS){return E(new T(function(){return B(A(_NR,[_NP]));}));}))];},_NT=new T(function(){return B(unCStr("DC1"));}),_NU=[0,17],_NV=function(_NW){return [1,B(_Mi(_NT,function(_NX){return E(new T(function(){return B(A(_NW,[_NU]));}));}))];},_NY=new T(function(){return B(unCStr("DC2"));}),_NZ=[0,18],_O0=function(_O1){return [1,B(_Mi(_NY,function(_O2){return E(new T(function(){return B(A(_O1,[_NZ]));}));}))];},_O3=new T(function(){return B(unCStr("DC3"));}),_O4=[0,19],_O5=function(_O6){return [1,B(_Mi(_O3,function(_O7){return E(new T(function(){return B(A(_O6,[_O4]));}));}))];},_O8=new T(function(){return B(unCStr("DC4"));}),_O9=[0,20],_Oa=function(_Ob){return [1,B(_Mi(_O8,function(_Oc){return E(new T(function(){return B(A(_Ob,[_O9]));}));}))];},_Od=new T(function(){return B(unCStr("NAK"));}),_Oe=[0,21],_Of=function(_Og){return [1,B(_Mi(_Od,function(_Oh){return E(new T(function(){return B(A(_Og,[_Oe]));}));}))];},_Oi=new T(function(){return B(unCStr("SYN"));}),_Oj=[0,22],_Ok=function(_Ol){return [1,B(_Mi(_Oi,function(_Om){return E(new T(function(){return B(A(_Ol,[_Oj]));}));}))];},_On=new T(function(){return B(unCStr("ETB"));}),_Oo=[0,23],_Op=function(_Oq){return [1,B(_Mi(_On,function(_Or){return E(new T(function(){return B(A(_Oq,[_Oo]));}));}))];},_Os=new T(function(){return B(unCStr("CAN"));}),_Ot=[0,24],_Ou=function(_Ov){return [1,B(_Mi(_Os,function(_Ow){return E(new T(function(){return B(A(_Ov,[_Ot]));}));}))];},_Ox=new T(function(){return B(unCStr("EM"));}),_Oy=[0,25],_Oz=function(_OA){return [1,B(_Mi(_Ox,function(_OB){return E(new T(function(){return B(A(_OA,[_Oy]));}));}))];},_OC=new T(function(){return B(unCStr("SUB"));}),_OD=[0,26],_OE=function(_OF){return [1,B(_Mi(_OC,function(_OG){return E(new T(function(){return B(A(_OF,[_OD]));}));}))];},_OH=new T(function(){return B(unCStr("ESC"));}),_OI=[0,27],_OJ=function(_OK){return [1,B(_Mi(_OH,function(_OL){return E(new T(function(){return B(A(_OK,[_OI]));}));}))];},_OM=new T(function(){return B(unCStr("FS"));}),_ON=[0,28],_OO=function(_OP){return [1,B(_Mi(_OM,function(_OQ){return E(new T(function(){return B(A(_OP,[_ON]));}));}))];},_OR=new T(function(){return B(unCStr("GS"));}),_OS=[0,29],_OT=function(_OU){return [1,B(_Mi(_OR,function(_OV){return E(new T(function(){return B(A(_OU,[_OS]));}));}))];},_OW=new T(function(){return B(unCStr("RS"));}),_OX=[0,30],_OY=function(_OZ){return [1,B(_Mi(_OW,function(_P0){return E(new T(function(){return B(A(_OZ,[_OX]));}));}))];},_P1=new T(function(){return B(unCStr("US"));}),_P2=[0,31],_P3=function(_P4){return [1,B(_Mi(_P1,function(_P5){return E(new T(function(){return B(A(_P4,[_P2]));}));}))];},_P6=new T(function(){return B(unCStr("SP"));}),_P7=[0,32],_P8=function(_P9){return [1,B(_Mi(_P6,function(_Pa){return E(new T(function(){return B(A(_P9,[_P7]));}));}))];},_Pb=new T(function(){return B(unCStr("DEL"));}),_Pc=[0,127],_Pd=function(_Pe){return [1,B(_Mi(_Pb,function(_Pf){return E(new T(function(){return B(A(_Pe,[_Pc]));}));}))];},_Pg=[1,_Pd,_9],_Ph=[1,_P8,_Pg],_Pi=[1,_P3,_Ph],_Pj=[1,_OY,_Pi],_Pk=[1,_OT,_Pj],_Pl=[1,_OO,_Pk],_Pm=[1,_OJ,_Pl],_Pn=[1,_OE,_Pm],_Po=[1,_Oz,_Pn],_Pp=[1,_Ou,_Po],_Pq=[1,_Op,_Pp],_Pr=[1,_Ok,_Pq],_Ps=[1,_Of,_Pr],_Pt=[1,_Oa,_Ps],_Pu=[1,_O5,_Pt],_Pv=[1,_O0,_Pu],_Pw=[1,_NV,_Pv],_Px=[1,_NQ,_Pw],_Py=[1,_NL,_Px],_Pz=[1,_NG,_Py],_PA=[1,_NB,_Pz],_PB=[1,_Nw,_PA],_PC=[1,_Nr,_PB],_PD=[1,_Nm,_PC],_PE=[1,_Nh,_PD],_PF=[1,_Nc,_PE],_PG=[1,_N7,_PF],_PH=[1,_N2,_PG],_PI=[1,_MX,_PH],_PJ=[1,_MS,_PI],_PK=[1,_MN,_PJ],_PL=[1,_MI,_PK],_PM=[1,_ME,_PL],_PN=new T(function(){return B(_Ma(_PM));}),_PO=[0,1114111],_PP=[0,34],_PQ=[0,39],_PR=function(_PS){var _PT=new T(function(){return B(A(_PS,[_Nb]));}),_PU=new T(function(){return B(A(_PS,[_Ng]));}),_PV=new T(function(){return B(A(_PS,[_Nl]));}),_PW=new T(function(){return B(A(_PS,[_Nq]));}),_PX=new T(function(){return B(A(_PS,[_Nv]));}),_PY=new T(function(){return B(A(_PS,[_NA]));}),_PZ=new T(function(){return B(A(_PS,[_NF]));});return new F(function(){return _ID([0,function(_Q0){switch(E(E(_Q0)[1])){case 34:return E(new T(function(){return B(A(_PS,[_PP]));}));case 39:return E(new T(function(){return B(A(_PS,[_PQ]));}));case 92:return E(new T(function(){return B(A(_PS,[_LS]));}));case 97:return E(_PT);case 98:return E(_PU);case 102:return E(_PY);case 110:return E(_PW);case 114:return E(_PZ);case 116:return E(_PV);case 118:return E(_PX);default:return [2];}}],new T(function(){return B(_ID([1,B(_Jt(_LQ,_LT,function(_Q1){return [1,B(_K2(_Q1,function(_Q2){var _Q3=B(_KY(new T(function(){return B(_KO(E(_Q1)[1]));}),_KN,_Q2));return !B(_M0(_Q3,_PO))?[2]:B(A(_PS,[new T(function(){var _Q4=B(_LX(_Q3));if(_Q4>>>0>1114111){var _Q5=B(_LV(_Q4));}else{var _Q5=[0,_Q4];}var _Q6=_Q5,_Q7=_Q6,_Q8=_Q7;return _Q8;})]));}))];}))],new T(function(){return B(_ID([0,function(_Q9){return E(E(_Q9)[1])==94?E([0,function(_Qa){switch(E(E(_Qa)[1])){case 64:return E(new T(function(){return B(A(_PS,[_MH]));}));case 65:return E(new T(function(){return B(A(_PS,[_Mv]));}));case 66:return E(new T(function(){return B(A(_PS,[_MM]));}));case 67:return E(new T(function(){return B(A(_PS,[_MR]));}));case 68:return E(new T(function(){return B(A(_PS,[_MW]));}));case 69:return E(new T(function(){return B(A(_PS,[_N1]));}));case 70:return E(new T(function(){return B(A(_PS,[_N6]));}));case 71:return E(_PT);case 72:return E(_PU);case 73:return E(_PV);case 74:return E(_PW);case 75:return E(_PX);case 76:return E(_PY);case 77:return E(_PZ);case 78:return E(new T(function(){return B(A(_PS,[_MA]));}));case 79:return E(new T(function(){return B(A(_PS,[_NK]));}));case 80:return E(new T(function(){return B(A(_PS,[_NP]));}));case 81:return E(new T(function(){return B(A(_PS,[_NU]));}));case 82:return E(new T(function(){return B(A(_PS,[_NZ]));}));case 83:return E(new T(function(){return B(A(_PS,[_O4]));}));case 84:return E(new T(function(){return B(A(_PS,[_O9]));}));case 85:return E(new T(function(){return B(A(_PS,[_Oe]));}));case 86:return E(new T(function(){return B(A(_PS,[_Oj]));}));case 87:return E(new T(function(){return B(A(_PS,[_Oo]));}));case 88:return E(new T(function(){return B(A(_PS,[_Ot]));}));case 89:return E(new T(function(){return B(A(_PS,[_Oy]));}));case 90:return E(new T(function(){return B(A(_PS,[_OD]));}));case 91:return E(new T(function(){return B(A(_PS,[_OI]));}));case 92:return E(new T(function(){return B(A(_PS,[_ON]));}));case 93:return E(new T(function(){return B(A(_PS,[_OS]));}));case 94:return E(new T(function(){return B(A(_PS,[_OX]));}));case 95:return E(new T(function(){return B(A(_PS,[_P2]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_PN,[_PS]));})));})));}));});},_Qb=function(_Qc){return new F(function(){return A(_Qc,[_6B]);});},_Qd=function(_Qe){var _Qf=E(_Qe);if(!_Qf[0]){return E(_Qb);}else{var _Qg=_Qf[2],_Qh=E(E(_Qf[1])[1]);switch(_Qh){case 9:return function(_Qi){return [0,function(_Qj){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qi]));}));}];};case 10:return function(_Qk){return [0,function(_Ql){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qk]));}));}];};case 11:return function(_Qm){return [0,function(_Qn){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qm]));}));}];};case 12:return function(_Qo){return [0,function(_Qp){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qo]));}));}];};case 13:return function(_Qq){return [0,function(_Qr){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qq]));}));}];};case 32:return function(_Qs){return [0,function(_Qt){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qs]));}));}];};case 160:return function(_Qu){return [0,function(_Qv){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qu]));}));}];};default:var _Qw=u_iswspace(_Qh),_Qx=_Qw;return E(_Qx)==0?E(_Qb):function(_Qy){return [0,function(_Qz){return E(new T(function(){return B(A(new T(function(){return B(_Qd(_Qg));}),[_Qy]));}));}];};}}},_QA=function(_QB){var _QC=new T(function(){return B(_QA(_QB));}),_QD=[1,function(_QE){return new F(function(){return A(_Qd,[_QE,function(_QF){return E([0,function(_QG){return E(E(_QG)[1])==92?E(_QC):[2];}]);}]);});}];return new F(function(){return _ID([0,function(_QH){return E(E(_QH)[1])==92?E([0,function(_QI){var _QJ=E(E(_QI)[1]);switch(_QJ){case 9:return E(_QD);case 10:return E(_QD);case 11:return E(_QD);case 12:return E(_QD);case 13:return E(_QD);case 32:return E(_QD);case 38:return E(_QC);case 160:return E(_QD);default:var _QK=u_iswspace(_QJ),_QL=_QK;return E(_QL)==0?[2]:E(_QD);}}]):[2];}],[0,function(_QM){var _QN=E(_QM);return E(_QN[1])==92?E(new T(function(){return B(_PR(function(_QO){return new F(function(){return A(_QB,[[0,_QO,_LK]]);});}));})):B(A(_QB,[[0,_QN,_4y]]));}]);});},_QP=function(_QQ,_QR){return new F(function(){return _QA(function(_QS){var _QT=E(_QS),_QU=E(_QT[1]);if(E(_QU[1])==34){if(!E(_QT[2])){return E(new T(function(){return B(A(_QR,[[1,new T(function(){return B(A(_QQ,[_9]));})]]));}));}else{return new F(function(){return _QP(function(_QV){return new F(function(){return A(_QQ,[[1,_QU,_QV]]);});},_QR);});}}else{return new F(function(){return _QP(function(_QW){return new F(function(){return A(_QQ,[[1,_QU,_QW]]);});},_QR);});}});});},_QX=new T(function(){return B(unCStr("_\'"));}),_QY=function(_QZ){var _R0=u_iswalnum(_QZ),_R1=_R0;return E(_R1)==0?B(_9r(_Gp,[0,_QZ],_QX)):true;},_R2=function(_R3){return new F(function(){return _QY(E(_R3)[1]);});},_R4=new T(function(){return B(unCStr(",;()[]{}`"));}),_R5=new T(function(){return B(unCStr(".."));}),_R6=new T(function(){return B(unCStr("::"));}),_R7=new T(function(){return B(unCStr("->"));}),_R8=[0,64],_R9=[1,_R8,_9],_Ra=[0,126],_Rb=[1,_Ra,_9],_Rc=new T(function(){return B(unCStr("=>"));}),_Rd=[1,_Rc,_9],_Re=[1,_Rb,_Rd],_Rf=[1,_R9,_Re],_Rg=[1,_R7,_Rf],_Rh=new T(function(){return B(unCStr("<-"));}),_Ri=[1,_Rh,_Rg],_Rj=[0,124],_Rk=[1,_Rj,_9],_Rl=[1,_Rk,_Ri],_Rm=[1,_LS,_9],_Rn=[1,_Rm,_Rl],_Ro=[0,61],_Rp=[1,_Ro,_9],_Rq=[1,_Rp,_Rn],_Rr=[1,_R6,_Rq],_Rs=[1,_R5,_Rr],_Rt=function(_Ru){return new F(function(){return _ID([1,function(_Rv){return E(_Rv)[0]==0?E(new T(function(){return B(A(_Ru,[_JZ]));})):[2];}],new T(function(){return B(_ID([0,function(_Rw){return E(E(_Rw)[1])==39?E([0,function(_Rx){var _Ry=E(_Rx);switch(E(_Ry[1])){case 39:return [2];case 92:return E(new T(function(){return B(_PR(function(_Rz){return [0,function(_RA){return E(E(_RA)[1])==39?E(new T(function(){return B(A(_Ru,[[0,_Rz]]));})):[2];}];}));}));default:return [0,function(_RB){return E(E(_RB)[1])==39?E(new T(function(){return B(A(_Ru,[[0,_Ry]]));})):[2];}];}}]):[2];}],new T(function(){return B(_ID([0,function(_RC){return E(E(_RC)[1])==34?E(new T(function(){return B(_QP(_6P,_Ru));})):[2];}],new T(function(){return B(_ID([0,function(_RD){return !B(_9r(_Gp,_RD,_R4))?[2]:B(A(_Ru,[[2,[1,_RD,_9]]]));}],new T(function(){return B(_ID([0,function(_RE){return !B(_9r(_Gp,_RE,_Lv))?[2]:[1,B(_JO(_Lw,function(_RF){var _RG=[1,_RE,_RF];return !B(_9r(_8H,_RG,_Rs))?B(A(_Ru,[[4,_RG]])):B(A(_Ru,[[2,_RG]]));}))];}],new T(function(){return B(_ID([0,function(_RH){var _RI=E(_RH),_RJ=_RI[1],_RK=u_iswalpha(_RJ),_RL=_RK;return E(_RL)==0?E(_RJ)==95?[1,B(_JO(_R2,function(_RM){return new F(function(){return A(_Ru,[[3,[1,_RI,_RM]]]);});}))]:[2]:[1,B(_JO(_R2,function(_RN){return new F(function(){return A(_Ru,[[3,[1,_RI,_RN]]]);});}))];}],new T(function(){return [1,B(_Jt(_LI,_Lt,_Ru))];})));})));})));})));})));}));});},_RO=[0,0],_RP=function(_RQ,_RR){return function(_RS){return new F(function(){return A(_Qd,[_RS,function(_RT){return E(new T(function(){return B(_Rt(function(_RU){var _RV=E(_RU);return _RV[0]==2?!B(_3x(_RV[1],_J9))?[2]:E(new T(function(){return B(A(_RQ,[_RO,function(_RW){return [1,function(_RX){return new F(function(){return A(_Qd,[_RX,function(_RY){return E(new T(function(){return B(_Rt(function(_RZ){var _S0=E(_RZ);return _S0[0]==2?!B(_3x(_S0[1],_J7))?[2]:E(new T(function(){return B(A(_RR,[_RW]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_S1=function(_S2,_S3,_S4){var _S5=function(_S6,_S7){return new F(function(){return _ID([1,function(_S8){return new F(function(){return A(_Qd,[_S8,function(_S9){return E(new T(function(){return B(_Rt(function(_Sa){var _Sb=E(_Sa);if(_Sb[0]==4){var _Sc=E(_Sb[1]);if(!_Sc[0]){return new F(function(){return A(_S2,[_Sb,_S6,_S7]);});}else{return E(E(_Sc[1])[1])==45?E(_Sc[2])[0]==0?E([1,function(_Sd){return new F(function(){return A(_Qd,[_Sd,function(_Se){return E(new T(function(){return B(_Rt(function(_Sf){return new F(function(){return A(_S2,[_Sf,_S6,function(_Sg){return new F(function(){return A(_S7,[new T(function(){return [0, -E(_Sg)[1]];})]);});}]);});}));}));}]);});}]):B(A(_S2,[_Sb,_S6,_S7])):B(A(_S2,[_Sb,_S6,_S7]));}}else{return new F(function(){return A(_S2,[_Sb,_S6,_S7]);});}}));}));}]);});}],new T(function(){return [1,B(_RP(_S5,_S7))];}));});};return new F(function(){return _S5(_S3,_S4);});},_Sh=function(_Si,_Sj){return [2];},_Sk=function(_Sl){var _Sm=E(_Sl);return _Sm[0]==0?[1,new T(function(){return B(_KY(new T(function(){return B(_KO(E(_Sm[1])[1]));}),_KN,_Sm[2]));})]:E(_Sm[2])[0]==0?E(_Sm[3])[0]==0?[1,new T(function(){return B(_KY(_KM,_KN,_Sm[1]));})]:[0]:[0];},_Sn=function(_So){var _Sp=E(_So);if(_Sp[0]==5){var _Sq=B(_Sk(_Sp[1]));return _Sq[0]==0?E(_Sh):function(_Sr,_Ss){return new F(function(){return A(_Ss,[new T(function(){return [0,B(_LX(_Sq[1]))];})]);});};}else{return E(_Sh);}},_St=function(_Su){return [1,function(_Sv){return new F(function(){return A(_Qd,[_Sv,function(_Sw){return E([3,_Su,_Jl]);}]);});}];},_Sx=new T(function(){return B(_S1(_Sn,_RO,_St));}),_Sy=function(_Sz){while(1){var _SA=(function(_SB){var _SC=E(_SB);if(!_SC[0]){return [0];}else{var _SD=_SC[2],_SE=E(_SC[1]);if(!E(_SE[2])[0]){return [1,_SE[1],new T(function(){return B(_Sy(_SD));})];}else{_Sz=_SD;return null;}}})(_Sz);if(_SA!=null){return _SA;}}},_SF=function(_SG){var _SH=B(_Sy(B(_It(_Sx,_SG))));return _SH[0]==0?E(_Ip):E(_SH[2])[0]==0?E(_SH[1]):E(_Ir);},_SI=function(_SJ,_SK,_SL,_SM,_SN){var _SO=function(_SP,_SQ,_SR){var _SS=function(_ST,_SU,_SV){return new F(function(){return A(_SR,[[0,_SJ,new T(function(){return B(_3d(_SF,_ST));})],_SU,new T(function(){var _SW=E(E(_SU)[2]),_SX=E(_SV),_SY=E(_SX[1]),_SZ=B(_B1(_SY[1],_SY[2],_SY[3],_SX[2],_SW[1],_SW[2],_SW[3],_9));return [0,E(_SZ[1]),_SZ[2]];})]);});},_T0=function(_T1){return new F(function(){return _SS(_9,_SP,new T(function(){var _T2=E(E(_SP)[2]),_T3=E(_T1),_T4=E(_T3[1]),_T5=B(_B1(_T4[1],_T4[2],_T4[3],_T3[2],_T2[1],_T2[2],_T2[3],_9));return [0,E(_T5[1]),_T5[2]];},1));});};return new F(function(){return _CW(_HW,_In,_SP,function(_T6,_T7,_T8){return new F(function(){return A(_SQ,[[0,_SJ,new T(function(){return B(_3d(_SF,_T6));})],_T7,new T(function(){var _T9=E(E(_T7)[2]),_Ta=E(_T8),_Tb=E(_Ta[1]),_Tc=B(_B1(_Tb[1],_Tb[2],_Tb[3],_Ta[2],_T9[1],_T9[2],_T9[3],_9));return [0,E(_Tc[1]),_Tc[2]];})]);});},_T0,_SS,_T0);});};return new F(function(){return _Cw(_GJ,_SK,function(_Td,_Te,_Tf){return new F(function(){return _SO(_Te,_SL,function(_Tg,_Th,_Ti){return new F(function(){return A(_SL,[_Tg,_Th,new T(function(){return B(_BL(_Tf,_Ti));})]);});});});},_SM,function(_Tj,_Tk,_Tl){return new F(function(){return _SO(_Tk,_SL,function(_Tm,_Tn,_To){return new F(function(){return A(_SN,[_Tm,_Tn,new T(function(){return B(_BL(_Tl,_To));})]);});});});});});},_Tp=new T(function(){return B(unCStr("letter or digit"));}),_Tq=[1,_Tp,_9],_Tr=function(_Ts){var _Tt=u_iswalnum(E(_Ts)[1]),_Tu=_Tt;return E(_Tu)==0?false:true;},_Tv=function(_Tw,_Tx,_Ty,_Tz,_TA){var _TB=E(_Tw),_TC=E(_TB[2]);return new F(function(){return _FX(_E7,_HD,_Tr,_TB[1],_TC[1],_TC[2],_TC[3],_TB[3],_Tx,_TA);});},_TD=function(_TE,_TF,_TG,_TH,_TI){return new F(function(){return _Hk(_Tv,_Tq,_TE,_TF,_TG,_TH,_TI);});},_TJ=function(_TK,_TL,_TM,_TN,_TO){return new F(function(){return _BT(_TD,_TK,function(_TP,_TQ,_TR){return new F(function(){return _SI(_TP,_TQ,_TL,_TM,function(_TS,_TT,_TU){return new F(function(){return A(_TL,[_TS,_TT,new T(function(){return B(_BL(_TR,_TU));})]);});});});},_TO,function(_TV,_TW,_TX){return new F(function(){return _SI(_TV,_TW,_TL,_TM,function(_TY,_TZ,_U0){return new F(function(){return A(_TN,[_TY,_TZ,new T(function(){return B(_BL(_TX,_U0));})]);});});});},_TO);});},_U1=new T(function(){return B(unCStr("SHOW"));}),_U2=[0,_U1,_9],_U3=function(_U4,_U5,_U6,_U7){var _U8=function(_U9){return new F(function(){return A(_U7,[[0,_U4,_U2],_U5,new T(function(){var _Ua=E(E(_U5)[2]),_Ub=_Ua[1],_Uc=_Ua[2],_Ud=_Ua[3],_Ue=E(_U9),_Uf=E(_Ue[1]),_Ug=B(_B1(_Uf[1],_Uf[2],_Uf[3],_Ue[2],_Ub,_Uc,_Ud,_9)),_Uh=E(_Ug[1]),_Ui=B(_B1(_Uh[1],_Uh[2],_Uh[3],_Ug[2],_Ub,_Uc,_Ud,_9));return [0,E(_Ui[1]),_Ui[2]];})]);});};return new F(function(){return _TJ(_U5,function(_Uj,_Uk,_Ul){return new F(function(){return A(_U6,[[0,_U4,_Uj],_Uk,new T(function(){var _Um=E(E(_Uk)[2]),_Un=E(_Ul),_Uo=E(_Un[1]),_Up=B(_B1(_Uo[1],_Uo[2],_Uo[3],_Un[2],_Um[1],_Um[2],_Um[3],_9));return [0,E(_Up[1]),_Up[2]];})]);});},_U8,function(_Uq,_Ur,_Us){return new F(function(){return A(_U7,[[0,_U4,_Uq],_Ur,new T(function(){var _Ut=E(E(_Ur)[2]),_Uu=E(_Us),_Uv=E(_Uu[1]),_Uw=B(_B1(_Uv[1],_Uv[2],_Uv[3],_Uu[2],_Ut[1],_Ut[2],_Ut[3],_9));return [0,E(_Uw[1]),_Uw[2]];})]);});},_U8);});},_Ux=new T(function(){return B(unCStr("sS"));}),_Uy=new T(function(){return B(_I2(_GA));}),_Uz=[0,58],_UA=new T(function(){return B(_I5(_Uy,_Uz));}),_UB=[1,_Tp,_9],_UC=function(_UD,_UE,_UF,_UG,_UH,_UI,_UJ,_UK,_UL){var _UM=function(_UN){var _UO=new T(function(){var _UP=E(_UN),_UQ=B(_GZ(_UP[1],_UP[2],_UB));return [0,E(_UQ[1]),_UQ[2]];});return new F(function(){return A(_UA,[[0,_UD,E([0,_UE,_UF,_UG]),E(_UH)],_UI,_UJ,function(_UR,_US,_UT){return new F(function(){return A(_UK,[_UR,_US,new T(function(){return B(_BL(_UO,_UT));})]);});},function(_UU){return new F(function(){return A(_UL,[new T(function(){return B(_BL(_UO,_UU));})]);});}]);});},_UV=E(_UD);if(!_UV[0]){return new F(function(){return _UM([0,E([0,_UE,_UF,_UG]),_Ed]);});}else{var _UW=_UV[2],_UX=E(_UV[1]),_UY=_UX[1],_UZ=u_iswalnum(_UY),_V0=_UZ;if(!E(_V0)){return new F(function(){return _UM([0,E([0,_UE,_UF,_UG]),[1,[0,E([1,_Ea,new T(function(){return B(_FR([1,_UX,_9],_Eb));})])],_9]]);});}else{switch(E(_UY)){case 9:var _V1=[0,_UE,_UF,(_UG+8|0)-B(_Ee(_UG-1|0,8))|0];break;case 10:var _V1=[0,_UE,_UF+1|0,1];break;default:var _V1=[0,_UE,_UF,_UG+1|0];}var _V2=_V1,_V3=[0,E(_V2),_9],_V4=[0,_UW,E(_V2),E(_UH)];return new F(function(){return A(_UI,[_UX,_V4,_V3]);});}}},_V5=function(_V6,_V7,_V8,_V9,_Va){var _Vb=E(_V6),_Vc=E(_Vb[2]);return new F(function(){return _UC(_Vb[1],_Vc[1],_Vc[2],_Vc[3],_Vb[3],_V7,_V8,_V9,_Va);});},_Vd=[0,10],_Ve=new T(function(){return B(unCStr("lf new-line"));}),_Vf=[1,_Ve,_9],_Vg=function(_Vh){return function(_Vi,_Vj,_Vk,_Vl,_Vm){return new F(function(){return _Hk(new T(function(){return B(_I5(_Vh,_Vd));}),_Vf,_Vi,_Vj,_Vk,_Vl,_Vm);});};},_Vn=new T(function(){return B(_Vg(_Uy));}),_Vo=function(_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv){var _Vw=function(_Vx,_Vy,_Vz,_VA,_VB,_VC){return new F(function(){return _VD(_Vy,function(_VE,_VF,_VG){return new F(function(){return A(_Vz,[[1,_Vx,_VE],_VF,new T(function(){var _VH=E(E(_VF)[2]),_VI=E(_VG),_VJ=E(_VI[1]),_VK=B(_B1(_VJ[1],_VJ[2],_VJ[3],_VI[2],_VH[1],_VH[2],_VH[3],_9));return [0,E(_VK[1]),_VK[2]];})]);});},_VA,function(_VL,_VM,_VN){return new F(function(){return A(_VB,[[1,_Vx,_VL],_VM,new T(function(){var _VO=E(E(_VM)[2]),_VP=E(_VN),_VQ=E(_VP[1]),_VR=B(_B1(_VQ[1],_VQ[2],_VQ[3],_VP[2],_VO[1],_VO[2],_VO[3],_9));return [0,E(_VR[1]),_VR[2]];})]);});},_VC);});},_VD=function(_VS,_VT,_VU,_VV,_VW){return new F(function(){return A(_Vq,[_VS,function(_VX,_VY,_VZ){return new F(function(){return A(_VT,[_9,_VY,new T(function(){var _W0=E(E(_VY)[2]),_W1=E(_VZ),_W2=E(_W1[1]),_W3=B(_B1(_W2[1],_W2[2],_W2[3],_W1[2],_W0[1],_W0[2],_W0[3],_9));return [0,E(_W3[1]),_W3[2]];})]);});},_VU,function(_W4,_W5,_W6){return new F(function(){return A(_VV,[_9,_W5,new T(function(){var _W7=E(E(_W5)[2]),_W8=E(_W6),_W9=E(_W8[1]),_Wa=B(_B1(_W9[1],_W9[2],_W9[3],_W8[2],_W7[1],_W7[2],_W7[3],_9));return [0,E(_Wa[1]),_Wa[2]];})]);});},function(_Wb){return new F(function(){return A(_Vp,[_VS,function(_Wc,_Wd,_We){return new F(function(){return _Vw(_Wc,_Wd,_VT,_VU,function(_Wf,_Wg,_Wh){return new F(function(){return A(_VT,[_Wf,_Wg,new T(function(){return B(_BL(_We,_Wh));})]);});},function(_Wi){return new F(function(){return A(_VU,[new T(function(){return B(_BL(_We,_Wi));})]);});});});},_VU,function(_Wj,_Wk,_Wl){return new F(function(){return _Vw(_Wj,_Wk,_VT,_VU,function(_Wm,_Wn,_Wo){return new F(function(){return A(_VV,[_Wm,_Wn,new T(function(){var _Wp=E(_Wb),_Wq=E(_Wp[1]),_Wr=E(_Wl),_Ws=E(_Wr[1]),_Wt=E(_Wo),_Wu=E(_Wt[1]),_Wv=B(_B1(_Ws[1],_Ws[2],_Ws[3],_Wr[2],_Wu[1],_Wu[2],_Wu[3],_Wt[2])),_Ww=E(_Wv[1]),_Wx=B(_B1(_Wq[1],_Wq[2],_Wq[3],_Wp[2],_Ww[1],_Ww[2],_Ww[3],_Wv[2]));return [0,E(_Wx[1]),_Wx[2]];})]);});},function(_Wy){return new F(function(){return A(_VW,[new T(function(){var _Wz=E(_Wb),_WA=E(_Wz[1]),_WB=E(_Wl),_WC=E(_WB[1]),_WD=E(_Wy),_WE=E(_WD[1]),_WF=B(_B1(_WC[1],_WC[2],_WC[3],_WB[2],_WE[1],_WE[2],_WE[3],_WD[2])),_WG=E(_WF[1]),_WH=B(_B1(_WA[1],_WA[2],_WA[3],_Wz[2],_WG[1],_WG[2],_WG[3],_WF[2]));return [0,E(_WH[1]),_WH[2]];})]);});});});},function(_WI){return new F(function(){return A(_VW,[new T(function(){return B(_BL(_Wb,_WI));})]);});}]);});}]);});};return new F(function(){return _VD(_Vr,_Vs,_Vt,_Vu,_Vv);});},_WJ=new T(function(){return B(unCStr("tab"));}),_WK=[1,_WJ,_9],_WL=[0,9],_WM=function(_WN){return function(_WO,_WP,_WQ,_WR,_WS){return new F(function(){return _Hk(new T(function(){return B(_I5(_WN,_WL));}),_WK,_WO,_WP,_WQ,_WR,_WS);});};},_WT=new T(function(){return B(_WM(_Uy));}),_WU=[0,39],_WV=[1,_WU,_9],_WW=new T(function(){return B(unCStr("\'\\\'\'"));}),_WX=function(_WY){var _WZ=E(E(_WY)[1]);return _WZ==39?E(_WW):[1,_WU,new T(function(){return B(_FA(_WZ,_WV));})];},_X0=function(_X1,_X2){return [1,_Ea,new T(function(){return B(_FR(_X1,[1,_Ea,_X2]));})];},_X3=function(_X4){return new F(function(){return _e(_WW,_X4);});},_X5=function(_X6,_X7){var _X8=E(E(_X7)[1]);return _X8==39?E(_X3):function(_X9){return [1,_WU,new T(function(){return B(_FA(_X8,[1,_WU,_X9]));})];};},_Xa=[0,_X5,_WX,_X0],_Xb=function(_Xc,_Xd,_Xe,_Xf,_Xg){var _Xh=new T(function(){return B(_bT(_Xc));}),_Xi=function(_Xj){return new F(function(){return A(_Xf,[_6B,_Xe,new T(function(){var _Xk=E(E(_Xe)[2]),_Xl=E(_Xj),_Xm=E(_Xl[1]),_Xn=B(_B1(_Xm[1],_Xm[2],_Xm[3],_Xl[2],_Xk[1],_Xk[2],_Xk[3],_9));return [0,E(_Xn[1]),_Xn[2]];})]);});};return new F(function(){return A(_Xd,[_Xe,function(_Xo,_Xp,_Xq){return new F(function(){return A(_Xg,[new T(function(){var _Xr=E(E(_Xp)[2]),_Xs=E(_Xq),_Xt=E(_Xs[1]),_Xu=B(_B1(_Xt[1],_Xt[2],_Xt[3],_Xs[2],_Xr[1],_Xr[2],_Xr[3],[1,new T(function(){return [1,E(B(A(_Xh,[_Xo])))];}),_9]));return [0,E(_Xu[1]),_Xu[2]];})]);});},_Xi,function(_Xv,_Xw,_Xx){return new F(function(){return A(_Xf,[_6B,_Xe,new T(function(){var _Xy=E(E(_Xe)[2]),_Xz=E(E(_Xw)[2]),_XA=E(_Xx),_XB=E(_XA[1]),_XC=B(_B1(_XB[1],_XB[2],_XB[3],_XA[2],_Xz[1],_Xz[2],_Xz[3],[1,new T(function(){return [1,E(B(A(_Xh,[_Xv])))];}),_9])),_XD=E(_XC[1]),_XE=B(_B1(_XD[1],_XD[2],_XD[3],_XC[2],_Xy[1],_Xy[2],_Xy[3],_9));return [0,E(_XE[1]),_XE[2]];})]);});},_Xi]);});},_XF=function(_XG,_XH,_XI){return new F(function(){return _Xb(_Xa,_WT,_XG,function(_XJ,_XK,_XL){return new F(function(){return A(_XH,[_6B,_XK,new T(function(){var _XM=E(E(_XK)[2]),_XN=E(_XL),_XO=E(_XN[1]),_XP=B(_B1(_XO[1],_XO[2],_XO[3],_XN[2],_XM[1],_XM[2],_XM[3],_9));return [0,E(_XP[1]),_XP[2]];})]);});},_XI);});},_XQ=function(_XR,_XS,_XT,_XU,_XV){return new F(function(){return A(_Vn,[_XR,function(_XW,_XX,_XY){return new F(function(){return _XF(_XX,function(_XZ,_Y0,_Y1){return new F(function(){return A(_XS,[_XZ,_Y0,new T(function(){return B(_BL(_XY,_Y1));})]);});},function(_Y2){return new F(function(){return A(_XT,[new T(function(){return B(_BL(_XY,_Y2));})]);});});});},_XT,function(_Y3,_Y4,_Y5){return new F(function(){return _XF(_Y4,function(_Y6,_Y7,_Y8){return new F(function(){return A(_XU,[_Y6,_Y7,new T(function(){return B(_BL(_Y5,_Y8));})]);});},function(_Y9){return new F(function(){return A(_XV,[new T(function(){return B(_BL(_Y5,_Y9));})]);});});});},_XV]);});},_Ya=[0,E(_9)],_Yb=[1,_Ya,_9],_Yc=function(_Yd,_Ye,_Yf,_Yg,_Yh,_Yi,_Yj){return new F(function(){return A(_Yd,[new T(function(){return B(A(_Ye,[_Yf]));}),function(_Yk){var _Yl=E(_Yk);if(!_Yl[0]){return E(new T(function(){return B(A(_Yj,[[0,E(_Yg),_Yb]]));}));}else{var _Ym=E(_Yl[1]);return new F(function(){return A(_Yi,[_Ym[1],[0,_Ym[2],E(_Yg),E(_Yh)],[0,E(_Yg),_9]]);});}}]);});},_Yn=new T(function(){return B(unCStr("end of input"));}),_Yo=[1,_Yn,_9],_Yp=function(_Yq,_Yr,_Ys,_Yt,_Yu,_Yv,_Yw,_Yx){return new F(function(){return _Hk(function(_Yy,_Yz,_YA,_YB,_YC){return new F(function(){return _Xb(_Ys,function(_YD,_YE,_YF,_YG,_YH){var _YI=E(_YD);return new F(function(){return _Yc(_Yq,_Yr,_YI[1],_YI[2],_YI[3],_YE,_YH);});},_Yy,_YB,_YC);});},_Yo,_Yt,_Yu,_Yv,_Yw,_Yx);});},_YJ=function(_YK,_YL,_YM,_YN,_YO){return new F(function(){return _Bj(_Vn,_YK,function(_YP,_YQ,_YR){return new F(function(){return _Yp(_E7,_GH,_Xa,_YQ,_YL,_YM,function(_YS,_YT,_YU){return new F(function(){return A(_YL,[_YS,_YT,new T(function(){return B(_BL(_YR,_YU));})]);});},function(_YV){return new F(function(){return A(_YM,[new T(function(){return B(_BL(_YR,_YV));})]);});});});},_YM,function(_YW,_YX,_YY){return new F(function(){return _Yp(_E7,_GH,_Xa,_YX,_YL,_YM,function(_YZ,_Z0,_Z1){return new F(function(){return A(_YN,[_YZ,_Z0,new T(function(){return B(_BL(_YY,_Z1));})]);});},function(_Z2){return new F(function(){return A(_YO,[new T(function(){return B(_BL(_YY,_Z2));})]);});});});});});},_Z3=function(_Z4,_Z5,_Z6,_Z7){var _Z8=function(_Z9){var _Za=function(_Zb){return new F(function(){return A(_Z7,[new T(function(){return B(_BL(_Z9,_Zb));})]);});};return new F(function(){return _XQ(_Z4,_Z5,_Za,function(_Zc,_Zd,_Ze){return new F(function(){return A(_Z6,[_Zc,_Zd,new T(function(){return B(_BL(_Z9,_Ze));})]);});},_Za);});};return new F(function(){return _YJ(_Z4,_Z5,_Z8,_Z6,_Z8);});},_Zf=function(_Zg,_Zh,_Zi,_Zj,_Zk){return new F(function(){return _Z3(_Zg,_Zh,_Zj,_Zk);});},_Zl=function(_Zm){return true;},_Zn=function(_Zo,_Zp,_Zq,_Zr,_Zs){var _Zt=E(_Zo),_Zu=E(_Zt[2]);return new F(function(){return _FX(_E7,_GH,_Zl,_Zt[1],_Zu[1],_Zu[2],_Zu[3],_Zt[3],_Zp,_Zs);});},_Zv=function(_Zw,_Zx,_Zy,_Zz,_ZA){return new F(function(){return A(_WT,[_Zw,function(_ZB,_ZC,_ZD){return new F(function(){return _Vo(_Zn,_Zf,_ZC,_Zx,_Zy,function(_ZE,_ZF,_ZG){return new F(function(){return A(_Zx,[_ZE,_ZF,new T(function(){return B(_BL(_ZD,_ZG));})]);});},function(_ZH){return new F(function(){return A(_Zy,[new T(function(){return B(_BL(_ZD,_ZH));})]);});});});},_Zy,function(_ZI,_ZJ,_ZK){return new F(function(){return _Vo(_Zn,_Zf,_ZJ,_Zx,_Zy,function(_ZL,_ZM,_ZN){return new F(function(){return A(_Zz,[_ZL,_ZM,new T(function(){return B(_BL(_ZK,_ZN));})]);});},function(_ZO){return new F(function(){return A(_ZA,[new T(function(){return B(_BL(_ZK,_ZO));})]);});});});},_ZA]);});},_ZP=[0,_U1,_9],_ZQ=[0,_9,1,1],_ZR=function(_ZS){return E(_ZS);},_ZT=new T(function(){return B(_iy("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_ZU=new T(function(){return B(_iy("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_ZV=[0,_E7,_ZU,_ZR,_ZT],_ZW=function(_ZX){return new F(function(){return unAppCStr("string error",new T(function(){return B(_bh(_ZX));}));});},_ZY=function(_ZZ,_100,_101,_102,_103){return new F(function(){return A(_WT,[_100,function(_104,_105,_106){return new F(function(){return A(_101,[_ZZ,_105,new T(function(){var _107=E(E(_105)[2]),_108=E(_106),_109=E(_108[1]),_10a=B(_B1(_109[1],_109[2],_109[3],_108[2],_107[1],_107[2],_107[3],_9));return [0,E(_10a[1]),_10a[2]];})]);});},_103,function(_10b,_10c,_10d){return new F(function(){return A(_102,[_ZZ,_10c,new T(function(){var _10e=E(E(_10c)[2]),_10f=E(_10d),_10g=E(_10f[1]),_10h=B(_B1(_10g[1],_10g[2],_10g[3],_10f[2],_10e[1],_10e[2],_10e[3],_9));return [0,E(_10h[1]),_10h[2]];})]);});},_103]);});},_10i=function(_10j,_10k,_10l,_10m,_10n){return new F(function(){return A(_Vn,[_10j,function(_10o,_10p,_10q){return new F(function(){return _ZY(_10o,_10p,_10k,function(_10r,_10s,_10t){return new F(function(){return A(_10k,[_10r,_10s,new T(function(){return B(_BL(_10q,_10t));})]);});},function(_10u){return new F(function(){return A(_10l,[new T(function(){return B(_BL(_10q,_10u));})]);});});});},_10l,function(_10v,_10w,_10x){return new F(function(){return _ZY(_10v,_10w,_10k,function(_10y,_10z,_10A){return new F(function(){return A(_10m,[_10y,_10z,new T(function(){return B(_BL(_10x,_10A));})]);});},function(_10B){return new F(function(){return A(_10n,[new T(function(){return B(_BL(_10x,_10B));})]);});});});},_10n]);});},_10C=function(_10D,_10E,_10F,_10G,_10H){return new F(function(){return _10i(_10D,_10E,_10F,_10G,function(_10I){var _10J=E(_10D),_10K=E(_10J[2]),_10L=E(_10J[1]);return _10L[0]==0?B(A(_10H,[new T(function(){var _10M=E(_10I),_10N=E(_10M[1]),_10O=B(_B1(_10N[1],_10N[2],_10N[3],_10M[2],_10K[1],_10K[2],_10K[3],_Yb));return [0,E(_10O[1]),_10O[2]];})])):B(A(_10E,[_10L[1],[0,_10L[2],E(_10K),E(_10J[3])],[0,E(_10K),_9]]));});});},_10P=function(_10Q,_10R,_10S,_10T,_10U){return new F(function(){return _Bj(_10C,_10Q,_10R,_10S,_10T);});},_10V=function(_10W,_10X,_10Y){return [0,_10W,E(E(_10X)),_10Y];},_10Z=function(_110,_111,_112){var _113=new T(function(){return B(_GB(_110));}),_114=new T(function(){return B(_GB(_110));});return new F(function(){return A(_111,[_112,function(_115,_116,_117){return new F(function(){return A(_113,[[0,new T(function(){return B(A(_114,[new T(function(){return B(_10V(_115,_116,_117));})]));})]]);});},function(_118){return new F(function(){return A(_113,[[0,new T(function(){return B(A(_114,[[1,_118]]));})]]);});},function(_119,_11a,_11b){return new F(function(){return A(_113,[new T(function(){return [1,E(B(A(_114,[new T(function(){return B(_10V(_119,_11a,_11b));})])))];})]);});},function(_11c){return new F(function(){return A(_113,[new T(function(){return [1,E(B(A(_114,[[1,_11c]])))];})]);});}]);});},_11d=function(_11e){return function(_11f,_11g,_11h,_11i,_11j){return new F(function(){return A(_11i,[new T(function(){var _11k=B(_10Z(_ZV,_11l,[0,new T(function(){var _11m=B(_10Z(_ZV,_10P,[0,_11e,E(_ZQ),E(_6B)]));if(!_11m[0]){var _11n=E(_11m[1]),_11o=_11n[0]==0?E(_11n[1]):B(_ZW(_11n[1]));}else{var _11p=E(_11m[1]),_11o=_11p[0]==0?E(_11p[1]):B(_ZW(_11p[1]));}return _11o;}),E(_ZQ),E(_6B)]));if(!_11k[0]){var _11q=E(_11k[1]),_11r=_11q[0]==0?E(_11q[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_11q[1]));})));})],_9],_9],_ZP];}else{var _11s=E(_11k[1]),_11r=_11s[0]==0?E(_11s[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_11s[1]));})));})],_9],_9],_ZP];}return _11r;}),_11f,new T(function(){return [0,E(E(_11f)[2]),_9];})]);});};},_11t=function(_11u,_11v,_11w,_11x,_11y){return new F(function(){return _Zv(_11u,function(_11z,_11A,_11B){return new F(function(){return A(_11d,[_11z,_11A,_11v,_11w,function(_11C,_11D,_11E){return new F(function(){return A(_11v,[_11C,_11D,new T(function(){return B(_BL(_11B,_11E));})]);});},function(_11F){return new F(function(){return A(_11w,[new T(function(){return B(_BL(_11B,_11F));})]);});}]);});},_11w,function(_11G,_11H,_11I){return new F(function(){return A(_11d,[_11G,_11H,_11v,_11w,function(_11J,_11K,_11L){return new F(function(){return A(_11x,[_11J,_11K,new T(function(){return B(_BL(_11I,_11L));})]);});},function(_11M){return new F(function(){return A(_11y,[new T(function(){return B(_BL(_11I,_11M));})]);});}]);});},_11y);});},_11N=function(_11O,_11P,_11Q,_11R,_11S,_11T){var _11U=function(_11V,_11W,_11X,_11Y,_11Z){var _120=function(_121,_122,_123,_124,_125){return new F(function(){return A(_11Y,[[0,[1,[0,_11O,_122,_123]],_121],_124,new T(function(){var _126=E(_125),_127=E(_126[1]),_128=E(E(_124)[2]),_129=B(_B1(_127[1],_127[2],_127[3],_126[2],_128[1],_128[2],_128[3],_9));return [0,E(_129[1]),_129[2]];})]);});},_12a=function(_12b){return new F(function(){return _120(_9,_U1,_9,_11V,new T(function(){var _12c=E(E(_11V)[2]),_12d=E(_12b),_12e=E(_12d[1]),_12f=B(_B1(_12e[1],_12e[2],_12e[3],_12d[2],_12c[1],_12c[2],_12c[3],_9));return [0,E(_12f[1]),_12f[2]];}));});};return new F(function(){return _11t(_11V,function(_12g,_12h,_12i){var _12j=E(_12g),_12k=E(_12j[2]);return new F(function(){return A(_11W,[[0,[1,[0,_11O,_12k[1],_12k[2]]],_12j[1]],_12h,new T(function(){var _12l=E(_12i),_12m=E(_12l[1]),_12n=E(E(_12h)[2]),_12o=B(_B1(_12m[1],_12m[2],_12m[3],_12l[2],_12n[1],_12n[2],_12n[3],_9));return [0,E(_12o[1]),_12o[2]];})]);});},_12a,function(_12p,_12q,_12r){var _12s=E(_12p),_12t=E(_12s[2]);return new F(function(){return _120(_12s[1],_12t[1],_12t[2],_12q,_12r);});},_12a);});};return new F(function(){return A(_Vn,[_11P,function(_12u,_12v,_12w){return new F(function(){return _11U(_12v,_11Q,_11R,function(_12x,_12y,_12z){return new F(function(){return A(_11Q,[_12x,_12y,new T(function(){return B(_BL(_12w,_12z));})]);});},function(_12A){return new F(function(){return A(_11R,[new T(function(){return B(_BL(_12w,_12A));})]);});});});},_11R,function(_12B,_12C,_12D){return new F(function(){return _11U(_12C,_11Q,_11R,function(_12E,_12F,_12G){return new F(function(){return A(_11S,[_12E,_12F,new T(function(){return B(_BL(_12D,_12G));})]);});},function(_12H){return new F(function(){return A(_11T,[new T(function(){return B(_BL(_12D,_12H));})]);});});});},_11T]);});},_12I=new T(function(){return B(unCStr(" associative operator"));}),_12J=function(_12K,_12L){var _12M=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_12K,_12I));}))))];}),_9];return function(_12N,_12O,_12P,_12Q,_12R){return new F(function(){return A(_12L,[_12N,function(_12S,_12T,_12U){return new F(function(){return A(_12R,[new T(function(){var _12V=E(E(_12T)[2]),_12W=E(_12U),_12X=E(_12W[1]),_12Y=B(_B1(_12X[1],_12X[2],_12X[3],_12W[2],_12V[1],_12V[2],_12V[3],_12M));return [0,E(_12Y[1]),_12Y[2]];})]);});},_12R,function(_12Z,_130,_131){return new F(function(){return A(_12R,[new T(function(){var _132=E(E(_130)[2]),_133=E(_131),_134=E(_133[1]),_135=B(_B1(_134[1],_134[2],_134[3],_133[2],_132[1],_132[2],_132[3],_12M));return [0,E(_135[1]),_135[2]];})]);});},_12R]);});};},_136=function(_137,_138,_139,_13a,_13b,_13c){var _13d=E(_137);if(!_13d[0]){return new F(function(){return A(_13c,[new T(function(){return [0,E(E(_138)[2]),_9];})]);});}else{return new F(function(){return A(_13d[1],[_138,_139,_13a,_13b,function(_13e){return new F(function(){return _136(_13d[2],_138,_139,_13a,function(_13f,_13g,_13h){return new F(function(){return A(_13b,[_13f,_13g,new T(function(){return B(_BL(_13e,_13h));})]);});},function(_13i){return new F(function(){return A(_13c,[new T(function(){return B(_BL(_13e,_13i));})]);});});});}]);});}},_13j=new T(function(){return B(unCStr("right"));}),_13k=new T(function(){return B(unCStr("left"));}),_13l=new T(function(){return B(unCStr("non"));}),_13m=new T(function(){return B(unCStr("operator"));}),_13n=[1,_13m,_9],_13o=[1,_9,_9],_13p=function(_13q){var _13r=E(_13q);if(!_13r[0]){return [0,_9,_9,_9,_9,_9];}else{var _13s=_13r[2],_13t=E(_13r[1]);switch(_13t[0]){case 0:var _13u=_13t[1],_13v=B(_13p(_13s)),_13w=_13v[1],_13x=_13v[2],_13y=_13v[3],_13z=_13v[4],_13A=_13v[5];switch(E(_13t[2])){case 0:return [0,_13w,_13x,[1,_13u,_13y],_13z,_13A];case 1:return [0,_13w,[1,_13u,_13x],_13y,_13z,_13A];default:return [0,[1,_13u,_13w],_13x,_13y,_13z,_13A];}break;case 1:var _13B=B(_13p(_13s));return [0,_13B[1],_13B[2],_13B[3],[1,_13t[1],_13B[4]],_13B[5]];default:var _13C=B(_13p(_13s));return [0,_13C[1],_13C[2],_13C[3],_13C[4],[1,_13t[1],_13C[5]]];}}},_13D=function(_13E,_13F){while(1){var _13G=(function(_13H,_13I){var _13J=E(_13I);if(!_13J[0]){return E(_13H);}else{var _13K=new T(function(){var _13L=B(_13p(_13J[1]));return [0,_13L[1],_13L[2],_13L[3],_13L[4],_13L[5]];}),_13M=new T(function(){return E(E(_13K)[2]);}),_13N=new T(function(){return B(_12J(_13k,function(_13O,_13P,_13Q,_13R,_13S){return new F(function(){return _136(_13M,_13O,_13P,_13Q,_13R,_13S);});}));}),_13T=new T(function(){return E(E(_13K)[1]);}),_13U=new T(function(){return E(E(_13K)[3]);}),_13V=new T(function(){return B(_12J(_13l,function(_13W,_13X,_13Y,_13Z,_140){return new F(function(){return _136(_13U,_13W,_13X,_13Y,_13Z,_140);});}));}),_141=function(_142,_143,_144,_145,_146,_147){var _148=function(_149,_14a,_14b,_14c,_14d){var _14e=new T(function(){return B(A(_142,[_149]));});return new F(function(){return _136(new T(function(){return E(E(_13K)[5]);}),_14a,function(_14f,_14g,_14h){return new F(function(){return A(_14b,[new T(function(){return B(A(_14f,[_14e]));}),_14g,new T(function(){var _14i=E(E(_14g)[2]),_14j=E(_14h),_14k=E(_14j[1]),_14l=B(_B1(_14k[1],_14k[2],_14k[3],_14j[2],_14i[1],_14i[2],_14i[3],_9));return [0,E(_14l[1]),_14l[2]];})]);});},_14c,function(_14m,_14n,_14o){return new F(function(){return A(_14d,[new T(function(){return B(A(_14m,[_14e]));}),_14n,new T(function(){var _14p=E(E(_14n)[2]),_14q=_14p[1],_14r=_14p[2],_14s=_14p[3],_14t=E(_14o),_14u=E(_14t[1]),_14v=_14u[2],_14w=_14u[3],_14x=E(_14t[2]);if(!_14x[0]){switch(B(_AT(_14u[1],_14q))){case 0:var _14y=[0,E(_14p),_9];break;case 1:if(_14v>=_14r){if(_14v!=_14r){var _14z=[0,E(_14u),_9];}else{if(_14w>=_14s){var _14A=_14w!=_14s?[0,E(_14u),_9]:[0,E(_14u),_B0];}else{var _14A=[0,E(_14p),_9];}var _14B=_14A,_14z=_14B;}var _14C=_14z,_14D=_14C;}else{var _14D=[0,E(_14p),_9];}var _14E=_14D,_14y=_14E;break;default:var _14y=[0,E(_14u),_9];}var _14F=_14y;}else{var _14G=B(_GZ(_14u,_14x,_13o)),_14H=E(_14G[1]),_14I=B(_B1(_14H[1],_14H[2],_14H[3],_14G[2],_14q,_14r,_14s,_9)),_14F=[0,E(_14I[1]),_14I[2]];}var _14J=_14F,_14K=_14J,_14L=_14K,_14M=_14L;return _14M;})]);});},function(_14N){return new F(function(){return A(_14d,[_14e,_14a,new T(function(){var _14O=E(E(_14a)[2]),_14P=_14O[1],_14Q=_14O[2],_14R=_14O[3],_14S=E(_14N),_14T=B(_GZ(_14S[1],_14S[2],_13o)),_14U=E(_14T[1]),_14V=B(_B1(_14U[1],_14U[2],_14U[3],_14T[2],_14P,_14Q,_14R,_9)),_14W=E(_14V[1]),_14X=B(_B1(_14W[1],_14W[2],_14W[3],_14V[2],_14P,_14Q,_14R,_9));return [0,E(_14X[1]),_14X[2]];})]);});});});};return new F(function(){return A(_13H,[_143,function(_14Y,_14Z,_150){return new F(function(){return _148(_14Y,_14Z,_144,_145,function(_151,_152,_153){return new F(function(){return A(_144,[_151,_152,new T(function(){return B(_BL(_150,_153));})]);});});});},_145,function(_154,_155,_156){return new F(function(){return _148(_154,_155,_144,_145,function(_157,_158,_159){return new F(function(){return A(_146,[_157,_158,new T(function(){return B(_BL(_156,_159));})]);});});});},_147]);});},_15a=function(_15b,_15c,_15d,_15e,_15f){var _15g=function(_15h,_15i,_15j){return new F(function(){return _141(_15h,_15i,_15c,_15d,function(_15k,_15l,_15m){return new F(function(){return A(_15e,[_15k,_15l,new T(function(){return B(_BL(_15j,_15m));})]);});},function(_15n){return new F(function(){return A(_15f,[new T(function(){return B(_BL(_15j,_15n));})]);});});});};return new F(function(){return _136(new T(function(){return E(E(_13K)[4]);}),_15b,function(_15o,_15p,_15q){return new F(function(){return _141(_15o,_15p,_15c,_15d,function(_15r,_15s,_15t){return new F(function(){return A(_15c,[_15r,_15s,new T(function(){return B(_BL(_15q,_15t));})]);});},function(_15u){return new F(function(){return A(_15d,[new T(function(){return B(_BL(_15q,_15u));})]);});});});},_15d,function(_15v,_15w,_15x){return new F(function(){return _15g(_15v,_15w,new T(function(){var _15y=E(_15x),_15z=E(_15y[2]);if(!_15z[0]){var _15A=E(_15y);}else{var _15B=B(_GZ(_15y[1],_15z,_13o)),_15A=[0,E(_15B[1]),_15B[2]];}var _15C=_15A;return _15C;}));});},function(_15D){return new F(function(){return _15g(_6P,_15b,new T(function(){var _15E=E(E(_15b)[2]),_15F=E(_15D),_15G=B(_GZ(_15F[1],_15F[2],_13o)),_15H=E(_15G[1]),_15I=B(_B1(_15H[1],_15H[2],_15H[3],_15G[2],_15E[1],_15E[2],_15E[3],_9));return [0,E(_15I[1]),_15I[2]];}));});});});},_15J=function(_15K,_15L,_15M,_15N,_15O,_15P){var _15Q=function(_15R){return new F(function(){return A(_13N,[_15L,_15M,_15N,function(_15S,_15T,_15U){return new F(function(){return A(_15O,[_15S,_15T,new T(function(){return B(_BL(_15R,_15U));})]);});},function(_15V){return new F(function(){return A(_13V,[_15L,_15M,_15N,function(_15W,_15X,_15Y){return new F(function(){return A(_15O,[_15W,_15X,new T(function(){var _15Z=E(_15R),_160=E(_15Z[1]),_161=E(_15V),_162=E(_161[1]),_163=E(_15Y),_164=E(_163[1]),_165=B(_B1(_162[1],_162[2],_162[3],_161[2],_164[1],_164[2],_164[3],_163[2])),_166=E(_165[1]),_167=B(_B1(_160[1],_160[2],_160[3],_15Z[2],_166[1],_166[2],_166[3],_165[2]));return [0,E(_167[1]),_167[2]];})]);});},function(_168){return new F(function(){return A(_15P,[new T(function(){var _169=E(_15R),_16a=E(_169[1]),_16b=E(_15V),_16c=E(_16b[1]),_16d=E(_168),_16e=E(_16d[1]),_16f=B(_B1(_16c[1],_16c[2],_16c[3],_16b[2],_16e[1],_16e[2],_16e[3],_16d[2])),_16g=E(_16f[1]),_16h=B(_B1(_16a[1],_16a[2],_16a[3],_169[2],_16g[1],_16g[2],_16g[3],_16f[2]));return [0,E(_16h[1]),_16h[2]];})]);});}]);});}]);});},_16i=function(_16j,_16k,_16l,_16m,_16n,_16o){var _16p=function(_16q,_16r,_16s){return new F(function(){return A(_16l,[new T(function(){return B(A(_16j,[_15K,_16q]));}),_16r,new T(function(){var _16t=E(E(_16r)[2]),_16u=E(_16s),_16v=E(_16u[1]),_16w=B(_B1(_16v[1],_16v[2],_16v[3],_16u[2],_16t[1],_16t[2],_16t[3],_9));return [0,E(_16w[1]),_16w[2]];})]);});};return new F(function(){return _15a(_16k,function(_16x,_16y,_16z){return new F(function(){return _15J(_16x,_16y,_16p,_16m,function(_16A,_16B,_16C){return new F(function(){return _16p(_16A,_16B,new T(function(){var _16D=E(_16z),_16E=E(_16D[1]),_16F=E(_16C),_16G=E(_16F[1]),_16H=B(_B1(_16E[1],_16E[2],_16E[3],_16D[2],_16G[1],_16G[2],_16G[3],_16F[2]));return [0,E(_16H[1]),_16H[2]];},1));});},function(_16I){return new F(function(){return _16p(_16x,_16y,new T(function(){var _16J=E(E(_16y)[2]),_16K=E(_16z),_16L=E(_16K[1]),_16M=E(_16I),_16N=E(_16M[1]),_16O=B(_B1(_16N[1],_16N[2],_16N[3],_16M[2],_16J[1],_16J[2],_16J[3],_9)),_16P=E(_16O[1]),_16Q=B(_B1(_16L[1],_16L[2],_16L[3],_16K[2],_16P[1],_16P[2],_16P[3],_16O[2]));return [0,E(_16Q[1]),_16Q[2]];},1));});});});},_16m,function(_16R,_16S,_16T){var _16U=function(_16V,_16W,_16X){return new F(function(){return A(_16n,[new T(function(){return B(A(_16j,[_15K,_16V]));}),_16W,new T(function(){var _16Y=E(E(_16W)[2]),_16Z=E(_16T),_170=E(_16Z[1]),_171=E(_16X),_172=E(_171[1]),_173=B(_B1(_170[1],_170[2],_170[3],_16Z[2],_172[1],_172[2],_172[3],_171[2])),_174=E(_173[1]),_175=B(_B1(_174[1],_174[2],_174[3],_173[2],_16Y[1],_16Y[2],_16Y[3],_9));return [0,E(_175[1]),_175[2]];})]);});};return new F(function(){return _15J(_16R,_16S,_16p,_16m,_16U,function(_176){return new F(function(){return _16U(_16R,_16S,new T(function(){var _177=E(E(_16S)[2]),_178=E(_176),_179=E(_178[1]),_17a=B(_B1(_179[1],_179[2],_179[3],_178[2],_177[1],_177[2],_177[3],_9));return [0,E(_17a[1]),_17a[2]];},1));});});});},_16o);});};return new F(function(){return _136(_13T,_15L,function(_17b,_17c,_17d){return new F(function(){return _16i(_17b,_17c,_15M,_15N,function(_17e,_17f,_17g){return new F(function(){return A(_15M,[_17e,_17f,new T(function(){return B(_BL(_17d,_17g));})]);});},function(_17h){return new F(function(){return A(_15N,[new T(function(){return B(_BL(_17d,_17h));})]);});});});},_15N,function(_17i,_17j,_17k){return new F(function(){return _16i(_17i,_17j,_15M,_15N,function(_17l,_17m,_17n){return new F(function(){return A(_15O,[_17l,_17m,new T(function(){return B(_BL(_17k,_17n));})]);});},function(_17o){return new F(function(){return _15Q(new T(function(){return B(_BL(_17k,_17o));}));});});});},_15Q);});},_17p=new T(function(){return B(_12J(_13j,function(_17q,_17r,_17s,_17t,_17u){return new F(function(){return _136(_13T,_17q,_17r,_17s,_17t,_17u);});}));}),_17v=function(_17w,_17x,_17y,_17z,_17A,_17B){var _17C=function(_17D){return new F(function(){return A(_17p,[_17x,_17y,_17z,function(_17E,_17F,_17G){return new F(function(){return A(_17A,[_17E,_17F,new T(function(){return B(_BL(_17D,_17G));})]);});},function(_17H){return new F(function(){return A(_13V,[_17x,_17y,_17z,function(_17I,_17J,_17K){return new F(function(){return A(_17A,[_17I,_17J,new T(function(){var _17L=E(_17D),_17M=E(_17L[1]),_17N=E(_17H),_17O=E(_17N[1]),_17P=E(_17K),_17Q=E(_17P[1]),_17R=B(_B1(_17O[1],_17O[2],_17O[3],_17N[2],_17Q[1],_17Q[2],_17Q[3],_17P[2])),_17S=E(_17R[1]),_17T=B(_B1(_17M[1],_17M[2],_17M[3],_17L[2],_17S[1],_17S[2],_17S[3],_17R[2]));return [0,E(_17T[1]),_17T[2]];})]);});},function(_17U){return new F(function(){return A(_17B,[new T(function(){var _17V=E(_17D),_17W=E(_17V[1]),_17X=E(_17H),_17Y=E(_17X[1]),_17Z=E(_17U),_180=E(_17Z[1]),_181=B(_B1(_17Y[1],_17Y[2],_17Y[3],_17X[2],_180[1],_180[2],_180[3],_17Z[2])),_182=E(_181[1]),_183=B(_B1(_17W[1],_17W[2],_17W[3],_17V[2],_182[1],_182[2],_182[3],_181[2]));return [0,E(_183[1]),_183[2]];})]);});}]);});}]);});},_184=function(_185,_186,_187,_188,_189,_18a){var _18b=function(_18c){var _18d=new T(function(){return B(A(_185,[_17w,_18c]));});return function(_18e,_18f,_18g,_18h,_18i){return new F(function(){return _17v(_18d,_18e,_18f,_18g,_18h,function(_18j){return new F(function(){return A(_18h,[_18d,_18e,new T(function(){var _18k=E(E(_18e)[2]),_18l=E(_18j),_18m=E(_18l[1]),_18n=B(_B1(_18m[1],_18m[2],_18m[3],_18l[2],_18k[1],_18k[2],_18k[3],_9));return [0,E(_18n[1]),_18n[2]];})]);});});});};};return new F(function(){return _15a(_186,function(_18o,_18p,_18q){return new F(function(){return A(_18b,[_18o,_18p,_187,_188,function(_18r,_18s,_18t){return new F(function(){return A(_187,[_18r,_18s,new T(function(){return B(_BL(_18q,_18t));})]);});},function(_18u){return new F(function(){return A(_188,[new T(function(){return B(_BL(_18q,_18u));})]);});}]);});},_188,function(_18v,_18w,_18x){return new F(function(){return A(_18b,[_18v,_18w,_187,_188,function(_18y,_18z,_18A){return new F(function(){return A(_189,[_18y,_18z,new T(function(){return B(_BL(_18x,_18A));})]);});},function(_18B){return new F(function(){return A(_18a,[new T(function(){return B(_BL(_18x,_18B));})]);});}]);});},_18a);});};return new F(function(){return _136(_13M,_17x,function(_18C,_18D,_18E){return new F(function(){return _184(_18C,_18D,_17y,_17z,function(_18F,_18G,_18H){return new F(function(){return A(_17y,[_18F,_18G,new T(function(){return B(_BL(_18E,_18H));})]);});},function(_18I){return new F(function(){return A(_17z,[new T(function(){return B(_BL(_18E,_18I));})]);});});});},_17z,function(_18J,_18K,_18L){return new F(function(){return _184(_18J,_18K,_17y,_17z,function(_18M,_18N,_18O){return new F(function(){return A(_17A,[_18M,_18N,new T(function(){return B(_BL(_18L,_18O));})]);});},function(_18P){return new F(function(){return _17C(new T(function(){return B(_BL(_18L,_18P));}));});});});},_17C);});},_18Q=function(_18R,_18S,_18T,_18U,_18V,_18W){var _18X=function(_18Y,_18Z,_190,_191,_192,_193){var _194=function(_195){return function(_196,_197,_198,_199,_19a){return new F(function(){return A(_17p,[_196,_197,_198,_199,function(_19b){return new F(function(){return A(_13N,[_196,_197,_198,function(_19c,_19d,_19e){return new F(function(){return A(_199,[_19c,_19d,new T(function(){return B(_BL(_19b,_19e));})]);});},function(_19f){return new F(function(){return A(_13V,[_196,_197,_198,function(_19g,_19h,_19i){return new F(function(){return A(_199,[_19g,_19h,new T(function(){var _19j=E(_19b),_19k=E(_19j[1]),_19l=E(_19f),_19m=E(_19l[1]),_19n=E(_19i),_19o=E(_19n[1]),_19p=B(_B1(_19m[1],_19m[2],_19m[3],_19l[2],_19o[1],_19o[2],_19o[3],_19n[2])),_19q=E(_19p[1]),_19r=B(_B1(_19k[1],_19k[2],_19k[3],_19j[2],_19q[1],_19q[2],_19q[3],_19p[2]));return [0,E(_19r[1]),_19r[2]];})]);});},function(_19s){return new F(function(){return A(_199,[new T(function(){return B(A(_18Y,[_18R,_195]));}),_196,new T(function(){var _19t=E(E(_196)[2]),_19u=E(_19b),_19v=E(_19u[1]),_19w=E(_19f),_19x=E(_19w[1]),_19y=E(_19s),_19z=E(_19y[1]),_19A=B(_B1(_19z[1],_19z[2],_19z[3],_19y[2],_19t[1],_19t[2],_19t[3],_9)),_19B=E(_19A[1]),_19C=B(_B1(_19x[1],_19x[2],_19x[3],_19w[2],_19B[1],_19B[2],_19B[3],_19A[2])),_19D=E(_19C[1]),_19E=B(_B1(_19v[1],_19v[2],_19v[3],_19u[2],_19D[1],_19D[2],_19D[3],_19C[2]));return [0,E(_19E[1]),_19E[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _15a(_18Z,function(_19F,_19G,_19H){return new F(function(){return A(_194,[_19F,_19G,_190,_191,function(_19I,_19J,_19K){return new F(function(){return A(_190,[_19I,_19J,new T(function(){return B(_BL(_19H,_19K));})]);});},function(_19L){return new F(function(){return A(_191,[new T(function(){return B(_BL(_19H,_19L));})]);});}]);});},_191,function(_19M,_19N,_19O){return new F(function(){return A(_194,[_19M,_19N,_190,_191,function(_19P,_19Q,_19R){return new F(function(){return A(_192,[_19P,_19Q,new T(function(){return B(_BL(_19O,_19R));})]);});},function(_19S){return new F(function(){return A(_193,[new T(function(){return B(_BL(_19O,_19S));})]);});}]);});},_193);});};return new F(function(){return _Hk(function(_19T,_19U,_19V,_19W,_19X){return new F(function(){return _15J(_18R,_19T,_19U,_19V,_19W,function(_19Y){return new F(function(){return _17v(_18R,_19T,_19U,_19V,function(_19Z,_1a0,_1a1){return new F(function(){return A(_19W,[_19Z,_1a0,new T(function(){return B(_BL(_19Y,_1a1));})]);});},function(_1a2){var _1a3=function(_1a4){return new F(function(){return A(_19W,[_18R,_19T,new T(function(){var _1a5=E(E(_19T)[2]),_1a6=E(_19Y),_1a7=E(_1a6[1]),_1a8=E(_1a2),_1a9=E(_1a8[1]),_1aa=E(_1a4),_1ab=E(_1aa[1]),_1ac=B(_B1(_1ab[1],_1ab[2],_1ab[3],_1aa[2],_1a5[1],_1a5[2],_1a5[3],_9)),_1ad=E(_1ac[1]),_1ae=B(_B1(_1a9[1],_1a9[2],_1a9[3],_1a8[2],_1ad[1],_1ad[2],_1ad[3],_1ac[2])),_1af=E(_1ae[1]),_1ag=B(_B1(_1a7[1],_1a7[2],_1a7[3],_1a6[2],_1af[1],_1af[2],_1af[3],_1ae[2]));return [0,E(_1ag[1]),_1ag[2]];})]);});};return new F(function(){return _136(_13U,_19T,function(_1ah,_1ai,_1aj){return new F(function(){return _18X(_1ah,_1ai,_19U,_19V,function(_1ak,_1al,_1am){return new F(function(){return A(_19U,[_1ak,_1al,new T(function(){return B(_BL(_1aj,_1am));})]);});},function(_1an){return new F(function(){return A(_19V,[new T(function(){return B(_BL(_1aj,_1an));})]);});});});},_19V,function(_1ao,_1ap,_1aq){return new F(function(){return _18X(_1ao,_1ap,_19U,_19V,function(_1ar,_1as,_1at){return new F(function(){return A(_19W,[_1ar,_1as,new T(function(){var _1au=E(_19Y),_1av=E(_1au[1]),_1aw=E(_1a2),_1ax=E(_1aw[1]),_1ay=E(_1aq),_1az=E(_1ay[1]),_1aA=E(_1at),_1aB=E(_1aA[1]),_1aC=B(_B1(_1az[1],_1az[2],_1az[3],_1ay[2],_1aB[1],_1aB[2],_1aB[3],_1aA[2])),_1aD=E(_1aC[1]),_1aE=B(_B1(_1ax[1],_1ax[2],_1ax[3],_1aw[2],_1aD[1],_1aD[2],_1aD[3],_1aC[2])),_1aF=E(_1aE[1]),_1aG=B(_B1(_1av[1],_1av[2],_1av[3],_1au[2],_1aF[1],_1aF[2],_1aF[3],_1aE[2]));return [0,E(_1aG[1]),_1aG[2]];})]);});},function(_1aH){return new F(function(){return _1a3(new T(function(){var _1aI=E(_1aq),_1aJ=E(_1aI[1]),_1aK=E(_1aH),_1aL=E(_1aK[1]),_1aM=B(_B1(_1aJ[1],_1aJ[2],_1aJ[3],_1aI[2],_1aL[1],_1aL[2],_1aL[3],_1aK[2]));return [0,E(_1aM[1]),_1aM[2]];},1));});});});},_1a3);});});});});});},_13n,_18S,_18T,_18U,_18V,_18W);});};_13E=function(_1aN,_1aO,_1aP,_1aQ,_1aR){return new F(function(){return _15a(_1aN,function(_1aS,_1aT,_1aU){return new F(function(){return _18Q(_1aS,_1aT,_1aO,_1aP,function(_1aV,_1aW,_1aX){return new F(function(){return A(_1aO,[_1aV,_1aW,new T(function(){return B(_BL(_1aU,_1aX));})]);});},function(_1aY){return new F(function(){return A(_1aP,[new T(function(){return B(_BL(_1aU,_1aY));})]);});});});},_1aP,function(_1aZ,_1b0,_1b1){return new F(function(){return _18Q(_1aZ,_1b0,_1aO,_1aP,function(_1b2,_1b3,_1b4){return new F(function(){return A(_1aQ,[_1b2,_1b3,new T(function(){return B(_BL(_1b1,_1b4));})]);});},function(_1b5){return new F(function(){return A(_1aR,[new T(function(){return B(_BL(_1b1,_1b5));})]);});});});},_1aR);});};_13F=_13J[2];return null;}})(_13E,_13F);if(_13G!=null){return _13G;}}},_1b6=0,_1b7=[3,_],_1b8=function(_1b9,_1ba){return [5,_1b7,_1b9,_1ba];},_1bb=new T(function(){return B(unCStr("=>"));}),_1bc=function(_1bd){return E(E(_1bd)[1]);},_1be=function(_1bf,_1bg,_1bh,_1bi){while(1){var _1bj=E(_1bi);if(!_1bj[0]){return [0,_1bf,_1bg,_1bh];}else{var _1bk=_1bj[2];switch(E(E(_1bj[1])[1])){case 9:var _1bl=(_1bh+8|0)-B(_Ee(_1bh-1|0,8))|0;_1bi=_1bk;_1bh=_1bl;continue;case 10:var _1bm=_1bg+1|0;_1bh=1;_1bi=_1bk;_1bg=_1bm;continue;default:var _1bl=_1bh+1|0;_1bi=_1bk;_1bh=_1bl;continue;}}}},_1bn=function(_1bo){return E(E(_1bo)[1]);},_1bp=function(_1bq){return E(E(_1bq)[2]);},_1br=function(_1bs){return [0,E(E(_1bs)[2]),_9];},_1bt=function(_1bu,_1bv,_1bw,_1bx,_1by,_1bz,_1bA){var _1bB=E(_1bv);if(!_1bB[0]){return new F(function(){return A(_1bz,[_9,_1bw,new T(function(){return B(_1br(_1bw));})]);});}else{var _1bC=E(_1bw),_1bD=E(_1bC[2]),_1bE=new T(function(){return B(_1bc(_1bu));}),_1bF=[0,E(_1bD),[1,[2,E([1,_Ea,new T(function(){return B(_FR(_1bB,_Eb));})])],_Ed]],_1bG=[2,E([1,_Ea,new T(function(){return B(_FR(_1bB,_Eb));})])],_1bH=new T(function(){var _1bI=B(_1be(_1bD[1],_1bD[2],_1bD[3],_1bB));return [0,_1bI[1],_1bI[2],_1bI[3]];}),_1bJ=function(_1bK,_1bL){var _1bM=E(_1bK);if(!_1bM[0]){return new F(function(){return A(_1bx,[_1bB,new T(function(){return [0,_1bL,E(E(_1bH)),E(_1bC[3])];}),new T(function(){return [0,E(E(_1bH)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_1bn(_1bE));}),[new T(function(){return B(A(new T(function(){return B(_1bp(_1bu));}),[_1bL]));}),function(_1bN){var _1bO=E(_1bN);if(!_1bO[0]){return E(new T(function(){return B(A(_1by,[_1bF]));}));}else{var _1bP=E(_1bO[1]),_1bQ=E(_1bP[1]);return E(_1bM[1])[1]!=_1bQ[1]?B(A(_1by,[[0,E(_1bD),[1,_1bG,[1,[0,E([1,_Ea,new T(function(){return B(_FR([1,_1bQ,_9],_Eb));})])],_9]]]])):B(_1bJ(_1bM[2],_1bP[2]));}}]);});}};return new F(function(){return A(_1bn,[_1bE,new T(function(){return B(A(_1bp,[_1bu,_1bC[1]]));}),function(_1bR){var _1bS=E(_1bR);if(!_1bS[0]){return E(new T(function(){return B(A(_1bA,[_1bF]));}));}else{var _1bT=E(_1bS[1]),_1bU=E(_1bT[1]);return E(_1bB[1])[1]!=_1bU[1]?B(A(_1bA,[[0,E(_1bD),[1,_1bG,[1,[0,E([1,_Ea,new T(function(){return B(_FR([1,_1bU,_9],_Eb));})])],_9]]]])):B(_1bJ(_1bB[2],_1bT[2]));}}]);});}},_1bV=function(_1bW,_1bX,_1bY,_1bZ,_1c0){return new F(function(){return _1bt(_I4,_1bb,_1bW,function(_1c1,_1c2,_1c3){return new F(function(){return A(_1bX,[_1b8,_1c2,new T(function(){var _1c4=E(E(_1c2)[2]),_1c5=E(_1c3),_1c6=E(_1c5[1]),_1c7=B(_B1(_1c6[1],_1c6[2],_1c6[3],_1c5[2],_1c4[1],_1c4[2],_1c4[3],_9));return [0,E(_1c7[1]),_1c7[2]];})]);});},_1bY,function(_1c8,_1c9,_1ca){return new F(function(){return A(_1bZ,[_1b8,_1c9,new T(function(){var _1cb=E(E(_1c9)[2]),_1cc=E(_1ca),_1cd=E(_1cc[1]),_1ce=B(_B1(_1cd[1],_1cd[2],_1cd[3],_1cc[2],_1cb[1],_1cb[2],_1cb[3],_9));return [0,E(_1ce[1]),_1ce[2]];})]);});},_1c0);});},_1cf=[0,_1bV,_1b6],_1cg=[1,_1cf,_9],_1ch=[1,_1cg,_9],_1ci=1,_1cj=[2,_],_1ck=function(_1b9,_1ba){return [5,_1cj,_1b9,_1ba];},_1cl=new T(function(){return B(unCStr("\\/"));}),_1cm=function(_1cn,_1co,_1cp,_1cq,_1cr){return new F(function(){return _1bt(_I4,_1cl,_1cn,function(_1cs,_1ct,_1cu){return new F(function(){return A(_1co,[_1ck,_1ct,new T(function(){var _1cv=E(E(_1ct)[2]),_1cw=E(_1cu),_1cx=E(_1cw[1]),_1cy=B(_B1(_1cx[1],_1cx[2],_1cx[3],_1cw[2],_1cv[1],_1cv[2],_1cv[3],_9));return [0,E(_1cy[1]),_1cy[2]];})]);});},_1cp,function(_1cz,_1cA,_1cB){return new F(function(){return A(_1cq,[_1ck,_1cA,new T(function(){var _1cC=E(E(_1cA)[2]),_1cD=E(_1cB),_1cE=E(_1cD[1]),_1cF=B(_B1(_1cE[1],_1cE[2],_1cE[3],_1cD[2],_1cC[1],_1cC[2],_1cC[3],_9));return [0,E(_1cF[1]),_1cF[2]];})]);});},_1cr);});},_1cG=[0,_1cm,_1ci],_1cH=[1,_],_1cI=function(_1b9,_1ba){return [5,_1cH,_1b9,_1ba];},_1cJ=new T(function(){return B(unCStr("/\\"));}),_1cK=function(_1cL,_1cM,_1cN,_1cO,_1cP){return new F(function(){return _1bt(_I4,_1cJ,_1cL,function(_1cQ,_1cR,_1cS){return new F(function(){return A(_1cM,[_1cI,_1cR,new T(function(){var _1cT=E(E(_1cR)[2]),_1cU=E(_1cS),_1cV=E(_1cU[1]),_1cW=B(_B1(_1cV[1],_1cV[2],_1cV[3],_1cU[2],_1cT[1],_1cT[2],_1cT[3],_9));return [0,E(_1cW[1]),_1cW[2]];})]);});},_1cN,function(_1cX,_1cY,_1cZ){return new F(function(){return A(_1cO,[_1cI,_1cY,new T(function(){var _1d0=E(E(_1cY)[2]),_1d1=E(_1cZ),_1d2=E(_1d1[1]),_1d3=B(_B1(_1d2[1],_1d2[2],_1d2[3],_1d1[2],_1d0[1],_1d0[2],_1d0[3],_9));return [0,E(_1d3[1]),_1d3[2]];})]);});},_1cP);});},_1d4=[0,_1cK,_1ci],_1d5=[1,_1d4,_9],_1d6=[1,_1cG,_1d5],_1d7=[1,_1d6,_1ch],_1d8=[0,_],_1d9=function(_1ba){return [4,_1d8,_1ba];},_1da=[0,45],_1db=[1,_1da,_9],_1dc=function(_1dd,_1de,_1df,_1dg,_1dh){return new F(function(){return _1bt(_I4,_1db,_1dd,function(_1di,_1dj,_1dk){return new F(function(){return A(_1de,[_1d9,_1dj,new T(function(){var _1dl=E(E(_1dj)[2]),_1dm=E(_1dk),_1dn=E(_1dm[1]),_1do=B(_B1(_1dn[1],_1dn[2],_1dn[3],_1dm[2],_1dl[1],_1dl[2],_1dl[3],_9));return [0,E(_1do[1]),_1do[2]];})]);});},_1df,function(_1dp,_1dq,_1dr){return new F(function(){return A(_1dg,[_1d9,_1dq,new T(function(){var _1ds=E(E(_1dq)[2]),_1dt=E(_1dr),_1du=E(_1dt[1]),_1dv=B(_B1(_1du[1],_1du[2],_1du[3],_1dt[2],_1ds[1],_1ds[2],_1ds[3],_9));return [0,E(_1dv[1]),_1dv[2]];})]);});},_1dh);});},_1dw=[1,_1dc],_1dx=[1,_1dw,_9],_1dy=[1,_1dx,_1d7],_1dz=new T(function(){return B(unCStr("number"));}),_1dA=[1,_1dz,_9],_1dB=new T(function(){return B(err(_Iq));}),_1dC=new T(function(){return B(err(_Io));}),_1dD=new T(function(){return B(_S1(_Sn,_RO,_St));}),_1dE=function(_1dF){return function(_1dG,_1dH,_1dI,_1dJ,_1dK){return new F(function(){return A(_1dJ,[new T(function(){var _1dL=B(_Sy(B(_It(_1dD,_1dF))));return _1dL[0]==0?E(_1dC):E(_1dL[2])[0]==0?E(_1dL[1]):E(_1dB);}),_1dG,new T(function(){return [0,E(E(_1dG)[2]),_9];})]);});};},_1dM=function(_1dN,_1dO,_1dP,_1dQ,_1dR){return new F(function(){return _BT(_HQ,_1dN,function(_1dS,_1dT,_1dU){return new F(function(){return A(_1dE,[_1dS,_1dT,_1dO,_1dP,function(_1dV,_1dW,_1dX){return new F(function(){return A(_1dO,[_1dV,_1dW,new T(function(){return B(_BL(_1dU,_1dX));})]);});},function(_1dY){return new F(function(){return A(_1dP,[new T(function(){return B(_BL(_1dU,_1dY));})]);});}]);});},_1dP,function(_1dZ,_1e0,_1e1){return new F(function(){return A(_1dE,[_1dZ,_1e0,_1dO,_1dP,function(_1e2,_1e3,_1e4){return new F(function(){return A(_1dQ,[_1e2,_1e3,new T(function(){return B(_BL(_1e1,_1e4));})]);});},function(_1e5){return new F(function(){return A(_1dR,[new T(function(){return B(_BL(_1e1,_1e5));})]);});}]);});},_1dR);});},_1e6=function(_1e7,_1e8,_1e9,_1ea,_1eb){return new F(function(){return _1dM(_1e7,function(_1ec,_1ed,_1ee){return new F(function(){return A(_1e8,[[1,[0,_,_1ec]],_1ed,new T(function(){var _1ef=E(E(_1ed)[2]),_1eg=E(_1ee),_1eh=E(_1eg[1]),_1ei=B(_B1(_1eh[1],_1eh[2],_1eh[3],_1eg[2],_1ef[1],_1ef[2],_1ef[3],_9));return [0,E(_1ei[1]),_1ei[2]];})]);});},_1e9,function(_1ej,_1ek,_1el){return new F(function(){return A(_1ea,[[1,[0,_,_1ej]],_1ek,new T(function(){var _1em=E(E(_1ek)[2]),_1en=_1em[1],_1eo=_1em[2],_1ep=_1em[3],_1eq=E(_1el),_1er=E(_1eq[1]),_1es=_1er[2],_1et=_1er[3],_1eu=E(_1eq[2]);if(!_1eu[0]){switch(B(_AT(_1er[1],_1en))){case 0:var _1ev=[0,E(_1em),_9];break;case 1:if(_1es>=_1eo){if(_1es!=_1eo){var _1ew=[0,E(_1er),_9];}else{if(_1et>=_1ep){var _1ex=_1et!=_1ep?[0,E(_1er),_9]:[0,E(_1er),_B0];}else{var _1ex=[0,E(_1em),_9];}var _1ey=_1ex,_1ew=_1ey;}var _1ez=_1ew,_1eA=_1ez;}else{var _1eA=[0,E(_1em),_9];}var _1eB=_1eA,_1ev=_1eB;break;default:var _1ev=[0,E(_1er),_9];}var _1eC=_1ev;}else{var _1eD=B(_GZ(_1er,_1eu,_1dA)),_1eE=E(_1eD[1]),_1eF=B(_B1(_1eE[1],_1eE[2],_1eE[3],_1eD[2],_1en,_1eo,_1ep,_9)),_1eC=[0,E(_1eF[1]),_1eF[2]];}var _1eG=_1eC,_1eH=_1eG,_1eI=_1eH,_1eJ=_1eI;return _1eJ;})]);});},function(_1eK){return new F(function(){return A(_1eb,[new T(function(){var _1eL=E(_1eK),_1eM=B(_GZ(_1eL[1],_1eL[2],_1dA));return [0,E(_1eM[1]),_1eM[2]];})]);});});});},_1eN=new T(function(){return B(unCStr("P_"));}),_1eO=function(_1eP,_1eQ,_1eR,_1eS,_1eT){return new F(function(){return _1bt(_I4,_1eN,_1eP,function(_1eU,_1eV,_1eW){return new F(function(){return _1e6(_1eV,_1eQ,_1eR,function(_1eX,_1eY,_1eZ){return new F(function(){return A(_1eQ,[_1eX,_1eY,new T(function(){return B(_BL(_1eW,_1eZ));})]);});},function(_1f0){return new F(function(){return A(_1eR,[new T(function(){return B(_BL(_1eW,_1f0));})]);});});});},_1eR,function(_1f1,_1f2,_1f3){return new F(function(){return _1e6(_1f2,_1eQ,_1eR,function(_1f4,_1f5,_1f6){return new F(function(){return A(_1eS,[_1f4,_1f5,new T(function(){return B(_BL(_1f3,_1f6));})]);});},function(_1f7){return new F(function(){return A(_1eT,[new T(function(){return B(_BL(_1f3,_1f7));})]);});});});},_1eT);});},_1f8=[0,41],_1f9=new T(function(){return B(_I5(_I4,_1f8));}),_1fa=function(_1fb,_1fc,_1fd,_1fe,_1ff,_1fg){return new F(function(){return A(_1f9,[_1fc,function(_1fh,_1fi,_1fj){return new F(function(){return A(_1fd,[_1fb,_1fi,new T(function(){var _1fk=E(E(_1fi)[2]),_1fl=E(_1fj),_1fm=E(_1fl[1]),_1fn=B(_B1(_1fm[1],_1fm[2],_1fm[3],_1fl[2],_1fk[1],_1fk[2],_1fk[3],_9));return [0,E(_1fn[1]),_1fn[2]];})]);});},_1fe,function(_1fo,_1fp,_1fq){return new F(function(){return A(_1ff,[_1fb,_1fp,new T(function(){var _1fr=E(E(_1fp)[2]),_1fs=E(_1fq),_1ft=E(_1fs[1]),_1fu=B(_B1(_1ft[1],_1ft[2],_1ft[3],_1fs[2],_1fr[1],_1fr[2],_1fr[3],_9));return [0,E(_1fu[1]),_1fu[2]];})]);});},_1fg]);});},_1fv=function(_1fw,_1fx,_1fy,_1fz,_1fA){return new F(function(){return A(_1fB,[_1fw,function(_1fC,_1fD,_1fE){return new F(function(){return _1fa(_1fC,_1fD,_1fx,_1fy,function(_1fF,_1fG,_1fH){return new F(function(){return A(_1fx,[_1fF,_1fG,new T(function(){return B(_BL(_1fE,_1fH));})]);});},function(_1fI){return new F(function(){return A(_1fy,[new T(function(){return B(_BL(_1fE,_1fI));})]);});});});},_1fy,function(_1fJ,_1fK,_1fL){return new F(function(){return _1fa(_1fJ,_1fK,_1fx,_1fy,function(_1fM,_1fN,_1fO){return new F(function(){return A(_1fz,[_1fM,_1fN,new T(function(){return B(_BL(_1fL,_1fO));})]);});},function(_1fP){return new F(function(){return A(_1fA,[new T(function(){return B(_BL(_1fL,_1fP));})]);});});});},_1fA]);});},_1fQ=[0,40],_1fR=new T(function(){return B(_I5(_I4,_1fQ));}),_1fS=function(_1fT,_1fU,_1fV,_1fW,_1fX){var _1fY=function(_1fZ){return new F(function(){return _1eO(_1fT,_1fU,_1fV,function(_1g0,_1g1,_1g2){return new F(function(){return A(_1fW,[_1g0,_1g1,new T(function(){return B(_BL(_1fZ,_1g2));})]);});},function(_1g3){return new F(function(){return A(_1fX,[new T(function(){return B(_BL(_1fZ,_1g3));})]);});});});};return new F(function(){return A(_1fR,[_1fT,function(_1g4,_1g5,_1g6){return new F(function(){return _1fv(_1g5,_1fU,_1fV,function(_1g7,_1g8,_1g9){return new F(function(){return A(_1fU,[_1g7,_1g8,new T(function(){return B(_BL(_1g6,_1g9));})]);});},function(_1ga){return new F(function(){return A(_1fV,[new T(function(){return B(_BL(_1g6,_1ga));})]);});});});},_1fV,function(_1gb,_1gc,_1gd){return new F(function(){return _1fv(_1gc,_1fU,_1fV,function(_1ge,_1gf,_1gg){return new F(function(){return A(_1fW,[_1ge,_1gf,new T(function(){return B(_BL(_1gd,_1gg));})]);});},function(_1gh){return new F(function(){return _1fY(new T(function(){return B(_BL(_1gd,_1gh));}));});});});},_1fY]);});},_1fB=new T(function(){return B(_13D(_1fS,_1dy));}),_1gi=function(_1gj,_1gk,_1gl,_1gm,_1gn){return new F(function(){return A(_1fB,[_1gj,function(_1go,_1gp,_1gq){return new F(function(){return _11N(_1go,_1gp,_1gk,_1gl,function(_1gr,_1gs,_1gt){return new F(function(){return A(_1gk,[_1gr,_1gs,new T(function(){return B(_BL(_1gq,_1gt));})]);});},function(_1gu){return new F(function(){return A(_1gl,[new T(function(){return B(_BL(_1gq,_1gu));})]);});});});},_1gl,function(_1gv,_1gw,_1gx){return new F(function(){return _11N(_1gv,_1gw,_1gk,_1gl,function(_1gy,_1gz,_1gA){return new F(function(){return A(_1gm,[_1gy,_1gz,new T(function(){return B(_BL(_1gx,_1gA));})]);});},function(_1gB){return new F(function(){return A(_1gn,[new T(function(){return B(_BL(_1gx,_1gB));})]);});});});},_1gn]);});},_1gC=function(_1gD,_1gE,_1gF,_1gG,_1gH){return new F(function(){return _Cw(_GJ,_1gD,function(_1gI,_1gJ,_1gK){return new F(function(){return _1gi(_1gJ,_1gE,_1gF,function(_1gL,_1gM,_1gN){return new F(function(){return A(_1gE,[_1gL,_1gM,new T(function(){return B(_BL(_1gK,_1gN));})]);});},function(_1gO){return new F(function(){return A(_1gF,[new T(function(){return B(_BL(_1gK,_1gO));})]);});});});},_1gF,function(_1gP,_1gQ,_1gR){return new F(function(){return _1gi(_1gQ,_1gE,_1gF,function(_1gS,_1gT,_1gU){return new F(function(){return A(_1gG,[_1gS,_1gT,new T(function(){return B(_BL(_1gR,_1gU));})]);});},function(_1gV){return new F(function(){return A(_1gH,[new T(function(){return B(_BL(_1gR,_1gV));})]);});});});});});},_1gW=function(_1gX,_1gY,_1gZ,_1h0,_1h1,_1h2,_1h3,_1h4){var _1h5=E(_1gX);if(!_1h5[0]){return new F(function(){return A(_1h4,[[0,E([0,_1gY,_1gZ,_1h0]),_Ed]]);});}else{var _1h6=_1h5[1];if(!B(_9r(_Gp,_1h6,_Ux))){return new F(function(){return A(_1h4,[[0,E([0,_1gY,_1gZ,_1h0]),[1,[0,E([1,_Ea,new T(function(){return B(_FR([1,_1h6,_9],_Eb));})])],_9]]]);});}else{var _1h7=function(_1h8,_1h9,_1ha,_1hb){var _1hc=[0,E([0,_1h8,_1h9,_1ha]),_9],_1hd=[0,E([0,_1h8,_1h9,_1ha]),_B0];return new F(function(){return _Cw(_V5,[0,_1h5[2],E(_1hb),E(_1h1)],function(_1he,_1hf,_1hg){return new F(function(){return _1gC(_1hf,_1h2,_1h3,function(_1hh,_1hi,_1hj){return new F(function(){return A(_1h2,[_1hh,_1hi,new T(function(){return B(_BL(_1hg,_1hj));})]);});},function(_1hk){return new F(function(){return A(_1h3,[new T(function(){return B(_BL(_1hg,_1hk));})]);});});});},_1h3,function(_1hl,_1hm,_1hn){return new F(function(){return _1gC(_1hm,_1h2,_1h3,function(_1ho,_1hp,_1hq){return new F(function(){return A(_1h2,[_1ho,_1hp,new T(function(){var _1hr=E(_1hn),_1hs=E(_1hr[1]),_1ht=E(_1hq),_1hu=E(_1ht[1]),_1hv=B(_B1(_1hs[1],_1hs[2],_1hs[3],_1hr[2],_1hu[1],_1hu[2],_1hu[3],_1ht[2])),_1hw=E(_1hv[1]),_1hx=_1hw[2],_1hy=_1hw[3],_1hz=E(_1hv[2]);if(!_1hz[0]){switch(B(_AT(_1h8,_1hw[1]))){case 0:var _1hA=[0,E(_1hw),_9];break;case 1:if(_1h9>=_1hx){if(_1h9!=_1hx){var _1hB=E(_1hc);}else{if(_1ha>=_1hy){var _1hC=_1ha!=_1hy?E(_1hc):E(_1hd);}else{var _1hC=[0,E(_1hw),_9];}var _1hD=_1hC,_1hB=_1hD;}var _1hE=_1hB,_1hF=_1hE;}else{var _1hF=[0,E(_1hw),_9];}var _1hG=_1hF,_1hA=_1hG;break;default:var _1hA=E(_1hc);}var _1hH=_1hA;}else{var _1hH=[0,E(_1hw),_1hz];}var _1hI=_1hH,_1hJ=_1hI,_1hK=_1hJ,_1hL=_1hK,_1hM=_1hL,_1hN=_1hM;return _1hN;})]);});},function(_1hO){return new F(function(){return A(_1h3,[new T(function(){var _1hP=E(_1hn),_1hQ=E(_1hP[1]),_1hR=E(_1hO),_1hS=E(_1hR[1]),_1hT=B(_B1(_1hQ[1],_1hQ[2],_1hQ[3],_1hP[2],_1hS[1],_1hS[2],_1hS[3],_1hR[2])),_1hU=E(_1hT[1]),_1hV=_1hU[2],_1hW=_1hU[3],_1hX=E(_1hT[2]);if(!_1hX[0]){switch(B(_AT(_1h8,_1hU[1]))){case 0:var _1hY=[0,E(_1hU),_9];break;case 1:if(_1h9>=_1hV){if(_1h9!=_1hV){var _1hZ=E(_1hc);}else{if(_1ha>=_1hW){var _1i0=_1ha!=_1hW?E(_1hc):E(_1hd);}else{var _1i0=[0,E(_1hU),_9];}var _1i1=_1i0,_1hZ=_1i1;}var _1i2=_1hZ,_1i3=_1i2;}else{var _1i3=[0,E(_1hU),_9];}var _1i4=_1i3,_1hY=_1i4;break;default:var _1hY=E(_1hc);}var _1i5=_1hY;}else{var _1i5=[0,E(_1hU),_1hX];}var _1i6=_1i5,_1i7=_1i6,_1i8=_1i7,_1i9=_1i8,_1ia=_1i9,_1ib=_1ia;return _1ib;})]);});});});});});};switch(E(E(_1h6)[1])){case 9:var _1ic=(_1h0+8|0)-B(_Ee(_1h0-1|0,8))|0;return new F(function(){return _1h7(_1gY,_1gZ,_1ic,[0,_1gY,_1gZ,_1ic]);});break;case 10:var _1id=_1gZ+1|0;return new F(function(){return _1h7(_1gY,_1id,1,[0,_1gY,_1id,1]);});break;default:var _1ie=_1h0+1|0;return new F(function(){return _1h7(_1gY,_1gZ,_1ie,[0,_1gY,_1gZ,_1ie]);});}}}},_1if=function(_1ig,_1ih){return E(_1);},_1ii=function(_1ij,_1ik,_1il,_1im){var _1in=E(_1il);switch(_1in[0]){case 0:var _1io=E(_1im);return _1io[0]==0?E(_1):E(_1io[1]);case 1:return new F(function(){return A(_1ij,[_1in[1],_9]);});break;case 2:return new F(function(){return A(_1ik,[_1in[1],[1,new T(function(){return B(_1ii(_1ij,_1ik,_1in[2],_1im));}),_9]]);});break;default:return new F(function(){return A(_1ik,[_1in[1],[1,new T(function(){return B(_1ii(_1ij,_1ik,_1in[2],_1im));}),[1,new T(function(){return B(_1ii(_1ij,_1ik,_1in[3],_1im));}),_9]]]);});}},_1ip=function(_1iq,_1ir,_1is,_1it,_1iu,_1iv,_1iw,_1ix){var _1iy=E(_1iw);switch(_1iy[0]){case 0:return [0];case 1:return new F(function(){return A(_1it,[_1iy[1],_9]);});break;case 2:return new F(function(){return A(_1iq,[_1iy[1],[1,new T(function(){return B(_1ii(_1it,_1iu,_1iy[2],_1ix));}),_9]]);});break;case 3:return new F(function(){return A(_1iq,[_1iy[1],[1,new T(function(){return B(_1ii(_1it,_1iu,_1iy[2],_1ix));}),[1,new T(function(){return B(_1ii(_1it,_1iu,_1iy[3],_1ix));}),_9]]]);});break;case 4:return new F(function(){return A(_1ir,[_1iy[1],[1,new T(function(){return B(_1ip(_1iq,_1ir,_1is,_1it,_1iu,_1iv,_1iy[2],_1ix));}),_9]]);});break;case 5:return new F(function(){return A(_1ir,[_1iy[1],[1,new T(function(){return B(_1ip(_1iq,_1ir,_1is,_1it,_1iu,_1iv,_1iy[2],_1ix));}),[1,new T(function(){return B(_1ip(_1iq,_1ir,_1is,_1it,_1iu,_1iv,_1iy[3],_1ix));}),_9]]]);});break;default:var _1iz=_1iy[1],_1iA=_1iy[2];return new F(function(){return A(_1is,[_1iz,[1,new T(function(){return B(A(_1iv,[new T(function(){return B(A(_1iA,[_2V]));}),_1iz]));}),[1,new T(function(){return B(_1ip(_1iq,_1ir,_1is,_1it,_1iu,_1iv,B(A(_1iA,[_2V])),[1,new T(function(){return B(A(_1iv,[new T(function(){return B(A(_1iA,[_2V]));}),_1iz]));}),_9]));}),_9]]]);});}},_1iB=[0,95],_1iC=[1,_1iB,_9],_1iD=[1,_1iC,_9],_1iE=function(_1iF){var _1iG=function(_1iH){var _1iI=E(new T(function(){var _1iJ=B(_10Z(_ZV,_1fB,[0,_1iF,E(_ZQ),E(_6B)]));if(!_1iJ[0]){var _1iK=E(_1iJ[1]),_1iL=_1iK[0]==0?[1,_1iK[1]]:[0,_1iK[1]];}else{var _1iM=E(_1iJ[1]),_1iL=_1iM[0]==0?[1,_1iM[1]]:[0,_1iM[1]];}return _1iL;}));return _1iI[0]==0?function(_1iN,_1iO,_1iP,_1iQ,_1iR){return new F(function(){return A(_1iQ,[[0,[0,new T(function(){var _1iS=E(_1iI[1]),_1iT=E(_1iS[1]);return B(_bc(_1iT[1],_1iT[2],_1iT[3],_1iS[2]));})],_9],_1iN,new T(function(){return [0,E(E(_1iN)[2]),_9];})]);});}:function(_1iU,_1iV,_1iW,_1iX,_1iY){return new F(function(){return A(_1iX,[[0,[0,new T(function(){return B(_1ip(_Q,_u,_Q,_N,_Q,_1if,_1iI[1],_1iD));})],_9],_1iU,new T(function(){return [0,E(E(_1iU)[2]),_9];})]);});};};return function(_1iZ,_1j0,_1j1,_1j2,_1j3){return new F(function(){return A(_Vn,[_1iZ,function(_1j4,_1j5,_1j6){return new F(function(){return A(_1iG,[_,_1j5,_1j0,_1j1,function(_1j7,_1j8,_1j9){return new F(function(){return A(_1j0,[_1j7,_1j8,new T(function(){return B(_BL(_1j6,_1j9));})]);});},function(_1ja){return new F(function(){return A(_1j1,[new T(function(){return B(_BL(_1j6,_1ja));})]);});}]);});},_1j1,function(_1jb,_1jc,_1jd){return new F(function(){return A(_1iG,[_,_1jc,_1j0,_1j1,function(_1je,_1jf,_1jg){return new F(function(){return A(_1j2,[_1je,_1jf,new T(function(){return B(_BL(_1jd,_1jg));})]);});},function(_1jh){return new F(function(){return A(_1j3,[new T(function(){return B(_BL(_1jd,_1jh));})]);});}]);});},_1j3]);});};},_1ji=function(_1jj,_1jk,_1jl,_1jm,_1jn,_1jo,_1jp,_1jq,_1jr,_1js){return new F(function(){return _FX(_1jj,_1jk,function(_1jt){return !B(_9r(_Gp,_1jt,_1jl))?true:false;},_1jm,_1jn,_1jo,_1jp,_1jq,_1jr,_1js);});},_1ju=[0,9],_1jv=[1,_1ju,_9],_1jw=[0,10],_1jx=[1,_1jw,_1jv],_1jy=function(_1jz,_1jA,_1jB,_1jC,_1jD){var _1jE=E(_1jz),_1jF=E(_1jE[2]);return new F(function(){return _1ji(_E7,_GH,_1jx,_1jE[1],_1jF[1],_1jF[2],_1jF[3],_1jE[3],_1jA,_1jD);});},_1jG=function(_1jH,_1jI,_1jJ,_1jK,_1jL){return new F(function(){return _BT(_1jy,_1jH,function(_1jM,_1jN,_1jO){return new F(function(){return A(_1iE,[_1jM,_1jN,_1jI,_1jJ,function(_1jP,_1jQ,_1jR){return new F(function(){return A(_1jI,[_1jP,_1jQ,new T(function(){return B(_BL(_1jO,_1jR));})]);});},function(_1jS){return new F(function(){return A(_1jJ,[new T(function(){return B(_BL(_1jO,_1jS));})]);});}]);});},_1jJ,function(_1jT,_1jU,_1jV){return new F(function(){return A(_1iE,[_1jT,_1jU,_1jI,_1jJ,function(_1jW,_1jX,_1jY){return new F(function(){return A(_1jK,[_1jW,_1jX,new T(function(){return B(_BL(_1jV,_1jY));})]);});},function(_1jZ){return new F(function(){return A(_1jL,[new T(function(){return B(_BL(_1jV,_1jZ));})]);});}]);});},_1jL);});},_1k0=function(_1k1,_1k2,_1k3,_1k4,_1k5,_1k6){var _1k7=function(_1k8,_1k9,_1ka,_1kb,_1kc,_1kd){var _1ke=function(_1kf){var _1kg=[0,[1,[0,_1k1,_1k8,new T(function(){return B(_3d(_SF,_1kf));})]],_9];return function(_1kh,_1ki,_1kj,_1kk,_1kl){return new F(function(){return A(_Vn,[_1kh,function(_1km,_1kn,_1ko){return new F(function(){return A(_1ki,[_1kg,_1kn,new T(function(){var _1kp=E(E(_1kn)[2]),_1kq=E(_1ko),_1kr=E(_1kq[1]),_1ks=B(_B1(_1kr[1],_1kr[2],_1kr[3],_1kq[2],_1kp[1],_1kp[2],_1kp[3],_9));return [0,E(_1ks[1]),_1ks[2]];})]);});},_1kj,function(_1kt,_1ku,_1kv){return new F(function(){return A(_1kk,[_1kg,_1ku,new T(function(){var _1kw=E(E(_1ku)[2]),_1kx=E(_1kv),_1ky=E(_1kx[1]),_1kz=B(_B1(_1ky[1],_1ky[2],_1ky[3],_1kx[2],_1kw[1],_1kw[2],_1kw[3],_9));return [0,E(_1kz[1]),_1kz[2]];})]);});},_1kl]);});};},_1kA=function(_1kB,_1kC,_1kD,_1kE,_1kF){var _1kG=function(_1kH,_1kI,_1kJ){return new F(function(){return A(_1ke,[_1kH,_1kI,_1kC,_1kD,function(_1kK,_1kL,_1kM){return new F(function(){return A(_1kE,[_1kK,_1kL,new T(function(){return B(_BL(_1kJ,_1kM));})]);});},function(_1kN){return new F(function(){return A(_1kF,[new T(function(){return B(_BL(_1kJ,_1kN));})]);});}]);});},_1kO=function(_1kP){return new F(function(){return _1kG(_9,_1kB,new T(function(){var _1kQ=E(E(_1kB)[2]),_1kR=E(_1kP),_1kS=E(_1kR[1]),_1kT=B(_B1(_1kS[1],_1kS[2],_1kS[3],_1kR[2],_1kQ[1],_1kQ[2],_1kQ[3],_9));return [0,E(_1kT[1]),_1kT[2]];}));});};return new F(function(){return _CW(_HW,_In,_1kB,function(_1kU,_1kV,_1kW){return new F(function(){return A(_1ke,[_1kU,_1kV,_1kC,_1kD,function(_1kX,_1kY,_1kZ){return new F(function(){return A(_1kC,[_1kX,_1kY,new T(function(){return B(_BL(_1kW,_1kZ));})]);});},function(_1l0){return new F(function(){return A(_1kD,[new T(function(){return B(_BL(_1kW,_1l0));})]);});}]);});},_1kO,_1kG,_1kO);});};return new F(function(){return _Cw(_GJ,_1k9,function(_1l1,_1l2,_1l3){return new F(function(){return _1kA(_1l2,_1ka,_1kb,function(_1l4,_1l5,_1l6){return new F(function(){return A(_1ka,[_1l4,_1l5,new T(function(){return B(_BL(_1l3,_1l6));})]);});},function(_1l7){return new F(function(){return A(_1kb,[new T(function(){return B(_BL(_1l3,_1l7));})]);});});});},_1kb,function(_1l8,_1l9,_1la){return new F(function(){return _1kA(_1l9,_1ka,_1kb,function(_1lb,_1lc,_1ld){return new F(function(){return A(_1kc,[_1lb,_1lc,new T(function(){return B(_BL(_1la,_1ld));})]);});},function(_1le){return new F(function(){return A(_1kd,[new T(function(){return B(_BL(_1la,_1le));})]);});});});});});},_1lf=function(_1lg,_1lh,_1li,_1lj,_1lk){return new F(function(){return _BT(_TD,_1lg,function(_1ll,_1lm,_1ln){return new F(function(){return _1k7(_1ll,_1lm,_1lh,_1li,function(_1lo,_1lp,_1lq){return new F(function(){return A(_1lh,[_1lo,_1lp,new T(function(){return B(_BL(_1ln,_1lq));})]);});},function(_1lr){return new F(function(){return A(_1li,[new T(function(){return B(_BL(_1ln,_1lr));})]);});});});},_1lk,function(_1ls,_1lt,_1lu){return new F(function(){return _1k7(_1ls,_1lt,_1lh,_1li,function(_1lv,_1lw,_1lx){return new F(function(){return A(_1lj,[_1lv,_1lw,new T(function(){return B(_BL(_1lu,_1lx));})]);});},function(_1ly){return new F(function(){return A(_1lk,[new T(function(){return B(_BL(_1lu,_1ly));})]);});});});},_1lk);});};return new F(function(){return _Cw(_GJ,_1k2,function(_1lz,_1lA,_1lB){return new F(function(){return _1lf(_1lA,_1k3,_1k4,function(_1lC,_1lD,_1lE){return new F(function(){return A(_1k3,[_1lC,_1lD,new T(function(){return B(_BL(_1lB,_1lE));})]);});},function(_1lF){return new F(function(){return A(_1k4,[new T(function(){return B(_BL(_1lB,_1lF));})]);});});});},_1k4,function(_1lG,_1lH,_1lI){return new F(function(){return _1lf(_1lH,_1k3,_1k4,function(_1lJ,_1lK,_1lL){return new F(function(){return A(_1k5,[_1lJ,_1lK,new T(function(){return B(_BL(_1lI,_1lL));})]);});},function(_1lM){return new F(function(){return A(_1k6,[new T(function(){return B(_BL(_1lI,_1lM));})]);});});});});});},_1lN=function(_1lO,_1lP,_1lQ,_1lR,_1lS){return new F(function(){return A(_1fB,[_1lO,function(_1lT,_1lU,_1lV){return new F(function(){return _1k0(_1lT,_1lU,_1lP,_1lQ,function(_1lW,_1lX,_1lY){return new F(function(){return A(_1lP,[_1lW,_1lX,new T(function(){return B(_BL(_1lV,_1lY));})]);});},function(_1lZ){return new F(function(){return A(_1lQ,[new T(function(){return B(_BL(_1lV,_1lZ));})]);});});});},_1lQ,function(_1m0,_1m1,_1m2){return new F(function(){return _1k0(_1m0,_1m1,_1lP,_1lQ,function(_1m3,_1m4,_1m5){return new F(function(){return A(_1lR,[_1m3,_1m4,new T(function(){return B(_BL(_1m2,_1m5));})]);});},function(_1m6){return new F(function(){return A(_1lS,[new T(function(){return B(_BL(_1m2,_1m6));})]);});});});},_1lS]);});},_1m7=function(_1m8,_1m9,_1ma,_1mb){var _1mc=function(_1md){var _1me=E(_1m8),_1mf=E(_1me[2]),_1mg=function(_1mh){var _1mi=function(_1mj){return new F(function(){return A(_1mb,[new T(function(){var _1mk=E(_1md),_1ml=E(_1mk[1]),_1mm=E(_1mh),_1mn=E(_1mm[1]),_1mo=E(_1mj),_1mp=E(_1mo[1]),_1mq=B(_B1(_1mn[1],_1mn[2],_1mn[3],_1mm[2],_1mp[1],_1mp[2],_1mp[3],_1mo[2])),_1mr=E(_1mq[1]),_1ms=B(_B1(_1ml[1],_1ml[2],_1ml[3],_1mk[2],_1mr[1],_1mr[2],_1mr[3],_1mq[2]));return [0,E(_1ms[1]),_1ms[2]];})]);});};return new F(function(){return _1jG(_1me,_1m9,_1mi,function(_1mt,_1mu,_1mv){return new F(function(){return A(_1ma,[_1mt,_1mu,new T(function(){var _1mw=E(_1md),_1mx=E(_1mw[1]),_1my=E(_1mh),_1mz=E(_1my[1]),_1mA=E(_1mv),_1mB=E(_1mA[1]),_1mC=B(_B1(_1mz[1],_1mz[2],_1mz[3],_1my[2],_1mB[1],_1mB[2],_1mB[3],_1mA[2])),_1mD=E(_1mC[1]),_1mE=B(_B1(_1mx[1],_1mx[2],_1mx[3],_1mw[2],_1mD[1],_1mD[2],_1mD[3],_1mC[2]));return [0,E(_1mE[1]),_1mE[2]];})]);});},_1mi);});};return new F(function(){return _1gW(_1me[1],_1mf[1],_1mf[2],_1mf[3],_1me[3],_1m9,_1mg,_1mg);});};return new F(function(){return _1lN(_1m8,_1m9,_1mc,_1ma,_1mc);});},_1mF=function(_1mG,_1mH,_1mI,_1mJ,_1mK){return new F(function(){return _1m7(_1mG,_1mH,_1mJ,_1mK);});},_11l=function(_1mL,_1mM,_1mN,_1mO,_1mP){return new F(function(){return _BT(_1mF,_1mL,function(_1mQ,_1mR,_1mS){return new F(function(){return _U3(_1mQ,_1mR,_1mM,function(_1mT,_1mU,_1mV){return new F(function(){return A(_1mM,[_1mT,_1mU,new T(function(){return B(_BL(_1mS,_1mV));})]);});});});},_1mN,function(_1mW,_1mX,_1mY){return new F(function(){return _U3(_1mW,_1mX,_1mM,function(_1mZ,_1n0,_1n1){return new F(function(){return A(_1mO,[_1mZ,_1n0,new T(function(){return B(_BL(_1mY,_1n1));})]);});});});},_1mP);});},_1n2=new T(function(){return B(unCStr("div"));}),_1n3=function(_1n4,_1n5,_1n6,_){var _1n7=jsCreateElem(toJSStr(E(_1n2))),_1n8=_1n7,_1n9=jsAppendChild(_1n8,E(_1n6)[1]),_1na=[0,_1n8],_1nb=B(A(_1n4,[_1n5,_1na,_])),_1nc=_1nb;return _1na;},_1nd=new T(function(){return B(unCStr("closed"));}),_1ne=function(_1nf,_1ng){return new F(function(){return _F(0,E(_1nf)[1],_1ng);});},_1nh=function(_1ni){return function(_md,_me){return new F(function(){return _6v(new T(function(){return B(_23(_1ne,_1ni,_9));}),_md,_me);});};},_1nj=function(_1nk){return function(_md,_me){return new F(function(){return _6v(new T(function(){return B(_1ip(_Q,_u,_Q,_N,_Q,_1if,_1nk,_1iD));}),_md,_me);});};},_1nl=new T(function(){return B(unCStr("open"));}),_1nm=new T(function(){return B(unCStr("termination"));}),_1nn=function(_1no,_){return _1no;},_1np=function(_1nq){var _1nr=E(_1nq);return _1nr[0]==0?E(_1nn):function(_1ns,_){var _1nt=B(A(new T(function(){var _1nu=E(_1nr[1]);return B(_1nv(_1nu[1],_1nu[2]));}),[_1ns,_])),_1nw=_1nt,_1nx=B(A(new T(function(){return B(_1np(_1nr[2]));}),[_1ns,_])),_1ny=_1nx;return _1ns;};},_1nz=function(_1nA){var _1nB=E(_1nA);return _1nB[0]==0?E(_1nn):function(_1nC,_){var _1nD=B(A(new T(function(){var _1nE=E(_1nB[1]);return B(_1nv(_1nE[1],_1nE[2]));}),[_1nC,_])),_1nF=_1nD,_1nG=B(A(new T(function(){return B(_1nz(_1nB[2]));}),[_1nC,_])),_1nH=_1nG;return _1nC;};},_1nI=new T(function(){return B(unCStr("SHOW"));}),_1nv=function(_1nJ,_1nK){var _1nL=E(_1nJ);if(!_1nL[0]){return function(_md,_me){return new F(function(){return _1n3(_6v,_1nL[1],_md,_me);});};}else{var _1nM=E(_1nL[1]),_1nN=_1nM[1],_1nO=_1nM[2],_1nP=_1nM[3];if(!B(_3x(_1nO,_1nI))){var _1nQ=E(_1nK);return _1nQ[0]==0?function(_md,_me){return new F(function(){return _1n3(_7s,function(_1nR,_){var _1nS=B(_7i(_1nj,_1nN,_1nR,_)),_1nT=_1nS,_1nU=B(_7i(_7s,function(_1nV,_){var _1nW=B(_7i(_6v,_1nO,_1nV,_)),_1nX=_1nW,_1nY=B(_7i(_1nh,_1nP,_1nV,_)),_1nZ=_1nY;return _1nV;},_1nR,_)),_1o0=_1nU;return _1nR;},_md,_me);});}:function(_md,_me){return new F(function(){return _1n3(_7s,function(_1o1,_){var _1o2=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1ip(_Q,_u,_Q,_N,_Q,_1if,_1nN,_1iD));})));}),_1o1,_)),_1o3=_1o2,_1o4=B(_1n3(_7s,function(_1o5,_){var _1o6=B(_7i(_7s,new T(function(){return B(_1nz(_1nQ));}),_1o5,_)),_1o7=_1o6,_1o8=B(_1n3(_7s,function(_1o9,_){var _1oa=B(_7i(_6v,_9,_1o9,_)),_1ob=_1oa,_1oc=B(A(_6C,[_6P,_1ob,_zS,_1nm,_])),_1od=_1oc,_1oe=B(_7i(_7s,function(_1of,_){var _1og=B(_7i(_6v,_1nO,_1of,_)),_1oh=_1og,_1oi=B(_7i(_1nh,_1nP,_1of,_)),_1oj=_1oi;return _1of;},_1o9,_)),_1ok=_1oe;return _1o9;},_1o5,_)),_1ol=_1o8;return _1o5;},_1o1,_)),_1om=_1o4,_1on=B(A(_6C,[_6P,_1om,_zS,_1nd,_])),_1oo=_1on;return _1o1;},_md,_me);});};}else{var _1op=E(_1nK);return _1op[0]==0?function(_md,_me){return new F(function(){return _1n3(_7s,function(_A1,_){return new F(function(){return _7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1ip(_Q,_u,_Q,_N,_Q,_1if,_1nN,_1iD));})));}),_A1,_);});},_md,_me);});}:function(_md,_me){return new F(function(){return _1n3(_7s,function(_1oq,_){var _1or=B(_7i(_6v,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1ip(_Q,_u,_Q,_N,_Q,_1if,_1nN,_1iD));})));}),_1oq,_)),_1os=_1or,_1ot=B(_1n3(_7s,function(_A1,_){return new F(function(){return _7i(_7s,new T(function(){return B(_1np(_1op));}),_A1,_);});},_1oq,_)),_1ou=_1ot,_1ov=B(A(_6C,[_6P,_1ou,_zS,_1nl,_])),_1ow=_1ov;return _1oq;},_md,_me);});};}}},_1ox=function(_1oy){var _1oz=E(_1oy);return _1oz[0]==0?E(_1nn):function(_1oA,_){var _1oB=B(A(new T(function(){var _1oC=E(_1oz[1]);return B(_1nv(_1oC[1],_1oC[2]));}),[_1oA,_])),_1oD=_1oB,_1oE=B(A(new T(function(){return B(_1ox(_1oz[2]));}),[_1oA,_])),_1oF=_1oE;return _1oA;};},_1oG=[0,10],_1oH=[1,_1oG,_9],_1oI=function(_1oJ,_1oK,_){var _1oL=jsCreateElem(toJSStr(E(_1oJ))),_1oM=_1oL,_1oN=jsAppendChild(_1oM,E(_1oK)[1]);return [0,_1oM];},_1oO=function(_1oP,_1oQ,_1oR,_){var _1oS=B(_1oI(_1oP,_1oR,_)),_1oT=_1oS,_1oU=B(A(_1oQ,[_1oT,_])),_1oV=_1oU;return _1oT;},_1oW=new T(function(){return B(unCStr("()"));}),_1oX=new T(function(){return B(unCStr("GHC.Tuple"));}),_1oY=new T(function(){return B(unCStr("ghc-prim"));}),_1oZ=new T(function(){var _1p0=hs_wordToWord64(2170319554),_1p1=_1p0,_1p2=hs_wordToWord64(26914641),_1p3=_1p2;return [0,_1p1,_1p3,[0,_1p1,_1p3,_1oY,_1oX,_1oW],_9];}),_1p4=function(_1p5){return E(_1oZ);},_1p6=new T(function(){return B(unCStr("PerchM"));}),_1p7=new T(function(){return B(unCStr("Haste.Perch"));}),_1p8=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1p9=new T(function(){var _1pa=hs_wordToWord64(3005229400),_1pb=_1pa,_1pc=hs_wordToWord64(2682402736),_1pd=_1pc;return [0,_1pb,_1pd,[0,_1pb,_1pd,_1p8,_1p7,_1p6],_9];}),_1pe=function(_1pf){return E(_1p9);},_1pg=function(_1ph){var _1pi=E(_1ph);if(!_1pi[0]){return [0];}else{var _1pj=E(_1pi[1]);return [1,[0,_1pj[1],_1pj[2]],new T(function(){return B(_1pg(_1pi[2]));})];}},_1pk=function(_1pl,_1pm){var _1pn=E(_1pl);if(!_1pn){return [0,_9,_1pm];}else{var _1po=E(_1pm);if(!_1po[0]){return [0,_9,_9];}else{var _1pp=new T(function(){var _1pq=B(_1pk(_1pn-1|0,_1po[2]));return [0,_1pq[1],_1pq[2]];});return [0,[1,_1po[1],new T(function(){return E(E(_1pp)[1]);})],new T(function(){return E(E(_1pp)[2]);})];}}},_1pr=[0,120],_1ps=[0,48],_1pt=function(_1pu){var _1pv=new T(function(){var _1pw=B(_1pk(8,new T(function(){var _1px=md5(toJSStr(E(_1pu))),_1py=_1px;return fromJSStr(_1py);})));return [0,_1pw[1],_1pw[2]];}),_1pz=parseInt([0,toJSStr([1,_1ps,[1,_1pr,new T(function(){return E(E(_1pv)[1]);})]])]),_1pA=_1pz,_1pB=new T(function(){var _1pC=B(_1pk(8,new T(function(){return E(E(_1pv)[2]);})));return [0,_1pC[1],_1pC[2]];}),_1pD=parseInt([0,toJSStr([1,_1ps,[1,_1pr,new T(function(){return E(E(_1pB)[1]);})]])]),_1pE=_1pD,_1pF=hs_mkWord64(_1pA,_1pE),_1pG=_1pF,_1pH=parseInt([0,toJSStr([1,_1ps,[1,_1pr,new T(function(){return E(B(_1pk(8,new T(function(){return E(E(_1pB)[2]);})))[1]);})]])]),_1pI=_1pH,_1pJ=hs_mkWord64(_1pI,_1pI),_1pK=_1pJ;return [0,_1pG,_1pK];},_1pL=function(_1pM,_1pN){var _1pO=jsShowI(_1pM),_1pP=_1pO,_1pQ=md5(_1pP),_1pR=_1pQ;return new F(function(){return _e(fromJSStr(_1pR),new T(function(){var _1pS=jsShowI(_1pN),_1pT=_1pS,_1pU=md5(_1pT),_1pV=_1pU;return fromJSStr(_1pV);},1));});},_1pW=function(_1pX){var _1pY=E(_1pX);return new F(function(){return _1pL(_1pY[1],_1pY[2]);});},_1pZ=function(_1q0,_1q1){return function(_1q2){return E(new T(function(){var _1q3=B(A(_1q0,[_])),_1q4=E(_1q3[3]),_1q5=_1q4[1],_1q6=_1q4[2],_1q7=B(_e(_1q3[4],[1,new T(function(){return B(A(_1q1,[_]));}),_9]));if(!_1q7[0]){var _1q8=[0,_1q5,_1q6,_1q4,_9];}else{var _1q9=B(_1pt(new T(function(){return B(_8Q(B(_3d(_1pW,[1,[0,_1q5,_1q6],new T(function(){return B(_1pg(_1q7));})]))));},1))),_1q8=[0,_1q9[1],_1q9[2],_1q4,_1q7];}var _1qa=_1q8,_1qb=_1qa;return _1qb;}));};},_1qc=new T(function(){return B(_1pZ(_1pe,_1p4));}),_1qd=function(_1qe,_1qf,_1qg,_){var _1qh=E(_1qf),_1qi=B(A(_1qe,[_1qg,_])),_1qj=_1qi,_1qk=B(A(_6C,[_6P,_1qj,_1qh[1],_1qh[2],_])),_1ql=_1qk;return _1qj;},_1qm=function(_1qn,_1qo){while(1){var _1qp=(function(_1qq,_1qr){var _1qs=E(_1qr);if(!_1qs[0]){return E(_1qq);}else{_1qn=function(_1qt,_){return new F(function(){return _1qd(_1qq,_1qs[1],_1qt,_);});};_1qo=_1qs[2];return null;}})(_1qn,_1qo);if(_1qp!=null){return _1qp;}}},_1qu=new T(function(){return B(unCStr("value"));}),_1qv=new T(function(){return B(unCStr("id"));}),_1qw=new T(function(){return B(unCStr("onclick"));}),_1qx=new T(function(){return B(unCStr("checked"));}),_1qy=[0,_1qx,_9],_1qz=[1,_1qy,_9],_1qA=new T(function(){return B(unCStr("type"));}),_1qB=new T(function(){return B(unCStr("input"));}),_1qC=function(_1qD,_){return new F(function(){return _1oI(_1qB,_1qD,_);});},_1qE=function(_1qF,_1qG,_1qH,_1qI,_1qJ){var _1qK=new T(function(){var _1qL=new T(function(){return B(_1qm(_1qC,[1,[0,_1qA,_1qG],[1,[0,_1qv,_1qF],[1,[0,_1qu,_1qH],_9]]]));});return !E(_1qI)?E(_1qL):B(_1qm(_1qL,_1qz));}),_1qM=E(_1qJ);return _1qM[0]==0?E(_1qK):B(_1qm(_1qK,[1,[0,_1qw,_1qM[1]],_9]));},_1qN=new T(function(){return B(unCStr("href"));}),_1qO=[0,97],_1qP=[1,_1qO,_9],_1qQ=function(_1qR,_){return new F(function(){return _1oI(_1qP,_1qR,_);});},_1qS=function(_1qT,_1qU){return function(_1qV,_){var _1qW=B(A(new T(function(){return B(_1qm(_1qQ,[1,[0,_1qN,_1qT],_9]));}),[_1qV,_])),_1qX=_1qW,_1qY=B(A(_1qU,[_1qX,_])),_1qZ=_1qY;return _1qX;};},_1r0=function(_1r1){return new F(function(){return _1qS(_1r1,function(_1qt,_){return new F(function(){return _6v(_1r1,_1qt,_);});});});},_1r2=new T(function(){return B(unCStr("option"));}),_1r3=function(_1r4,_){return new F(function(){return _1oI(_1r2,_1r4,_);});},_1r5=new T(function(){return B(unCStr("selected"));}),_1r6=[0,_1r5,_9],_1r7=[1,_1r6,_9],_1r8=function(_1r9,_1ra,_1rb){var _1rc=new T(function(){return B(_1qm(_1r3,[1,[0,_1qu,_1r9],_9]));});if(!E(_1rb)){return function(_1rd,_){var _1re=B(A(_1rc,[_1rd,_])),_1rf=_1re,_1rg=B(A(_1ra,[_1rf,_])),_1rh=_1rg;return _1rf;};}else{return new F(function(){return _1qm(function(_1ri,_){var _1rj=B(A(_1rc,[_1ri,_])),_1rk=_1rj,_1rl=B(A(_1ra,[_1rk,_])),_1rm=_1rl;return _1rk;},_1r7);});}},_1rn=function(_1ro,_1rp){return new F(function(){return _1r8(_1ro,function(_1qt,_){return new F(function(){return _6v(_1ro,_1qt,_);});},_1rp);});},_1rq=new T(function(){return B(unCStr("method"));}),_1rr=new T(function(){return B(unCStr("action"));}),_1rs=new T(function(){return B(unCStr("UTF-8"));}),_1rt=new T(function(){return B(unCStr("acceptCharset"));}),_1ru=[0,_1rt,_1rs],_1rv=new T(function(){return B(unCStr("form"));}),_1rw=function(_1rx,_){return new F(function(){return _1oI(_1rv,_1rx,_);});},_1ry=function(_1rz,_1rA,_1rB){return function(_1rC,_){var _1rD=B(A(new T(function(){return B(_1qm(_1rw,[1,_1ru,[1,[0,_1rr,_1rz],[1,[0,_1rq,_1rA],_9]]]));}),[_1rC,_])),_1rE=_1rD,_1rF=B(A(_1rB,[_1rE,_])),_1rG=_1rF;return _1rE;};},_1rH=new T(function(){return B(unCStr("select"));}),_1rI=function(_1rJ,_){return new F(function(){return _1oI(_1rH,_1rJ,_);});},_1rK=function(_1rL,_1rM){return function(_1rN,_){var _1rO=B(A(new T(function(){return B(_1qm(_1rI,[1,[0,_1qv,_1rL],_9]));}),[_1rN,_])),_1rP=_1rO,_1rQ=B(A(_1rM,[_1rP,_])),_1rR=_1rQ;return _1rP;};},_1rS=new T(function(){return B(unCStr("textarea"));}),_1rT=function(_1rU,_){return new F(function(){return _1oI(_1rS,_1rU,_);});},_1rV=function(_1rW,_1rX){return function(_1rY,_){var _1rZ=B(A(new T(function(){return B(_1qm(_1rT,[1,[0,_1qv,_1rW],_9]));}),[_1rY,_])),_1s0=_1rZ,_1s1=B(_6v(_1rX,_1s0,_)),_1s2=_1s1;return _1s0;};},_1s3=new T(function(){return B(unCStr("color:red"));}),_1s4=new T(function(){return B(unCStr("style"));}),_1s5=[0,_1s4,_1s3],_1s6=[1,_1s5,_9],_1s7=[0,98],_1s8=[1,_1s7,_9],_1s9=function(_1sa){return new F(function(){return _1qm(function(_1sb,_){var _1sc=B(_1oI(_1s8,_1sb,_)),_1sd=_1sc,_1se=B(A(_1sa,[_1sd,_])),_1sf=_1se;return _1sd;},_1s6);});},_1sg=function(_1sh,_1si,_){var _1sj=E(_1sh);if(!_1sj[0]){return _1si;}else{var _1sk=B(A(_1sj[1],[_1si,_])),_1sl=_1sk,_1sm=B(_1sg(_1sj[2],_1si,_)),_1sn=_1sm;return _1si;}},_1so=function(_1sp,_1sq,_){return new F(function(){return _1sg(_1sp,_1sq,_);});},_1sr=function(_1ss,_1st,_1su,_){var _1sv=B(A(_1ss,[_1su,_])),_1sw=_1sv,_1sx=B(A(_1st,[_1su,_])),_1sy=_1sx;return _1su;},_1sz=[0,_6S,_1sr,_1so],_1sA=[0,_1sz,_1qc,_6v,_6v,_1oO,_1s9,_1qS,_1r0,_1qE,_1rV,_1rK,_1r8,_1rn,_1ry,_1qm],_1sB=function(_1sC,_1sD,_){var _1sE=B(A(_1sD,[_])),_1sF=_1sE;return _1sC;},_1sG=function(_1sH,_1sI,_){var _1sJ=B(A(_1sI,[_])),_1sK=_1sJ;return new T(function(){return B(A(_1sH,[_1sK]));});},_1sL=[0,_1sG,_1sB],_1sM=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1sN=new T(function(){return B(unCStr("base"));}),_1sO=new T(function(){return B(unCStr("IOException"));}),_1sP=new T(function(){var _1sQ=hs_wordToWord64(4053623282),_1sR=_1sQ,_1sS=hs_wordToWord64(3693590983),_1sT=_1sS;return [0,_1sR,_1sT,[0,_1sR,_1sT,_1sN,_1sM,_1sO],_9];}),_1sU=function(_1sV){return E(_1sP);},_1sW=function(_1sX){var _1sY=E(_1sX);return new F(function(){return _1I(B(_1G(_1sY[1])),_1sU,_1sY[2]);});},_1sZ=new T(function(){return B(unCStr(": "));}),_1t0=[0,41],_1t1=new T(function(){return B(unCStr(" ("));}),_1t2=new T(function(){return B(unCStr("already exists"));}),_1t3=new T(function(){return B(unCStr("does not exist"));}),_1t4=new T(function(){return B(unCStr("protocol error"));}),_1t5=new T(function(){return B(unCStr("failed"));}),_1t6=new T(function(){return B(unCStr("invalid argument"));}),_1t7=new T(function(){return B(unCStr("inappropriate type"));}),_1t8=new T(function(){return B(unCStr("hardware fault"));}),_1t9=new T(function(){return B(unCStr("unsupported operation"));}),_1ta=new T(function(){return B(unCStr("timeout"));}),_1tb=new T(function(){return B(unCStr("resource vanished"));}),_1tc=new T(function(){return B(unCStr("interrupted"));}),_1td=new T(function(){return B(unCStr("resource busy"));}),_1te=new T(function(){return B(unCStr("resource exhausted"));}),_1tf=new T(function(){return B(unCStr("end of file"));}),_1tg=new T(function(){return B(unCStr("illegal operation"));}),_1th=new T(function(){return B(unCStr("permission denied"));}),_1ti=new T(function(){return B(unCStr("user error"));}),_1tj=new T(function(){return B(unCStr("unsatisified constraints"));}),_1tk=new T(function(){return B(unCStr("system error"));}),_1tl=function(_1tm,_1tn){switch(E(_1tm)){case 0:return new F(function(){return _e(_1t2,_1tn);});break;case 1:return new F(function(){return _e(_1t3,_1tn);});break;case 2:return new F(function(){return _e(_1td,_1tn);});break;case 3:return new F(function(){return _e(_1te,_1tn);});break;case 4:return new F(function(){return _e(_1tf,_1tn);});break;case 5:return new F(function(){return _e(_1tg,_1tn);});break;case 6:return new F(function(){return _e(_1th,_1tn);});break;case 7:return new F(function(){return _e(_1ti,_1tn);});break;case 8:return new F(function(){return _e(_1tj,_1tn);});break;case 9:return new F(function(){return _e(_1tk,_1tn);});break;case 10:return new F(function(){return _e(_1t4,_1tn);});break;case 11:return new F(function(){return _e(_1t5,_1tn);});break;case 12:return new F(function(){return _e(_1t6,_1tn);});break;case 13:return new F(function(){return _e(_1t7,_1tn);});break;case 14:return new F(function(){return _e(_1t8,_1tn);});break;case 15:return new F(function(){return _e(_1t9,_1tn);});break;case 16:return new F(function(){return _e(_1ta,_1tn);});break;case 17:return new F(function(){return _e(_1tb,_1tn);});break;default:return new F(function(){return _e(_1tc,_1tn);});}},_1to=[0,125],_1tp=new T(function(){return B(unCStr("{handle: "));}),_1tq=function(_1tr,_1ts,_1tt,_1tu,_1tv,_1tw){var _1tx=new T(function(){var _1ty=new T(function(){return B(_1tl(_1ts,new T(function(){var _1tz=E(_1tu);return _1tz[0]==0?E(_1tw):B(_e(_1t1,new T(function(){return B(_e(_1tz,[1,_1t0,_1tw]));},1)));},1)));},1),_1tA=E(_1tt);return _1tA[0]==0?E(_1ty):B(_e(_1tA,new T(function(){return B(_e(_1sZ,_1ty));},1)));},1),_1tB=E(_1tv);if(!_1tB[0]){var _1tC=E(_1tr);if(!_1tC[0]){return E(_1tx);}else{var _1tD=E(_1tC[1]);return _1tD[0]==0?B(_e(_1tp,new T(function(){return B(_e(_1tD[1],[1,_1to,new T(function(){return B(_e(_1sZ,_1tx));})]));},1))):B(_e(_1tp,new T(function(){return B(_e(_1tD[1],[1,_1to,new T(function(){return B(_e(_1sZ,_1tx));})]));},1)));}}else{return new F(function(){return _e(_1tB[1],new T(function(){return B(_e(_1sZ,_1tx));},1));});}},_1tE=function(_1tF){var _1tG=E(_1tF);return new F(function(){return _1tq(_1tG[1],_1tG[2],_1tG[3],_1tG[4],_1tG[6],_9);});},_1tH=function(_1tI,_1tJ){var _1tK=E(_1tI);return new F(function(){return _1tq(_1tK[1],_1tK[2],_1tK[3],_1tK[4],_1tK[6],_1tJ);});},_1tL=function(_1tM,_1tN){return new F(function(){return _23(_1tH,_1tM,_1tN);});},_1tO=function(_1tP,_1tQ,_1tR){var _1tS=E(_1tQ);return new F(function(){return _1tq(_1tS[1],_1tS[2],_1tS[3],_1tS[4],_1tS[6],_1tR);});},_1tT=[0,_1tO,_1tE,_1tL],_1tU=new T(function(){return [0,_1sU,_1tT,_1tV,_1sW];}),_1tV=function(_1tW){return [0,_1tU,_1tW];},_1tX=7,_1tY=function(_1tZ){return [0,_4O,_1tX,_9,_1tZ,_4O,_4O];},_1u0=function(_1u1,_){return new F(function(){return die(new T(function(){return B(_1tV(new T(function(){return B(_1tY(_1u1));})));}));});},_1u2=function(_1u3,_){return new F(function(){return _1u0(_1u3,_);});},_1u4=function(_1u5,_){return new F(function(){return _1u2(_1u5,_);});},_1u6=function(_1u7,_){return new F(function(){return _1u4(_1u7,_);});},_1u8=function(_1u9,_1ua,_){var _1ub=B(A(_1u9,[_])),_1uc=_1ub;return new F(function(){return A(_1ua,[_1uc,_]);});},_1ud=function(_1ue,_1uf,_){var _1ug=B(A(_1ue,[_])),_1uh=_1ug;return new F(function(){return A(_1uf,[_]);});},_1ui=[0,_1u8,_1ud,_6S,_1u6],_1uj=[0,_1ui,_6P],_1uk=function(_1ul){return E(E(_1ul)[1]);},_1um=function(_1un){return E(E(_1un)[2]);},_1uo=function(_1up,_1uq){var _1ur=new T(function(){return B(_1uk(_1up));});return function(_1us){return new F(function(){return A(new T(function(){return B(_1bn(_1ur));}),[new T(function(){return B(A(_1um,[_1up,_1uq]));}),function(_1ut){return new F(function(){return A(new T(function(){return B(_GB(_1ur));}),[[0,_1ut,_1us]]);});}]);});};},_1uu=function(_1uv,_1uw){return [0,_1uv,function(_1ux){return new F(function(){return _1uo(_1uw,_1ux);});}];},_1uy=function(_1uz,_1uA,_1uB,_1uC){return new F(function(){return A(_1bn,[_1uz,new T(function(){return B(A(_1uA,[_1uC]));}),function(_1uD){return new F(function(){return A(_1uB,[new T(function(){return E(E(_1uD)[1]);}),new T(function(){return E(E(_1uD)[2]);})]);});}]);});},_1uE=function(_1uF,_1uG,_1uH,_1uI){return new F(function(){return A(_1bn,[_1uF,new T(function(){return B(A(_1uG,[_1uI]));}),function(_1uJ){return new F(function(){return A(_1uH,[new T(function(){return E(E(_1uJ)[2]);})]);});}]);});},_1uK=function(_1uL,_1uM,_1uN,_1uO){return new F(function(){return _1uE(_1uL,_1uM,_1uN,_1uO);});},_1uP=function(_1uQ){return E(E(_1uQ)[4]);},_1uR=function(_1uS,_1uT){return function(_1uU){return E(new T(function(){return B(A(_1uP,[_1uS,_1uT]));}));};},_1uV=function(_1uW){return [0,function(_1uM,_1uN,_1uO){return new F(function(){return _1uy(_1uW,_1uM,_1uN,_1uO);});},function(_1uM,_1uN,_1uO){return new F(function(){return _1uK(_1uW,_1uM,_1uN,_1uO);});},function(_1uX,_1uY){return new F(function(){return A(new T(function(){return B(_GB(_1uW));}),[[0,_1uX,_1uY]]);});},function(_1uO){return new F(function(){return _1uR(_1uW,_1uO);});}];},_1uZ=function(_1v0,_1v1,_1v2){return new F(function(){return A(_GB,[_1v0,[0,_1v1,_1v2]]);});},_1v3=[0,10],_1v4=function(_1v5,_1v6){var _1v7=E(_1v6);if(!_1v7[0]){return E(_6P);}else{var _1v8=_1v7[1],_1v9=E(_1v7[2]);if(!_1v9[0]){var _1va=E(_1v8);return new F(function(){return _1vb(_1v3,_1va[3],_1va[4]);});}else{return function(_1vc){return new F(function(){return A(new T(function(){var _1vd=E(_1v8);return B(_1vb(_1v3,_1vd[3],_1vd[4]));}),[new T(function(){return B(A(_1v5,[new T(function(){return B(A(new T(function(){return B(_1v4(_1v5,_1v9));}),[_1vc]));})]));})]);});};}}},_1ve=new T(function(){return B(unCStr("(->)"));}),_1vf=new T(function(){return B(unCStr("GHC.Prim"));}),_1vg=new T(function(){var _1vh=hs_wordToWord64(4173248105),_1vi=_1vh,_1vj=hs_wordToWord64(4270398258),_1vk=_1vj;return [0,_1vi,_1vk,[0,_1vi,_1vk,_1oY,_1vf,_1ve],_9];}),_1vl=new T(function(){return E(E(_1vg)[3]);}),_1vm=new T(function(){return B(unCStr("GHC.Types"));}),_1vn=new T(function(){return B(unCStr("[]"));}),_1vo=new T(function(){var _1vp=hs_wordToWord64(4033920485),_1vq=_1vp,_1vr=hs_wordToWord64(786266835),_1vs=_1vr;return [0,_1vq,_1vs,[0,_1vq,_1vs,_1oY,_1vm,_1vn],_9];}),_1vt=[1,_1oZ,_9],_1vu=function(_1vv){var _1vw=E(_1vv);if(!_1vw[0]){return [0];}else{var _1vx=E(_1vw[1]);return [1,[0,_1vx[1],_1vx[2]],new T(function(){return B(_1vu(_1vw[2]));})];}},_1vy=new T(function(){var _1vz=E(_1vo),_1vA=E(_1vz[3]),_1vB=B(_e(_1vz[4],_1vt));if(!_1vB[0]){var _1vC=E(_1vA);}else{var _1vD=B(_1pt(new T(function(){return B(_8Q(B(_3d(_1pW,[1,[0,_1vA[1],_1vA[2]],new T(function(){return B(_1vu(_1vB));})]))));},1))),_1vC=E(_1vA);}var _1vE=_1vC,_1vF=_1vE;return _1vF;}),_1vG=[0,8],_1vH=[0,32],_1vI=function(_1vJ){return [1,_1vH,_1vJ];},_1vK=new T(function(){return B(unCStr(" -> "));}),_1vL=[0,9],_1vM=[0,93],_1vN=[0,91],_1vO=[0,41],_1vP=[0,44],_1vQ=function(_1vJ){return [1,_1vP,_1vJ];},_1vR=[0,40],_1vS=[0,0],_1vb=function(_1vT,_1vU,_1vV){var _1vW=E(_1vV);if(!_1vW[0]){return function(_1vX){return new F(function(){return _e(E(_1vU)[5],_1vX);});};}else{var _1vY=_1vW[1],_1vZ=function(_1w0){var _1w1=E(_1vU)[5],_1w2=function(_1w3){var _1w4=new T(function(){return B(_1v4(_1vI,_1vW));});return E(_1vT)[1]<=9?function(_1w5){return new F(function(){return _e(_1w1,[1,_1vH,new T(function(){return B(A(_1w4,[_1w5]));})]);});}:function(_1w6){return [1,_E,new T(function(){return B(_e(_1w1,[1,_1vH,new T(function(){return B(A(_1w4,[[1,_D,_1w6]]));})]));})];};},_1w7=E(_1w1);if(!_1w7[0]){return new F(function(){return _1w2(_);});}else{if(E(E(_1w7[1])[1])==40){var _1w8=E(_1w7[2]);if(!_1w8[0]){return new F(function(){return _1w2(_);});}else{if(E(E(_1w8[1])[1])==44){return function(_1w9){return [1,_1vR,new T(function(){return B(A(new T(function(){return B(_1v4(_1vQ,_1vW));}),[[1,_1vO,_1w9]]));})];};}else{return new F(function(){return _1w2(_);});}}}else{return new F(function(){return _1w2(_);});}}},_1wa=E(_1vW[2]);if(!_1wa[0]){var _1wb=E(_1vU),_1wc=E(_1vy),_1wd=hs_eqWord64(_1wb[1],_1wc[1]),_1we=_1wd;if(!E(_1we)){return new F(function(){return _1vZ(_);});}else{var _1wf=hs_eqWord64(_1wb[2],_1wc[2]),_1wg=_1wf;if(!E(_1wg)){return new F(function(){return _1vZ(_);});}else{return function(_1wh){return [1,_1vN,new T(function(){return B(A(new T(function(){var _1wi=E(_1vY);return B(_1vb(_1vS,_1wi[3],_1wi[4]));}),[[1,_1vM,_1wh]]));})];};}}}else{if(!E(_1wa[2])[0]){var _1wj=E(_1vU),_1wk=E(_1vl),_1wl=hs_eqWord64(_1wj[1],_1wk[1]),_1wm=_1wl;if(!E(_1wm)){return new F(function(){return _1vZ(_);});}else{var _1wn=hs_eqWord64(_1wj[2],_1wk[2]),_1wo=_1wn;if(!E(_1wo)){return new F(function(){return _1vZ(_);});}else{var _1wp=new T(function(){var _1wq=E(_1wa[1]);return B(_1vb(_1vG,_1wq[3],_1wq[4]));}),_1wr=new T(function(){var _1ws=E(_1vY);return B(_1vb(_1vL,_1ws[3],_1ws[4]));});return E(_1vT)[1]<=8?function(_1wt){return new F(function(){return A(_1wr,[new T(function(){return B(_e(_1vK,new T(function(){return B(A(_1wp,[_1wt]));},1)));})]);});}:function(_1wu){return [1,_E,new T(function(){return B(A(_1wr,[new T(function(){return B(_e(_1vK,new T(function(){return B(A(_1wp,[[1,_D,_1wu]]));},1)));})]));})];};}}}else{return new F(function(){return _1vZ(_);});}}}},_1wv=function(_1ww,_1wx){return new F(function(){return A(_1ww,[function(_){return new F(function(){return jsFind(toJSStr(E(_1wx)));});}]);});},_1wy=[0],_1wz=function(_1wA){return E(E(_1wA)[3]);},_1wB=new T(function(){return [0,"value"];}),_1wC=function(_1wD){return E(E(_1wD)[6]);},_1wE=function(_1wF){return E(E(_1wF)[1]);},_1wG=new T(function(){return B(unCStr("Char"));}),_1wH=new T(function(){var _1wI=hs_wordToWord64(3763641161),_1wJ=_1wI,_1wK=hs_wordToWord64(1343745632),_1wL=_1wK;return [0,_1wJ,_1wL,[0,_1wJ,_1wL,_1oY,_1vm,_1wG],_9];}),_1wM=function(_1wN){return E(_1wH);},_1wO=function(_1wP){return E(_1vo);},_1wQ=new T(function(){return B(_1pZ(_1wO,_1wM));}),_1wR=new T(function(){return B(A(_1wQ,[_]));}),_1wS=function(_1wT,_1wU,_1wV,_1wW,_1wX,_1wY,_1wZ,_1x0,_1x1){var _1x2=new T(function(){return B(A(_1wW,[_1wy]));});return new F(function(){return A(_1wU,[new T(function(){return B(_1wv(E(_1wT)[2],_1x1));}),function(_1x3){var _1x4=E(_1x3);return _1x4[0]==0?E(_1x2):B(A(_1wU,[new T(function(){return B(A(E(_1wT)[2],[function(_){var _1x5=jsGet(E(_1x4[1])[1],E(_1wB)[1]),_1x6=_1x5;return [1,new T(function(){return fromJSStr(_1x6);})];}]));}),function(_1x7){var _1x8=E(_1x7);if(!_1x8[0]){return E(_1x2);}else{var _1x9=_1x8[1];if(!E(new T(function(){var _1xa=B(A(_1wY,[_])),_1xb=E(_1wR),_1xc=hs_eqWord64(_1xa[1],_1xb[1]),_1xd=_1xc;if(!E(_1xd)){var _1xe=false;}else{var _1xf=hs_eqWord64(_1xa[2],_1xb[2]),_1xg=_1xf,_1xe=E(_1xg)==0?false:true;}var _1xh=_1xe,_1xi=_1xh;return _1xi;}))){var _1xj=function(_1xk){return new F(function(){return A(_1wW,[[1,_1x9,new T(function(){return B(A(new T(function(){return B(_1wC(_1x0));}),[new T(function(){return B(A(new T(function(){return B(_1wz(_1x0));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1x9,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1xl=B(A(_1wY,[_]));return B(A(_1vb,[_1vS,_1xl[3],_1xl[4],_9]));})));})));})));})]));})]));})]]);});},_1xm=B(A(new T(function(){return B(A(_1wE,[_1wZ,_4x]));}),[_1x9]));if(!_1xm[0]){return new F(function(){return _1xj(_);});}else{var _1xn=E(_1xm[1]);return E(_1xn[2])[0]==0?E(_1xm[2])[0]==0?B(A(_1wW,[[2,_1xn[1]]])):B(_1xj(_)):B(_1xj(_));}}else{return new F(function(){return A(_1wW,[[2,_1x9]]);});}}}]));}]);});},_1xo=function(_1xp){return E(E(_1xp)[10]);},_1xq=function(_1xr){return new F(function(){return _ID([1,function(_1xs){return new F(function(){return A(_Qd,[_1xs,function(_1xt){return E(new T(function(){return B(_Rt(function(_1xu){var _1xv=E(_1xu);return _1xv[0]==0?B(A(_1xr,[_1xv[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_RP(_1xw,_1xr))];}));});},_1xw=function(_1xx,_1xy){return new F(function(){return _1xq(_1xy);});},_1xz=[0,91],_1xA=[1,_1xz,_9],_1xB=function(_1xC,_1xD){var _1xE=function(_1xF,_1xG){return [1,function(_1xH){return new F(function(){return A(_Qd,[_1xH,function(_1xI){return E(new T(function(){return B(_Rt(function(_1xJ){var _1xK=E(_1xJ);if(_1xK[0]==2){var _1xL=E(_1xK[1]);if(!_1xL[0]){return [2];}else{var _1xM=_1xL[2];switch(E(E(_1xL[1])[1])){case 44:return E(_1xM)[0]==0?!E(_1xF)?[2]:E(new T(function(){return B(A(_1xC,[_RO,function(_1xN){return new F(function(){return _1xE(_LK,function(_1xO){return new F(function(){return A(_1xG,[[1,_1xN,_1xO]]);});});});}]));})):[2];case 93:return E(_1xM)[0]==0?E(new T(function(){return B(A(_1xG,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1xP=function(_1xQ){return new F(function(){return _ID([1,function(_1xR){return new F(function(){return A(_Qd,[_1xR,function(_1xS){return E(new T(function(){return B(_Rt(function(_1xT){var _1xU=E(_1xT);return _1xU[0]==2?!B(_3x(_1xU[1],_1xA))?[2]:E(new T(function(){return B(_ID(B(_1xE(_4y,_1xQ)),new T(function(){return B(A(_1xC,[_RO,function(_1xV){return new F(function(){return _1xE(_LK,function(_1xW){return new F(function(){return A(_1xQ,[[1,_1xV,_1xW]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_RP(function(_1xX,_1xY){return new F(function(){return _1xP(_1xY);});},_1xQ))];}));});};return new F(function(){return _1xP(_1xD);});},_1xZ=function(_1y0){return new F(function(){return _ID(B(_ID([1,function(_1y1){return new F(function(){return A(_Qd,[_1y1,function(_1y2){return E(new T(function(){return B(_Rt(function(_1y3){var _1y4=E(_1y3);return _1y4[0]==1?B(A(_1y0,[_1y4[1]])):[2];}));}));}]);});}],new T(function(){return B(_1xB(_1xw,_1y0));}))),new T(function(){return [1,B(_RP(_1y5,_1y0))];}));});},_1y5=function(_1y6,_1y7){return new F(function(){return _1xZ(_1y7);});},_1y8=new T(function(){return B(_1xZ(_Jm));}),_1y9=function(_1ya){return new F(function(){return _It(_1y8,_1ya);});},_1yb=new T(function(){return B(_1xq(_Jm));}),_1yc=function(_1ya){return new F(function(){return _It(_1yb,_1ya);});},_1yd=function(_1ye){return E(_1yc);},_1yf=[0,_1yd,_1y9,_1xw,_1y5],_1yg=function(_1yh){return E(E(_1yh)[4]);},_1yi=function(_1yj,_1yk,_1yl){return new F(function(){return _1xB(new T(function(){return B(_1yg(_1yj));}),_1yl);});},_1ym=function(_1yn){return function(_md){return new F(function(){return _It(new T(function(){return B(_1xB(new T(function(){return B(_1yg(_1yn));}),_Jm));}),_md);});};},_1yo=function(_1yp,_1yq){return function(_md){return new F(function(){return _It(new T(function(){return B(A(_1yg,[_1yp,_1yq,_Jm]));}),_md);});};},_1yr=function(_1ys){return [0,function(_1ya){return new F(function(){return _1yo(_1ys,_1ya);});},new T(function(){return B(_1ym(_1ys));}),new T(function(){return B(_1yg(_1ys));}),function(_1yt,_1ya){return new F(function(){return _1yi(_1ys,_1yt,_1ya);});}];},_1yu=new T(function(){return B(_1yr(_1yf));}),_1yv=function(_1yw,_1yx,_1yy){var _1yz=new T(function(){return B(_1xo(_1yw));}),_1yA=new T(function(){return B(_1uk(_1yy));}),_1yB=new T(function(){return B(_GB(_1yA));});return function(_1yC,_1yD){return new F(function(){return A(new T(function(){return B(_1bn(_1yA));}),[new T(function(){return B(A(new T(function(){return B(_1bn(_1yA));}),[new T(function(){return B(A(new T(function(){return B(_GB(_1yA));}),[[0,_1yD,_1yD]]));}),function(_1yE){var _1yF=new T(function(){return E(E(_1yE)[1]);}),_1yG=new T(function(){return E(E(_1yF)[2]);});return new F(function(){return A(new T(function(){return B(_1bn(_1yA));}),[new T(function(){return B(A(new T(function(){return B(_GB(_1yA));}),[[0,_6B,new T(function(){var _1yH=E(_1yF);return [0,_1yH[1],new T(function(){return [0,E(_1yG)[1]+1|0];}),_1yH[3],_1yH[4],_1yH[5],_1yH[6],_1yH[7]];})]]));}),function(_1yI){return new F(function(){return A(new T(function(){return B(_GB(_1yA));}),[[0,[1,_6I,new T(function(){return B(_e(B(_F(0,E(_1yG)[1],_9)),new T(function(){return E(E(_1yF)[1]);},1)));})],new T(function(){return E(E(_1yI)[2]);})]]);});}]);});}]));}),function(_1yJ){var _1yK=new T(function(){return E(E(_1yJ)[1]);});return new F(function(){return A(new T(function(){return B(_1bn(_1yA));}),[new T(function(){return B(A(_1wS,[new T(function(){return B(_1uu(new T(function(){return B(_1uV(_1yA));}),_1yy));}),function(_1yL,_1qt,_1yM){return new F(function(){return _1uy(_1yA,_1yL,_1qt,_1yM);});},function(_1yL,_1qt,_1yM){return new F(function(){return _1uK(_1yA,_1yL,_1qt,_1yM);});},function(_1qt,_1yM){return new F(function(){return _1uZ(_1yA,_1qt,_1yM);});},function(_1yM){return new F(function(){return _1uR(_1yA,_1yM);});},_1wQ,_1yu,_1yw,_1yK,new T(function(){return E(E(_1yJ)[2]);})]));}),function(_1yN){var _1yO=E(_1yN),_1yP=_1yO[2],_1yQ=E(_1yO[1]);switch(_1yQ[0]){case 0:return new F(function(){return A(_1yB,[[0,[0,new T(function(){return B(A(_1yz,[_1yK,_1yC]));}),_4O],_1yP]]);});break;case 1:return new F(function(){return A(_1yB,[[0,[0,new T(function(){return B(A(_1yz,[_1yK,_1yQ[1]]));}),_4O],_1yP]]);});break;default:var _1yR=_1yQ[1];return new F(function(){return A(_1yB,[[0,[0,new T(function(){return B(A(_1yz,[_1yK,_1yR]));}),[1,_1yR]],_1yP]]);});}}]);});}]);});};},_1yS=new T(function(){return B(_1yv(_1sA,_1sL,_1uj));}),_1yT=function(_1yU){return E(E(_1yU)[2]);},_1yV=function(_1yW){return E(E(_1yW)[1]);},_1yX=function(_1yY,_1yZ,_1z0){return function(_1z1,_){var _1z2=B(A(_1yZ,[_1z1,_])),_1z3=_1z2,_1z4=E(_1z3),_1z5=E(_1z4[1]),_1z6=new T(function(){return B(A(new T(function(){return B(_1yT(_1yY));}),[_1z0,function(_){var _1z7=E(E(_1z1)[4]),_1z8=B(A(_1z7[1],[_])),_1z9=_1z8,_1za=E(_1z9);if(!_1za[0]){return _6B;}else{var _1zb=B(A(_1z7[2],[_1za[1],_])),_1zc=_1zb;return _6B;}}]));});return [0,[0,function(_1zd,_){var _1ze=B(A(_1z5[1],[_1zd,_])),_1zf=_1ze,_1zg=E(_1zf),_1zh=E(_1z6),_1zi=jsSetCB(_1zg[1],toJSStr(E(new T(function(){return B(A(_1yV,[_1yY,_1z0]));}))),_1z6),_1zj=_1zi;return _1zg;},_1z5[2]],_1z4[2]];};},_1zk=function(_1zl){while(1){var _1zm=(function(_1zn){var _1zo=E(_1zn);switch(_1zo[0]){case 0:var _1zp=_1zo[1];return new F(function(){return unAppCStr("Unable to unify ",new T(function(){return B(_e(B(A(_bT,[_1zp,_1zo[2]])),new T(function(){return B(unAppCStr(" with ",new T(function(){return B(A(_bT,[_1zp,_1zo[3]]));})));},1)));}));});break;case 1:_1zl=_1zo[3];return null;case 2:var _1zq=_1zo[1];return new F(function(){return unAppCStr("When matching ",new T(function(){return B(_e(B(A(_bT,[_1zq,_1zo[3]])),new T(function(){return B(unAppCStr(" with ",new T(function(){return B(_e(B(A(_bT,[_1zq,_1zo[4]])),new T(function(){return B(unAppCStr(",\n",new T(function(){return B(_1zk(_1zo[2]));})));},1)));})));},1)));}));});break;default:return new F(function(){return unAppCStr("Cannot construct infinite type ",new T(function(){return B(_e(B(A(_bT,[_1zo[1],_1zo[3]])),new T(function(){return B(unAppCStr(" = ",new T(function(){return B(A(_bT,[_1zo[2],_1zo[4]]));})));},1)));}));});}})(_1zl);if(_1zm!=null){return _1zm;}}},_1zr=function(_1zs){return function(_md,_me){return new F(function(){return _1n3(_6v,new T(function(){return B(_1zk(_1zs));}),_md,_me);});};},_1zt=new T(function(){return B(unCStr("errormsg"));}),_1zu=function(_A1,_){return new F(function(){return _1n3(_6v,_9,_A1,_);});},_1zv=new T(function(){return B(unCStr("hr"));}),_1zw=function(_1zx,_){var _1zy=jsCreateElem(toJSStr(E(_1zv))),_1zz=_1zy,_1zA=jsAppendChild(_1zz,E(_1zx)[1]);return [0,_1zz];},_1zB=[0,10006],_1zC=[1,_1zB,_9],_1zD=[0,10003],_1zE=[1,_1zD,_9],_1zF=function(_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM,_1zN,_1zO,_1zP,_1zQ,_1zR,_1zS){return function(_md,_me){return new F(function(){return _1n3(_7s,new T(function(){var _1zT=function(_1zU,_1zV,_1zW){var _1zX=B(_uN(_1zG,_1zH,_1zI,_1zJ,_1zK,_1zL,_1zM,_1zU,_1zO,_1zP,_1zQ,new T(function(){return E(E(_1zR)[2]);}),_1zV,_1zW));return _1zX[0]==0?function(_md,_me){return new F(function(){return _1n3(_7s,function(_1zY,_){var _1zZ=B(_1n3(_6v,_1zC,_1zY,_)),_1A0=_1zZ,_1A1=B(_1n3(_7s,function(_1A2,_){return new F(function(){return _1sg(new T(function(){var _1A3=B(_3d(_1zr,_1zX[1]));return _1A3[0]==0?[0]:[1,_1A3[1],new T(function(){return B(_3h(_1zw,_1A3[2]));})];}),_1A2,_);});},_1zY,_)),_1A4=_1A1,_1A5=B(A(_6C,[_6P,_1A4,_zS,_1zt,_])),_1A6=_1A5;return _1zY;},_md,_me);});}:function(_md,_me){return new F(function(){return _1n3(_7s,function(_1A7,_){var _1A8=B(_1n3(_6v,_1zE,_1A7,_)),_1A9=_1A8,_1Aa=B(_1n3(_6v,new T(function(){var _1Ab=E(_1zX[1]);return B(_bV(new T(function(){return B(_bI(_1zM,_1zL,_1zK,_1zJ,_1zI,_1zG,_1zH));}),new T(function(){return B(_3W(_1zM,_1zL,_1zK,_1zJ,_1zI,_1zG,_1zH));}),_1Ab[1],_1Ab[2]));}),_1A7,_)),_1Ac=_1Aa,_1Ad=B(A(_6C,[_6P,_1Ac,_zS,_1zt,_])),_1Ae=_1Ad;return _1A7;},_md,_me);});};},_1Af=function(_1Ag){var _1Ah=E(_1Ag);return _1Ah[0]==0?E(_1nn):function(_1Ai,_){var _1Aj=B(A(new T(function(){var _1Ak=E(_1Ah[1]);switch(_1Ak[0]){case 0:var _1Al=E(_1Ak[1]),_1Am=B(_1zT(_1zN,_1Al[1],_1Al[2]));break;case 1:var _1An=E(_1Ak[1]),_1Am=B(_1zT(_1zN,_1An[1],_1An[2]));break;case 2:var _1Am=function(_md,_me){return new F(function(){return _1n3(_7s,function(_1Ao,_){var _1Ap=B(_1n3(_6v,_1zC,_1Ao,_)),_1Aq=_1Ap,_1Ar=B(_1n3(_6v,_1Ak[1],_1Ao,_)),_1As=_1Ar,_1At=B(A(_6C,[_6P,_1As,_zS,_1zt,_])),_1Au=_1At;return _1Ao;},_md,_me);});};break;default:var _1Am=E(_1zu);}return _1Am;}),[_1Ai,_])),_1Av=_1Aj,_1Aw=B(A(new T(function(){return B(_1Af(_1Ah[2]));}),[_1Ai,_])),_1Ax=_1Aw;return _1Ai;};};return B(_1Af(_1zS));}),_md,_me);});};},_1Ay=function(_1Az,_1AA,_1AB,_1AC,_1AD,_1AE,_1AF,_1AG,_1AH,_1AI,_1AJ){return function(_1AK,_1AL){return function(_md,_me){return new F(function(){return _7u(function(_1AM,_){var _1AN=B(A(new T(function(){return B(_1yX(_6u,new T(function(){return B(_1yX(_6u,new T(function(){return B(A(_1yS,[_1AL]));}),_1p));}),_1o));}),[_1AM,_])),_1AO=_1AN,_1AP=E(_1AO),_1AQ=E(_1AP[1]);return [0,[0,function(_1AR,_){var _1AS=B(A(_1AQ[1],[_1AR,_])),_1AT=_1AS,_1AU=B(A(_6C,[_6P,_1AT,_zS,_zT,_])),_1AV=_1AU;return _1AT;},_1AQ[2]],_1AP[2]];},function(_1AW){var _1AX=new T(function(){var _1AY=B(_10Z(_ZV,_11l,[0,new T(function(){return B(_e(_1AW,_1oH));}),E(_ZQ),E(_6B)]));if(!_1AY[0]){var _1AZ=E(_1AY[1]);if(!_1AZ[0]){var _1B0=E(E(_1AZ[1])[1]);}else{var _1B0=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1AZ[1]));})));})],_9],_9];}var _1B1=_1B0;}else{var _1B2=E(_1AY[1]);if(!_1B2[0]){var _1B3=E(E(_1B2[1])[1]);}else{var _1B3=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_bh(_1B2[1]));})));})],_9],_9];}var _1B1=_1B3;}return _1B1;});return function(_md,_me){return new F(function(){return _7u(_A0,function(_1B4,_1B5,_){return new F(function(){return _7u(_A6,function(_1B6,_1B7,_){return new F(function(){return _7u(_Ab,function(_1B8,_1B9,_){return new F(function(){return _7u(function(_1Ba,_){return [0,[0,function(_1Bb,_){var _1Bc=B(_1n3(_6v,_9,_1Bb,_)),_1Bd=_1Bc,_1Be=B(A(_6C,[_6P,_1Bd,_6O,_1B4,_])),_1Bf=_1Be,_1Bg=B(A(_6C,[_6P,_1Bd,_zS,_Ac,_])),_1Bh=_1Bg;return _1Bd;},_Ah],_1Ba];},function(_1Bi,_1Bj,_){return new F(function(){return _7u(function(_1Bk,_){return [0,[0,function(_1Bl,_){var _1Bm=B(_7i(_7s,new T(function(){return B(_1ox(_1AX));}),_1Bl,_)),_1Bn=_1Bm,_1Bo=B(A(_6C,[_6P,_1Bn,_6O,_1B6,_])),_1Bp=_1Bo,_1Bq=B(A(_6C,[_6P,_1Bn,_zS,_Ad,_])),_1Br=_1Bq;return _1Bn;},_Ah],_1Bk];},function(_1Bs){return E(new T(function(){var _1Bt=E(new T(function(){return B(_zA(_1Az,_1AA,_1AB,_1AC,_1AD,_1AE,_1AF,_1AG,_1AH,_1AI,_1AJ,_1AX,new T(function(){return E(E(_1AK)[1]);}),new T(function(){return E(E(_1AK)[2]);})));}));if(!_1Bt[0]){var _1Bu=function(_1Bv,_){return [0,[0,function(_1Bw,_){var _1Bx=B(A(new T(function(){return B(_1zF(_1Az,_1AA,_1AB,_1AC,_1AD,_1AE,_1AF,_1AG,_1AH,_1AI,_1AJ,_1AK,new T(function(){return B(_wg(_1Bt[1]));},1)));}),[_1Bw,_])),_1By=_1Bx,_1Bz=B(A(_6C,[_6P,_1By,_6O,_1B8,_])),_1BA=_1Bz,_1BB=B(A(_6C,[_6P,_1By,_zS,_Ae,_])),_1BC=_1BB;return _1By;},_Ah],_1Bv];};}else{var _1BD=E(_1Bt[1]);if(!_1BD[0]){var _1BE=function(_A1,_){return new F(function(){return _Am(_1B4,_zR,_Aj,_A1,_);});};}else{var _1BE=function(_md,_me){return new F(function(){return _Am(_1B4,_zR,function(_1BF,_){return [0,[0,function(_A1,_){return new F(function(){return _7i(_6v,new T(function(){var _1BG=E(_1BD[1]);return B(_bV(new T(function(){return B(_bI(_1AF,_1AE,_1AD,_1AC,_1AB,_1Az,_1AA));}),new T(function(){return B(_3W(_1AF,_1AE,_1AD,_1AC,_1AB,_1Az,_1AA));}),_1BG[1],_1BG[2]));}),_A1,_);});},_Ah],_1BF];},_md,_me);});};}var _1Bu=_1BE;}return _1Bu;}));},_1Bj,_);});},_1B9,_);});},_1B7,_);});},_1B5,_);});},_md,_me);});};},_md,_me);});};};},_1BH=function(_1BI,_1BJ,_1BK,_1BL){return new F(function(){return A(_1BI,[function(_){var _1BM=jsSet(E(_1BJ)[1],toJSStr(E(_1BK)),toJSStr(E(_1BL)));return _6B;}]);});},_1BN=new T(function(){return B(unCStr("innerHTML"));}),_1BO=new T(function(){return B(unCStr("textContent"));}),_1BP=function(_1BQ,_1BR,_1BS,_1BT,_1BU,_1BV,_1BW,_1BX,_1BY,_1BZ,_1C0,_1C1,_1C2,_){var _1C3=B(_1j(_1C2,_1BO,_)),_1C4=_1C3,_1C5=[0,_1C2],_1C6=B(A(_1BH,[_6P,_1C5,_1BN,_9,_])),_1C7=_1C6,_1C8=E(_51)[1],_1C9=takeMVar(_1C8),_1Ca=_1C9,_1Cb=B(A(_1Ay,[_1BQ,_1BR,_1BS,_1BT,_1BU,_1BV,_1BW,_1BX,_1BY,_1BZ,_1C0,_1C1,_1C4,_1Ca,_])),_1Cc=_1Cb,_1Cd=E(_1Cc),_1Ce=E(_1Cd[1]),_=putMVar(_1C8,_1Cd[2]),_1Cf=B(A(_1Ce[1],[_1C5,_])),_1Cg=_1Cf;return _1Ce[2];},_1Ch=function(_){var _1Ci=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1Cj=_1Ci;return _6B;},_1Ck=new T(function(){return B(unCStr("embedding complete"));}),_1Cl=new T(function(){return B(unCStr("proofbox"));}),_1Cm=function(_1Cn,_1Co,_1Cp,_1Cq,_1Cr,_1Cs,_1Ct,_1Cu,_1Cv,_1Cw,_1Cx,_1Cy,_){var _1Cz=jsElemsByClassName(toJSStr(E(_1Cl))),_1CA=_1Cz,_1CB=B((function(_1CC,_){while(1){var _1CD=E(_1CC);if(!_1CD[0]){return _6B;}else{var _1CE=B(_1BP(_1Cn,_1Co,_1Cp,_1Cq,_1Cr,_1Cs,_1Ct,_1Cu,_1Cv,_1Cw,_1Cx,_1Cy,E(_1CD[1])[1],_)),_1CF=_1CE;_1CC=_1CD[2];continue;}}})(_1CA,_)),_1CG=_1CB,_1CH=jsLog(toJSStr(E(_1Ck))),_1CI=jsSetTimeout(60,_1Ch);return _6B;},_1CJ=new T(function(){return B(unCStr("ADD"));}),_1CK=new T(function(){return B(unCStr("ADJ"));}),_1CL=[0,1],_1CM=[1,_1CL],_1CN=[1,_1CM],_1CO=[0,_1CL],_1CP=[1,_1CO],_1CQ=new T(function(){return B(unCStr("DN"));}),_1CR=new T(function(){return B(_3x(_9,_1CQ));}),_1CS=new T(function(){return B(unCStr("MTP"));}),_1CT=new T(function(){return B(unCStr("MT"));}),_1CU=new T(function(){return B(unCStr("MP"));}),_1CV=new T(function(){return B(unCStr("ID"));}),_1CW=new T(function(){return B(unCStr("DD"));}),_1CX=new T(function(){return B(unCStr("CD"));}),_1CY=[0,2],_1CZ=[1,_1CY],_1D0=[1,_1CZ],_1D1=[0,_1CY],_1D2=[1,_1D1],_1D3=function(_1D4){if(!B(_3x(_1D4,_1CJ))){if(!B(_3x(_1D4,_1CK))){if(!B(_3x(_1D4,_1CX))){if(!B(_3x(_1D4,_1CW))){if(!B(_3x(_1D4,_1CV))){if(!B(_3x(_1D4,_1CU))){if(!B(_3x(_1D4,_1CT))){if(!B(_3x(_1D4,_1CS))){var _1D5=E(_1D4);return _1D5[0]==0?!E(_1CR)?[0]:E(_1CP):E(E(_1D5[1])[1])==83?E(_1D5[2])[0]==0?E(_1CP):!B(_3x(_1D5,_1CQ))?[0]:E(_1CP):!B(_3x(_1D5,_1CQ))?[0]:E(_1CP);}else{return E(_1D2);}}else{return E(_1D2);}}else{return E(_1D2);}}else{return E(_1D0);}}else{return E(_1CN);}}else{return E(_1CN);}}else{return E(_1D2);}}else{return E(_1CP);}},_1D6=function(_1D7){return E(E(_1D7)[2]);},_1D8=function(_1D9,_1Da,_1Db){while(1){var _1Dc=E(_1Da);if(!_1Dc[0]){return E(_1Db)[0]==0?1:0;}else{var _1Dd=E(_1Db);if(!_1Dd[0]){return 2;}else{var _1De=B(A(_1D6,[_1D9,_1Dc[1],_1Dd[1]]));if(_1De==1){_1Da=_1Dc[2];_1Db=_1Dd[2];continue;}else{return E(_1De);}}}}},_1Df=function(_1Dg){return E(E(_1Dg)[3]);},_1Dh=function(_1Di,_1Dj,_1Dk,_1Dl,_1Dm){switch(B(_1D8(_1Di,_1Dj,_1Dl))){case 0:return true;case 1:return new F(function(){return A(_1Df,[_1Di,_1Dk,_1Dm]);});break;default:return false;}},_1Dn=function(_1Do,_1Dp,_1Dq,_1Dr){var _1Ds=E(_1Dq),_1Dt=E(_1Dr);return new F(function(){return _1Dh(_1Dp,_1Ds[1],_1Ds[2],_1Dt[1],_1Dt[2]);});},_1Du=function(_1Dv){return E(E(_1Dv)[6]);},_1Dw=function(_1Dx,_1Dy,_1Dz,_1DA,_1DB){switch(B(_1D8(_1Dx,_1Dy,_1DA))){case 0:return true;case 1:return new F(function(){return A(_1Du,[_1Dx,_1Dz,_1DB]);});break;default:return false;}},_1DC=function(_1DD,_1DE,_1DF,_1DG){var _1DH=E(_1DF),_1DI=E(_1DG);return new F(function(){return _1Dw(_1DE,_1DH[1],_1DH[2],_1DI[1],_1DI[2]);});},_1DJ=function(_1DK){return E(E(_1DK)[5]);},_1DL=function(_1DM,_1DN,_1DO,_1DP,_1DQ){switch(B(_1D8(_1DM,_1DN,_1DP))){case 0:return false;case 1:return new F(function(){return A(_1DJ,[_1DM,_1DO,_1DQ]);});break;default:return true;}},_1DR=function(_1DS,_1DT,_1DU,_1DV){var _1DW=E(_1DU),_1DX=E(_1DV);return new F(function(){return _1DL(_1DT,_1DW[1],_1DW[2],_1DX[1],_1DX[2]);});},_1DY=function(_1DZ){return E(E(_1DZ)[4]);},_1E0=function(_1E1,_1E2,_1E3,_1E4,_1E5){switch(B(_1D8(_1E1,_1E2,_1E4))){case 0:return false;case 1:return new F(function(){return A(_1DY,[_1E1,_1E3,_1E5]);});break;default:return true;}},_1E6=function(_1E7,_1E8,_1E9,_1Ea){var _1Eb=E(_1E9),_1Ec=E(_1Ea);return new F(function(){return _1E0(_1E8,_1Eb[1],_1Eb[2],_1Ec[1],_1Ec[2]);});},_1Ed=function(_1Ee,_1Ef,_1Eg,_1Eh,_1Ei){switch(B(_1D8(_1Ee,_1Ef,_1Eh))){case 0:return 0;case 1:return new F(function(){return A(_1D6,[_1Ee,_1Eg,_1Ei]);});break;default:return 2;}},_1Ej=function(_1Ek,_1El,_1Em,_1En){var _1Eo=E(_1Em),_1Ep=E(_1En);return new F(function(){return _1Ed(_1El,_1Eo[1],_1Eo[2],_1Ep[1],_1Ep[2]);});},_1Eq=function(_1Er,_1Es,_1Et,_1Eu){var _1Ev=E(_1Et),_1Ew=_1Ev[1],_1Ex=_1Ev[2],_1Ey=E(_1Eu),_1Ez=_1Ey[1],_1EA=_1Ey[2];switch(B(_1D8(_1Es,_1Ew,_1Ez))){case 0:return [0,_1Ez,_1EA];case 1:return !B(A(_1Du,[_1Es,_1Ex,_1EA]))?[0,_1Ew,_1Ex]:[0,_1Ez,_1EA];default:return [0,_1Ew,_1Ex];}},_1EB=function(_1EC,_1ED,_1EE,_1EF){var _1EG=E(_1EE),_1EH=_1EG[1],_1EI=_1EG[2],_1EJ=E(_1EF),_1EK=_1EJ[1],_1EL=_1EJ[2];switch(B(_1D8(_1ED,_1EH,_1EK))){case 0:return [0,_1EH,_1EI];case 1:return !B(A(_1Du,[_1ED,_1EI,_1EL]))?[0,_1EK,_1EL]:[0,_1EH,_1EI];default:return [0,_1EK,_1EL];}},_1EM=function(_1EN,_1EO){return [0,_1EN,function(_cr,_cs){return new F(function(){return _1Ej(_1EN,_1EO,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Dn(_1EN,_1EO,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1E6(_1EN,_1EO,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1DR(_1EN,_1EO,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1DC(_1EN,_1EO,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Eq(_1EN,_1EO,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1EB(_1EN,_1EO,_cr,_cs);});}];},_1EP=function(_1EQ,_1ER,_1ES,_1ET){return !B(A(_1EQ,[_1ES,_1ET]))?B(_AT(B(A(_1ER,[_1ES,_jh])),B(A(_1ER,[_1ET,_jh]))))==2?false:true:false;},_1EU=function(_1EV,_1EW,_1EX,_1EY){return new F(function(){return _1EP(E(_1EV)[1],_1EW,_1EX,_1EY);});},_1EZ=function(_1F0,_1F1,_1F2,_1F3){return B(_AT(B(A(_1F1,[_1F2,_jh])),B(A(_1F1,[_1F3,_jh]))))==2?false:true;},_1F4=function(_1F5,_1F6,_1F7,_1F8){return !B(A(_1F5,[_1F7,_1F8]))?B(_AT(B(A(_1F6,[_1F7,_jh])),B(A(_1F6,[_1F8,_jh]))))==2?true:false:false;},_1F9=function(_1Fa,_1Fb,_1Fc,_1Fd){return new F(function(){return _1F4(E(_1Fa)[1],_1Fb,_1Fc,_1Fd);});},_1Fe=function(_1Ff,_1Fg,_1Fh,_1Fi){return !B(A(_1Ff,[_1Fh,_1Fi]))?B(_AT(B(A(_1Fg,[_1Fh,_jh])),B(A(_1Fg,[_1Fi,_jh]))))==2?true:false:true;},_1Fj=function(_1Fk,_1Fl,_1Fm,_1Fn){return new F(function(){return _1Fe(E(_1Fk)[1],_1Fl,_1Fm,_1Fn);});},_1Fo=function(_1Fp,_1Fq,_1Fr,_1Fs){return !B(A(_1Fp,[_1Fr,_1Fs]))?B(_AT(B(A(_1Fq,[_1Fr,_jh])),B(A(_1Fq,[_1Fs,_jh]))))==2?2:0:1;},_1Ft=function(_1Fu,_1Fv,_1Fw,_1Fx){return new F(function(){return _1Fo(E(_1Fu)[1],_1Fv,_1Fw,_1Fx);});},_1Fy=function(_1Fz,_1FA,_1FB,_1FC){return B(_AT(B(A(_1FA,[_1FB,_jh])),B(A(_1FA,[_1FC,_jh]))))==2?E(_1FB):E(_1FC);},_1FD=function(_1FE,_1FF,_1FG,_1FH){return B(_AT(B(A(_1FF,[_1FG,_jh])),B(A(_1FF,[_1FH,_jh]))))==2?E(_1FH):E(_1FG);},_1FI=function(_1FJ,_1FK){return [0,_1FJ,function(_44,_45){return new F(function(){return _1Ft(_1FJ,_1FK,_44,_45);});},function(_44,_45){return new F(function(){return _1EU(_1FJ,_1FK,_44,_45);});},function(_44,_45){return new F(function(){return _1Fj(_1FJ,_1FK,_44,_45);});},function(_44,_45){return new F(function(){return _1F9(_1FJ,_1FK,_44,_45);});},function(_44,_45){return new F(function(){return _1EZ(_1FJ,_1FK,_44,_45);});},function(_44,_45){return new F(function(){return _1Fy(_1FJ,_1FK,_44,_45);});},function(_44,_45){return new F(function(){return _1FD(_1FJ,_1FK,_44,_45);});}];},_1FL=function(_1FM,_1FN,_1FO,_1FP,_1FQ,_1FR,_1FS){var _1FT=function(_1FU,_1FV){return new F(function(){return _2W(_1FM,_1FN,_1FO,_1FQ,_1FP,_1FS,_1FR,_1FU);});};return function(_1FW,_1FX){var _1FY=E(_1FW);if(!_1FY[0]){var _1FZ=E(_1FX);return _1FZ[0]==0?B(_AT(B(_1r(_1FY[1])),B(_1r(_1FZ[1]))))==2?false:true:true;}else{var _1G0=E(_1FX);return _1G0[0]==0?false:B(_1D8(new T(function(){return B(_1FI(new T(function(){return B(_jm(_1FT));}),_1FT));}),_1FY[1],_1G0[1]))==2?false:true;}};},_1G1=function(_1G2,_1G3,_1G4,_1G5,_1G6,_1G7,_1G8,_1G9,_1Ga,_1Gb){return !B(A(_1FL,[_1G3,_1G4,_1G5,_1G6,_1G7,_1G8,_1G9,_1Ga,_1Gb]))?E(_1Ga):E(_1Gb);},_1Gc=function(_1Gd,_1Ge,_1Gf,_1Gg,_1Gh,_1Gi,_1Gj,_1Gk,_1Gl,_1Gm){return !B(A(_1FL,[_1Ge,_1Gf,_1Gg,_1Gh,_1Gi,_1Gj,_1Gk,_1Gl,_1Gm]))?E(_1Gm):E(_1Gl);},_1Gn=function(_1Go,_1Gp,_1Gq,_1Gr,_1Gs,_1Gt,_1Gu){var _1Gv=function(_1Gw,_1Gx){return new F(function(){return _2W(_1Go,_1Gp,_1Gq,_1Gs,_1Gr,_1Gu,_1Gt,_1Gw);});};return function(_1Gy,_1Gz){var _1GA=E(_1Gy);if(!_1GA[0]){var _1GB=_1GA[1],_1GC=E(_1Gz);if(!_1GC[0]){var _1GD=_1GC[1];return B(_cH(_1GB,_1GD,_1))[0]==0?B(_AT(B(_1r(_1GB)),B(_1r(_1GD))))==2?false:true:false;}else{return true;}}else{var _1GE=E(_1Gz);return _1GE[0]==0?false:B(_1D8(new T(function(){return B(_1FI(new T(function(){return B(_jm(_1Gv));}),_1Gv));}),_1GA[1],_1GE[1]))==0?true:false;}};},_1GF=function(_1GG,_1GH,_1GI,_1GJ,_1GK,_1GL,_1GM){var _1GN=function(_1GO,_1GP){return new F(function(){return _2W(_1GG,_1GH,_1GI,_1GK,_1GJ,_1GM,_1GL,_1GO);});};return function(_1GQ,_1GR){var _1GS=E(_1GQ);if(!_1GS[0]){var _1GT=_1GS[1],_1GU=E(_1GR);if(!_1GU[0]){var _1GV=_1GU[1];return B(_cH(_1GT,_1GV,_1))[0]==0?B(_AT(B(_1r(_1GT)),B(_1r(_1GV))))==2?true:false:false;}else{return false;}}else{var _1GW=E(_1GR);return _1GW[0]==0?true:B(_1D8(new T(function(){return B(_1FI(new T(function(){return B(_jm(_1GN));}),_1GN));}),_1GS[1],_1GW[1]))==2?true:false;}};},_1GX=function(_1GY,_1GZ,_1H0,_1H1,_1H2,_1H3,_1H4){var _1H5=function(_1H6,_1H7){return new F(function(){return _2W(_1GY,_1GZ,_1H0,_1H2,_1H1,_1H4,_1H3,_1H6);});};return function(_1H8,_1H9){var _1Ha=E(_1H8);if(!_1Ha[0]){var _1Hb=_1Ha[1],_1Hc=E(_1H9);if(!_1Hc[0]){var _1Hd=_1Hc[1];return B(_cH(_1Hb,_1Hd,_1))[0]==0?B(_AT(B(_1r(_1Hb)),B(_1r(_1Hd))))==2?true:false:true;}else{return false;}}else{var _1He=E(_1H9);return _1He[0]==0?true:B(_1D8(new T(function(){return B(_1FI(new T(function(){return B(_jm(_1H5));}),_1H5));}),_1Ha[1],_1He[1]))==0?false:true;}};},_1Hf=function(_1Hg,_1Hh,_1Hi,_1Hj,_1Hk,_1Hl,_1Hm){var _1Hn=function(_1Ho,_1Hp){return new F(function(){return _2W(_1Hg,_1Hh,_1Hi,_1Hk,_1Hj,_1Hm,_1Hl,_1Ho);});};return function(_1Hq,_1Hr){var _1Hs=E(_1Hq);if(!_1Hs[0]){var _1Ht=_1Hs[1],_1Hu=E(_1Hr);if(!_1Hu[0]){var _1Hv=_1Hu[1];return B(_cH(_1Ht,_1Hv,_1))[0]==0?B(_AT(B(_1r(_1Ht)),B(_1r(_1Hv))))==2?2:0:1;}else{return 0;}}else{var _1Hw=E(_1Hr);return _1Hw[0]==0?2:B(_1D8(new T(function(){return B(_1FI(new T(function(){return B(_jm(_1Hn));}),_1Hn));}),_1Hs[1],_1Hw[1]));}};},_1Hx=function(_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF){return [0,_1Hy,new T(function(){return B(_1Hf(_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF));}),new T(function(){return B(_1Gn(_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF));}),new T(function(){return B(_1GX(_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF));}),new T(function(){return B(_1GF(_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF));}),new T(function(){return B(_1FL(_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF));}),function(_44,_45){return new F(function(){return _1G1(_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_44,_45);});},function(_44,_45){return new F(function(){return _1Gc(_1Hy,_1Hz,_1HA,_1HB,_1HC,_1HD,_1HE,_1HF,_44,_45);});}];},_1HG=new T(function(){return B(_3W(_Q,_u,_Q,_Q,_N,_2,_15));}),_1HH=new T(function(){return B(_1Hx(_1HG,_Q,_u,_Q,_Q,_N,_15,_2));}),_1HI=new T(function(){return B(_cF(_1HG));}),_1HJ=new T(function(){return B(_1EM(_1HI,_1HH));}),_1HK=function(_1HL,_1HM,_1HN,_1HO){var _1HP=E(_1HN),_1HQ=E(_1HO);return new F(function(){return _1Dh(_1HM,_1HP[1],_1HP[2],_1HQ[1],_1HQ[2]);});},_1HR=function(_1HS,_1HT,_1HU,_1HV){var _1HW=E(_1HU),_1HX=E(_1HV);return new F(function(){return _1Dw(_1HT,_1HW[1],_1HW[2],_1HX[1],_1HX[2]);});},_1HY=function(_1HZ,_1I0,_1I1,_1I2){var _1I3=E(_1I1),_1I4=E(_1I2);return new F(function(){return _1DL(_1I0,_1I3[1],_1I3[2],_1I4[1],_1I4[2]);});},_1I5=function(_1I6,_1I7,_1I8,_1I9){var _1Ia=E(_1I8),_1Ib=E(_1I9);return new F(function(){return _1E0(_1I7,_1Ia[1],_1Ia[2],_1Ib[1],_1Ib[2]);});},_1Ic=function(_1Id,_1Ie,_1If,_1Ig){var _1Ih=E(_1If),_1Ii=E(_1Ig);return new F(function(){return _1Ed(_1Ie,_1Ih[1],_1Ih[2],_1Ii[1],_1Ii[2]);});},_1Ij=function(_1Ik,_1Il,_1Im,_1In){var _1Io=E(_1Im),_1Ip=_1Io[1],_1Iq=_1Io[2],_1Ir=E(_1In),_1Is=_1Ir[1],_1It=_1Ir[2];switch(B(_1D8(_1Il,_1Ip,_1Is))){case 0:return [0,_1Is,_1It];case 1:return !B(A(_1Du,[_1Il,_1Iq,_1It]))?[0,_1Ip,_1Iq]:[0,_1Is,_1It];default:return [0,_1Ip,_1Iq];}},_1Iu=function(_1Iv,_1Iw,_1Ix,_1Iy){var _1Iz=E(_1Ix),_1IA=_1Iz[1],_1IB=_1Iz[2],_1IC=E(_1Iy),_1ID=_1IC[1],_1IE=_1IC[2];switch(B(_1D8(_1Iw,_1IA,_1ID))){case 0:return [0,_1IA,_1IB];case 1:return !B(A(_1Du,[_1Iw,_1IB,_1IE]))?[0,_1ID,_1IE]:[0,_1IA,_1IB];default:return [0,_1ID,_1IE];}},_1IF=function(_1IG,_1IH){return [0,_1IG,function(_cr,_cs){return new F(function(){return _1Ic(_1IG,_1IH,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1HK(_1IG,_1IH,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1I5(_1IG,_1IH,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1HY(_1IG,_1IH,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1HR(_1IG,_1IH,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Ij(_1IG,_1IH,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1Iu(_1IG,_1IH,_cr,_cs);});}];},_1II=function(_1IJ,_1IK){return B(_AT(_1IJ,_1IK))==0?false:true;},_1IL=function(_1IM){return E(E(_1IM)[1]);},_1IN=function(_1IO){return function(_1IP,_1IQ){var _1IR=E(_1IP),_1IS=E(_1IQ);switch(B(_1D8(new T(function(){return B(_1IF(new T(function(){return B(_cp(new T(function(){return B(_1IL(_1IO));})));}),_1IO));}),_1IR[1],_1IS[1]))){case 0:return false;case 1:return new F(function(){return _1II(_1IR[2],_1IS[2]);});break;default:return true;}};},_1IT=new T(function(){return B(_1IN(_1HJ));}),_1IU=function(_1IV,_1IW){return B(_AT(_1IV,_1IW))==2?false:true;},_1IX=function(_1IY){return function(_1IZ,_1J0){var _1J1=E(_1IZ),_1J2=E(_1J0);switch(B(_1D8(new T(function(){return B(_1IF(new T(function(){return B(_cp(new T(function(){return B(_1IL(_1IY));})));}),_1IY));}),_1J1[1],_1J2[1]))){case 0:return true;case 1:return new F(function(){return _1IU(_1J1[2],_1J2[2]);});break;default:return false;}};},_1J3=function(_1J4,_1J5,_1J6,_1J7){return !B(A(_1IX,[_1J5,_1J6,_1J7]))?E(_1J6):E(_1J7);},_1J8=function(_1J9,_1Ja,_1Jb,_1Jc){return !B(A(_1IX,[_1Ja,_1Jb,_1Jc]))?E(_1Jc):E(_1Jb);},_1Jd=function(_1Je,_1Jf){return B(_AT(_1Je,_1Jf))==0?true:false;},_1Jg=function(_1Jh){return function(_1Ji,_1Jj){var _1Jk=E(_1Ji),_1Jl=E(_1Jj);switch(B(_1D8(new T(function(){return B(_1IF(new T(function(){return B(_cp(new T(function(){return B(_1IL(_1Jh));})));}),_1Jh));}),_1Jk[1],_1Jl[1]))){case 0:return true;case 1:return new F(function(){return _1Jd(_1Jk[2],_1Jl[2]);});break;default:return false;}};},_1Jm=function(_1Jn,_1Jo){return B(_AT(_1Jn,_1Jo))==2?true:false;},_1Jp=function(_1Jq){return function(_1Jr,_1Js){var _1Jt=E(_1Jr),_1Ju=E(_1Js);switch(B(_1D8(new T(function(){return B(_1IF(new T(function(){return B(_cp(new T(function(){return B(_1IL(_1Jq));})));}),_1Jq));}),_1Jt[1],_1Ju[1]))){case 0:return false;case 1:return new F(function(){return _1Jm(_1Jt[2],_1Ju[2]);});break;default:return true;}};},_1Jv=function(_1Jw){return function(_1Jx,_1Jy){var _1Jz=E(_1Jx),_1JA=E(_1Jy);switch(B(_1D8(new T(function(){return B(_1IF(new T(function(){return B(_cp(new T(function(){return B(_1IL(_1Jw));})));}),_1Jw));}),_1Jz[1],_1JA[1]))){case 0:return 0;case 1:return new F(function(){return _AT(_1Jz[2],_1JA[2]);});break;default:return 2;}};},_1JB=function(_1JC,_1JD){return [0,_1JC,new T(function(){return B(_1Jv(_1JD));}),new T(function(){return B(_1Jg(_1JD));}),new T(function(){return B(_1IN(_1JD));}),new T(function(){return B(_1Jp(_1JD));}),new T(function(){return B(_1IX(_1JD));}),function(_cr,_cs){return new F(function(){return _1J3(_1JC,_1JD,_cr,_cs);});},function(_cr,_cs){return new F(function(){return _1J8(_1JC,_1JD,_cr,_cs);});}];},_1JE=function(_1JF,_1JG,_1JH,_1JI,_1JJ){return !B(_c1(new T(function(){return B(_cp(_1JF));}),_1JG,_1JI))?true:!B(_3x(_1JH,_1JJ))?true:false;},_1JK=function(_1JL,_1JM,_1JN){var _1JO=E(_1JM),_1JP=E(_1JN);return new F(function(){return _1JE(_1JL,_1JO[1],_1JO[2],_1JP[1],_1JP[2]);});},_1JQ=function(_1JR){return function(_1JS,_1JT){var _1JU=E(_1JS),_1JV=E(_1JT);return !B(_c1(new T(function(){return B(_cp(_1JR));}),_1JU[1],_1JV[1]))?false:B(_3x(_1JU[2],_1JV[2]));};},_1JW=function(_1JX){return [0,new T(function(){return B(_1JQ(_1JX));}),function(_cr,_cs){return new F(function(){return _1JK(_1JX,_cr,_cs);});}];},_1JY=new T(function(){return B(_1JW(_1HI));}),_1JZ=new T(function(){return B(_1JB(_1JY,_1HJ));}),_1K0=function(_1K1,_1K2,_1K3){var _1K4=E(_1K2),_1K5=E(_1K3);if(!_1K5[0]){var _1K6=_1K5[2],_1K7=_1K5[3],_1K8=_1K5[4];switch(B(A(_1D6,[_1K1,_1K4,_1K6]))){case 0:return new F(function(){return _rk(_1K6,B(_1K0(_1K1,_1K4,_1K7)),_1K8);});break;case 1:return [0,_1K5[1],E(_1K4),E(_1K7),E(_1K8)];default:return new F(function(){return _rW(_1K6,_1K7,B(_1K0(_1K1,_1K4,_1K8)));});}}else{return [0,1,E(_1K4),E(_rf),E(_rf)];}},_1K9=function(_1Ka,_1Kb){while(1){var _1Kc=E(_1Kb);if(!_1Kc[0]){return E(_1Ka);}else{var _1Kd=B(_1K0(_1JZ,_1Kc[1],_1Ka));_1Kb=_1Kc[2];_1Ka=_1Kd;continue;}}},_1Ke=function(_1Kf,_1Kg){var _1Kh=E(_1Kg);if(!_1Kh[0]){return [0,_rf,_9,_9];}else{var _1Ki=_1Kh[1],_1Kj=E(_1Kf);if(_1Kj==1){var _1Kk=E(_1Kh[2]);return _1Kk[0]==0?[0,new T(function(){return [0,1,E(E(_1Ki)),E(_rf),E(_rf)];}),_9,_9]:!B(A(_1IT,[_1Ki,_1Kk[1]]))?[0,new T(function(){return [0,1,E(E(_1Ki)),E(_rf),E(_rf)];}),_1Kk,_9]:[0,new T(function(){return [0,1,E(E(_1Ki)),E(_rf),E(_rf)];}),_9,_1Kk];}else{var _1Kl=B(_1Ke(_1Kj>>1,_1Kh)),_1Km=_1Kl[1],_1Kn=_1Kl[3],_1Ko=E(_1Kl[2]);if(!_1Ko[0]){return [0,_1Km,_9,_1Kn];}else{var _1Kp=_1Ko[1],_1Kq=E(_1Ko[2]);if(!_1Kq[0]){return [0,new T(function(){return B(_sC(_1Kp,_1Km));}),_9,_1Kn];}else{if(!B(A(_1IT,[_1Kp,_1Kq[1]]))){var _1Kr=B(_1Ke(_1Kj>>1,_1Kq));return [0,new T(function(){return B(_tg(_1Kp,_1Km,_1Kr[1]));}),_1Kr[2],_1Kr[3]];}else{return [0,_1Km,_9,_1Ko];}}}}}},_1Ks=function(_1Kt,_1Ku,_1Kv){while(1){var _1Kw=E(_1Kv);if(!_1Kw[0]){return E(_1Ku);}else{var _1Kx=_1Kw[1],_1Ky=E(_1Kw[2]);if(!_1Ky[0]){return new F(function(){return _sC(_1Kx,_1Ku);});}else{if(!B(A(_1IT,[_1Kx,_1Ky[1]]))){var _1Kz=B(_1Ke(_1Kt,_1Ky)),_1KA=_1Kz[1],_1KB=E(_1Kz[3]);if(!_1KB[0]){var _1KC=_1Kt<<1,_1KD=B(_tg(_1Kx,_1Ku,_1KA));_1Kv=_1Kz[2];_1Kt=_1KC;_1Ku=_1KD;continue;}else{return new F(function(){return _1K9(B(_tg(_1Kx,_1Ku,_1KA)),_1KB);});}}else{return new F(function(){return _1K9(_1Ku,_1Kw);});}}}}},_1KE=function(_1KF){var _1KG=E(_1KF);if(!_1KG[0]){return [1];}else{var _1KH=_1KG[1],_1KI=E(_1KG[2]);if(!_1KI[0]){return [0,1,E(E(_1KH)),E(_rf),E(_rf)];}else{if(!B(A(_1IT,[_1KH,_1KI[1]]))){return new F(function(){return _1Ks(1,[0,1,E(E(_1KH)),E(_rf),E(_rf)],_1KI);});}else{return new F(function(){return _1K9([0,1,E(E(_1KH)),E(_rf),E(_rf)],_1KI);});}}}},_1KJ=new T(function(){return B(_F(0,1,_9));}),_1KK=new T(function(){return B(unAppCStr("delta_",_1KJ));}),_1KL=[9,_,_,_1KK],_1KM=[0,_1KL],_1KN=[1,_1KM,_9],_1KO=new T(function(){return B(unAppCStr("phi_",_1KJ));}),_1KP=[3,_,_,_1KO],_1KQ=[2,_,_1KP],_1KR=[1,_1KQ,_9],_1KS=[1,_1KR],_1KT=[0,_1KN,_1KS],_1KU=new T(function(){return B(_F(0,2,_9));}),_1KV=new T(function(){return B(unAppCStr("phi_",_1KU));}),_1KW=[3,_,_,_1KV],_1KX=[2,_,_1KW],_1KY=[1,_1KX,_9],_1KZ=[1,_1KY],_1L0=new T(function(){return B(unAppCStr("delta_",_1KU));}),_1L1=[9,_,_,_1L0],_1L2=[0,_1L1],_1L3=[1,_1L2,_9],_1L4=[0,_1L3,_1KZ],_1L5=[1,_1L4,_9],_1L6=[1,_1KT,_1L5],_1L7=function(_1L8,_1L9){var _1La=E(_1L8);if(!_1La[0]){return [0];}else{var _1Lb=_1La[1],_1Lc=_1La[2],_1Ld=function(_1Le,_1Lf,_1Lg){var _1Lh=E(_1Lf);if(!_1Lh[0]){return [0,_1Lc,_1Lg];}else{var _1Li=_1Lh[1],_1Lj=new T(function(){var _1Lk=B(_1Ld(function(_1Ll){return new F(function(){return A(_1Le,[[1,_1Li,_1Ll]]);});},_1Lh[2],_1Lg));return [0,_1Lk[1],_1Lk[2]];}),_1Lm=new T(function(){return E(E(_1Lj)[1]);});return [0,[1,_1Li,_1Lm],[1,new T(function(){return B(A(_1Le,[[1,_1Lb,[1,_1Li,_1Lm]]]));}),new T(function(){return E(E(_1Lj)[2]);})]];}},_1Ln=function(_1Lo){var _1Lp=E(_1Lo);return _1Lp[0]==0?E(new T(function(){return B(_1L7(_1Lc,[1,_1Lb,_1L9]));})):E(B(_1Ld(_6P,_1Lp[1],new T(function(){return B(_1Ln(_1Lp[2]));})))[2]);};return new F(function(){return _1Ln([1,_1L9,new T(function(){return B(_1L7(_1L9,_9));})]);});}},_1Lq=new T(function(){return B(_1L7(_1L6,_9));}),_1Lr=[1,_1L6,_1Lq],_1Ls=[9,_,_1cH,_1KQ,_1KX],_1Lt=[1,_1Ls,_9],_1Lu=[1,_1Lt],_1Lv=[1,_1KM,_1L3],_1Lw=[0,_1Lv,_1Lu],_1Lx=function(_1Ly){return [0,_1Ly,_1Lw];},_1Lz=new T(function(){return B(_3d(_1Lx,_1Lr));}),_1LA=[0,_1Lz,_1CK],_1LB=[1,_1KT,_9],_1LC=[9,_,_1cj,_1KQ,_1KX],_1LD=[1,_1LC,_9],_1LE=[1,_1LD],_1LF=[0,_1KN,_1LE],_1LG=[0,_1LB,_1LF],_1LH=[9,_,_1cj,_1KX,_1KQ],_1LI=[1,_1LH,_9],_1LJ=[1,_1LI],_1LK=[0,_1KN,_1LJ],_1LL=[0,_1LB,_1LK],_1LM=[1,_1LL,_9],_1LN=[1,_1LG,_1LM],_1LO=[0,_1LN,_1CJ],_1LP=[0,_1LB,_1KT],_1LQ=[1,_1LP,_9],_1LR=[0,_1LQ,_1CW],_1LS=[1,_1LR,_9],_1LT=[1,_1KS,_1KN],_1LU=[0,_1LT,_1KZ],_1LV=[1,_1KS,_1L3],_1LW=[7,_,_1d8,_1KX],_1LX=[1,_1LW,_9],_1LY=[1,_1LX],_1LZ=[0,_1LV,_1LY],_1M0=[1,_1LZ,_9],_1M1=[1,_1LU,_1M0],_1M2=new T(function(){return B(_1L7(_1M1,_9));}),_1M3=[1,_1M1,_1M2],_1M4=[7,_,_1d8,_1KQ],_1M5=[1,_1M4,_9],_1M6=[1,_1M5],_1M7=[0,_1Lv,_1M6],_1M8=[0,_1Lv,_1KS],_1M9=function(_1Ma){return [0,_1Ma,_1M8];},_1Mb=[0,_1KN,_1KZ],_1Mc=[1,_1Mb,_9],_1Md=[0,_1L3,_1LY],_1Me=[1,_1Md,_1Mc],_1Mf=new T(function(){return B(_1L7(_1Me,_9));}),_1Mg=[1,_1Me,_1Mf],_1Mh=new T(function(){return B(_3d(_1M9,_1Mg));}),_1Mi=function(_1Mj){var _1Mk=E(_1Mj);return _1Mk[0]==0?E(_1Mh):[1,[0,_1Mk[1],_1M8],new T(function(){return B(_1Mi(_1Mk[2]));})];},_1Ml=[1,_1M6,_1L3],_1Mm=[0,_1Ml,_1LY],_1Mn=[1,_1Mm,_1Mc],_1Mo=new T(function(){return B(_1L7(_1Mn,_9));}),_1Mp=[1,_1Mn,_1Mo],_1Mq=new T(function(){return B(_1Mi(_1Mp));}),_1Mr=function(_1Ms){var _1Mt=E(_1Ms);return _1Mt[0]==0?E(_1Mq):[1,[0,_1Mt[1],_1M8],new T(function(){return B(_1Mr(_1Mt[2]));})];},_1Mu=[1,_1M6,_1KN],_1Mv=[0,_1Mu,_1KZ],_1Mw=[1,_1Mv,_9],_1Mx=[1,_1Md,_1Mw],_1My=new T(function(){return B(_1L7(_1Mx,_9));}),_1Mz=[1,_1Mx,_1My],_1MA=new T(function(){return B(_1Mr(_1Mz));}),_1MB=function(_1MC){var _1MD=E(_1MC);return _1MD[0]==0?E(_1MA):[1,[0,_1MD[1],_1M8],new T(function(){return B(_1MB(_1MD[2]));})];},_1ME=[1,_1Mm,_1Mw],_1MF=new T(function(){return B(_1L7(_1ME,_9));}),_1MG=[1,_1ME,_1MF],_1MH=new T(function(){return B(_1MB(_1MG));}),_1MI=function(_1MJ){var _1MK=E(_1MJ);return _1MK[0]==0?E(_1MH):[1,[0,_1MK[1],_1M7],new T(function(){return B(_1MI(_1MK[2]));})];},_1ML=[1,_1Md,_9],_1MM=[1,_1Mb,_1ML],_1MN=new T(function(){return B(_1L7(_1MM,_9));}),_1MO=[1,_1MM,_1MN],_1MP=new T(function(){return B(_1MI(_1MO));}),_1MQ=function(_1MR){var _1MS=E(_1MR);return _1MS[0]==0?E(_1MP):[1,[0,_1MS[1],_1M7],new T(function(){return B(_1MQ(_1MS[2]));})];},_1MT=[1,_1LU,_1ML],_1MU=new T(function(){return B(_1L7(_1MT,_9));}),_1MV=[1,_1MT,_1MU],_1MW=new T(function(){return B(_1MQ(_1MV));}),_1MX=function(_1MY){var _1MZ=E(_1MY);return _1MZ[0]==0?E(_1MW):[1,[0,_1MZ[1],_1M7],new T(function(){return B(_1MX(_1MZ[2]));})];},_1N0=[1,_1Mb,_1M0],_1N1=new T(function(){return B(_1L7(_1N0,_9));}),_1N2=[1,_1N0,_1N1],_1N3=new T(function(){return B(_1MX(_1N2));}),_1N4=function(_1N5){var _1N6=E(_1N5);return _1N6[0]==0?E(_1N3):[1,[0,_1N6[1],_1M7],new T(function(){return B(_1N4(_1N6[2]));})];},_1N7=new T(function(){return B(_1N4(_1M3));}),_1N8=[0,_1N7,_1CV],_1N9=[1,_1N8,_1LS],_1Na=[1,_1LO,_1N9],_1Nb=[0,83],_1Nc=[1,_1Nb,_9],_1Nd=[0,_1KN,_1Lu],_1Ne=[1,_1Nd,_9],_1Nf=[0,_1Ne,_1KT],_1Ng=[0,_1Ne,_1Mb],_1Nh=[1,_1Ng,_9],_1Ni=[1,_1Nf,_1Nh],_1Nj=[0,_1Ni,_1Nc],_1Nk=[1,_1Nj,_1Na],_1Nl=[1,_1LK,_1ML],_1Nm=new T(function(){return B(_1L7(_1Nl,_9));}),_1Nn=[1,_1Nl,_1Nm],_1No=[0,_1L3,_1M6],_1Np=[1,_1No,_9],_1Nq=[1,_1LK,_1Np],_1Nr=new T(function(){return B(_1L7(_1Nq,_9));}),_1Ns=[1,_1Nq,_1Nr],_1Nt=[0,_1Lv,_1KZ],_1Nu=function(_1Nv){return [0,_1Nv,_1Nt];},_1Nw=new T(function(){return B(_3d(_1Nu,_1Ns));}),_1Nx=function(_1Ny){var _1Nz=E(_1Ny);return _1Nz[0]==0?E(_1Nw):[1,[0,_1Nz[1],_1M8],new T(function(){return B(_1Nx(_1Nz[2]));})];},_1NA=new T(function(){return B(_1Nx(_1Nn));}),_1NB=[0,_1NA,_1CS],_1NC=[1,_1NB,_1Nk],_1ND=function(_1NE){return [0,_1NE,_1M7];},_1NF=[0,_1KN,_1LY],_1NG=[9,_,_1b7,_1KQ,_1KX],_1NH=[1,_1NG,_9],_1NI=[1,_1NH],_1NJ=[0,_1L3,_1NI],_1NK=[1,_1NJ,_9],_1NL=[1,_1NF,_1NK],_1NM=new T(function(){return B(_1L7(_1NL,_9));}),_1NN=[1,_1NL,_1NM],_1NO=new T(function(){return B(_3d(_1ND,_1NN));}),_1NP=[0,_1NO,_1CT],_1NQ=[1,_1NP,_1NC],_1NR=[1,_1KT,_1NK],_1NS=new T(function(){return B(_1L7(_1NR,_9));}),_1NT=[1,_1NR,_1NS],_1NU=new T(function(){return B(_3d(_1Nu,_1NT));}),_1NV=[0,_1NU,_1CU],_1NW=[1,_1NV,_1NQ],_1NX=[0,_1KN,_1NI],_1NY=[1,_1LU,_9],_1NZ=[0,_1NY,_1NX],_1O0=[0,_1Mc,_1NX],_1O1=[1,_1O0,_9],_1O2=[1,_1NZ,_1O1],_1O3=[0,_1O2,_1CX],_1O4=[1,_1O3,_1NW],_1O5=[1,_1LA,_1O4],_1O6=new T(function(){return B(_1KE(_1O5));}),_1O7=[0,_1D3,_1O6],_1O8=function(_){return new F(function(){return _1Cm(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1O7,_);});},_1O9=function(_){return new F(function(){return _1O8(_);});};
var hasteMain = function() {B(A(_1O9, [0]));};window.onload = hasteMain;