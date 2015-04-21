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

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr("wheel"));}),_1r=new T(function(){return B(unCStr("mouseout"));}),_1s=new T(function(){return B(unCStr("mouseover"));}),_1t=new T(function(){return B(unCStr("mousemove"));}),_1u=new T(function(){return B(unCStr("blur"));}),_1v=new T(function(){return B(unCStr("focus"));}),_1w=new T(function(){return B(unCStr("change"));}),_1x=new T(function(){return B(unCStr("unload"));}),_1y=new T(function(){return B(unCStr("load"));}),_1z=new T(function(){return B(unCStr("submit"));}),_1A=new T(function(){return B(unCStr("keydown"));}),_1B=new T(function(){return B(unCStr("keyup"));}),_1C=new T(function(){return B(unCStr("keypress"));}),_1D=new T(function(){return B(unCStr("mouseup"));}),_1E=new T(function(){return B(unCStr("mousedown"));}),_1F=new T(function(){return B(unCStr("dblclick"));}),_1G=new T(function(){return B(unCStr("click"));}),_1H=function(_1I){switch(E(_1I)[0]){case 0:return E(_1y);case 1:return E(_1x);case 2:return E(_1w);case 3:return E(_1v);case 4:return E(_1u);case 5:return E(_1t);case 6:return E(_1s);case 7:return E(_1r);case 8:return E(_1G);case 9:return E(_1F);case 10:return E(_1E);case 11:return E(_1D);case 12:return E(_1C);case 13:return E(_1B);case 14:return E(_1A);case 15:return E(_1z);default:return E(_1q);}},_1J=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_1K=new T(function(){return B(unCStr("main"));}),_1L=new T(function(){return B(unCStr("EventData"));}),_1M=new T(function(){var _1N=hs_wordToWord64(3703396926),_1O=_1N,_1P=hs_wordToWord64(1660403598),_1Q=_1P;return [0,_1O,_1Q,[0,_1O,_1Q,_1K,_1J,_1L],_9];}),_1R=[0,0],_1S=false,_1T=2,_1U=[1],_1V=new T(function(){return B(unCStr("Dynamic"));}),_1W=new T(function(){return B(unCStr("Data.Dynamic"));}),_1X=new T(function(){return B(unCStr("base"));}),_1Y=new T(function(){var _1Z=hs_wordToWord64(628307645),_20=_1Z,_21=hs_wordToWord64(949574464),_22=_21;return [0,_20,_22,[0,_20,_22,_1X,_1W,_1V],_9];}),_23=[0],_24=new T(function(){return B(unCStr("OnLoad"));}),_25=[0,_24,_23],_26=[0,_1M,_25],_27=[0,_1Y,_26],_28=[0],_29=function(_){return _28;},_2a=function(_2b,_){return _28;},_2c=[0,_29,_2a],_2d=[0,_9,_1R,_1T,_2c,_1S,_27,_1U],_2e=function(_){var _=0,_2f=newMVar(),_2g=_2f,_=putMVar(_2g,_2d);return [0,_2g];},_2h=function(_2i){var _2j=B(A(_2i,[_])),_2k=_2j;return E(_2k);},_2l=new T(function(){return B(_2h(_2e));}),_2m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2n=new T(function(){return B(unCStr("base"));}),_2o=new T(function(){return B(unCStr("PatternMatchFail"));}),_2p=new T(function(){var _2q=hs_wordToWord64(18445595),_2r=_2q,_2s=hs_wordToWord64(52003073),_2t=_2s;return [0,_2r,_2t,[0,_2r,_2t,_2n,_2m,_2o],_9];}),_2u=function(_2v){return E(_2p);},_2w=function(_2x){return E(E(_2x)[1]);},_2y=function(_2z,_2A,_2B){var _2C=B(A(_2z,[_])),_2D=B(A(_2A,[_])),_2E=hs_eqWord64(_2C[1],_2D[1]),_2F=_2E;if(!E(_2F)){return [0];}else{var _2G=hs_eqWord64(_2C[2],_2D[2]),_2H=_2G;return E(_2H)==0?[0]:[1,_2B];}},_2I=function(_2J){var _2K=E(_2J);return new F(function(){return _2y(B(_2w(_2K[1])),_2u,_2K[2]);});},_2L=function(_2M){return E(E(_2M)[1]);},_2N=function(_2O,_2P){return new F(function(){return _e(E(_2O)[1],_2P);});},_2Q=[0,44],_2R=[0,93],_2S=[0,91],_2T=function(_2U,_2V,_2W){var _2X=E(_2V);return _2X[0]==0?B(unAppCStr("[]",_2W)):[1,_2S,new T(function(){return B(A(_2U,[_2X[1],new T(function(){var _2Y=function(_2Z){var _30=E(_2Z);return _30[0]==0?E([1,_2R,_2W]):[1,_2Q,new T(function(){return B(A(_2U,[_30[1],new T(function(){return B(_2Y(_30[2]));})]));})];};return B(_2Y(_2X[2]));})]));})];},_31=function(_32,_33){return new F(function(){return _2T(_2N,_32,_33);});},_34=function(_35,_36,_37){return new F(function(){return _e(E(_36)[1],_37);});},_38=[0,_34,_2L,_31],_39=new T(function(){return [0,_2u,_38,_3a,_2I];}),_3a=function(_3b){return [0,_39,_3b];},_3c=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3d=function(_3e,_3f){return new F(function(){return die(new T(function(){return B(A(_3f,[_3e]));}));});},_3g=function(_3h,_3i){var _3j=E(_3i);if(!_3j[0]){return [0,_9,_9];}else{var _3k=_3j[1];if(!B(A(_3h,[_3k]))){return [0,_9,_3j];}else{var _3l=new T(function(){var _3m=B(_3g(_3h,_3j[2]));return [0,_3m[1],_3m[2]];});return [0,[1,_3k,new T(function(){return E(E(_3l)[1]);})],new T(function(){return E(E(_3l)[2]);})];}}},_3n=[0,32],_3o=[0,10],_3p=[1,_3o,_9],_3q=function(_3r){return E(E(_3r)[1])==124?false:true;},_3s=function(_3t,_3u){var _3v=B(_3g(_3q,B(unCStr(_3t)))),_3w=_3v[1],_3x=function(_3y,_3z){return new F(function(){return _e(_3y,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_3u,new T(function(){return B(_e(_3z,_3p));},1)));})));},1));});},_3A=E(_3v[2]);if(!_3A[0]){return new F(function(){return _3x(_3w,_9);});}else{return E(E(_3A[1])[1])==124?B(_3x(_3w,[1,_3n,_3A[2]])):B(_3x(_3w,_9));}},_3B=function(_3C){return new F(function(){return _3d([0,new T(function(){return B(_3s(_3C,_3c));})],_3a);});},_3D=new T(function(){return B(_3B("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_3E=[0,_1y,_23],_3F=[0,_1M,_3E],_3G=[0,_1x,_23],_3H=[0,_1M,_3G],_3I=[0,_1w,_23],_3J=[0,_1M,_3I],_3K=[0,_1v,_23],_3L=[0,_1M,_3K],_3M=[0,_1u,_23],_3N=[0,_1M,_3M],_3O=[3],_3P=[0,_1r,_3O],_3Q=[0,_1M,_3P],_3R=function(_3S,_3T){switch(E(_3S)[0]){case 0:return function(_){var _3U=E(_2l)[1],_3V=takeMVar(_3U),_3W=_3V,_=putMVar(_3U,new T(function(){var _3X=E(_3W);return [0,_3X[1],_3X[2],_3X[3],_3X[4],_3X[5],_3F,_3X[7]];}));return new F(function(){return A(_3T,[_]);});};case 1:return function(_){var _3Y=E(_2l)[1],_3Z=takeMVar(_3Y),_40=_3Z,_=putMVar(_3Y,new T(function(){var _41=E(_40);return [0,_41[1],_41[2],_41[3],_41[4],_41[5],_3H,_41[7]];}));return new F(function(){return A(_3T,[_]);});};case 2:return function(_){var _42=E(_2l)[1],_43=takeMVar(_42),_44=_43,_=putMVar(_42,new T(function(){var _45=E(_44);return [0,_45[1],_45[2],_45[3],_45[4],_45[5],_3J,_45[7]];}));return new F(function(){return A(_3T,[_]);});};case 3:return function(_){var _46=E(_2l)[1],_47=takeMVar(_46),_48=_47,_=putMVar(_46,new T(function(){var _49=E(_48);return [0,_49[1],_49[2],_49[3],_49[4],_49[5],_3L,_49[7]];}));return new F(function(){return A(_3T,[_]);});};case 4:return function(_){var _4a=E(_2l)[1],_4b=takeMVar(_4a),_4c=_4b,_=putMVar(_4a,new T(function(){var _4d=E(_4c);return [0,_4d[1],_4d[2],_4d[3],_4d[4],_4d[5],_3N,_4d[7]];}));return new F(function(){return A(_3T,[_]);});};case 5:return function(_4e){return function(_){var _4f=E(_2l)[1],_4g=takeMVar(_4f),_4h=_4g,_=putMVar(_4f,new T(function(){var _4i=E(_4h);return [0,_4i[1],_4i[2],_4i[3],_4i[4],_4i[5],[0,_1M,[0,_1t,[2,E(_4e)]]],_4i[7]];}));return new F(function(){return A(_3T,[_]);});};};case 6:return function(_4j){return function(_){var _4k=E(_2l)[1],_4l=takeMVar(_4k),_4m=_4l,_=putMVar(_4k,new T(function(){var _4n=E(_4m);return [0,_4n[1],_4n[2],_4n[3],_4n[4],_4n[5],[0,_1M,[0,_1s,[2,E(_4j)]]],_4n[7]];}));return new F(function(){return A(_3T,[_]);});};};case 7:return function(_){var _4o=E(_2l)[1],_4p=takeMVar(_4o),_4q=_4p,_=putMVar(_4o,new T(function(){var _4r=E(_4q);return [0,_4r[1],_4r[2],_4r[3],_4r[4],_4r[5],_3Q,_4r[7]];}));return new F(function(){return A(_3T,[_]);});};case 8:return function(_4s,_4t){return function(_){var _4u=E(_2l)[1],_4v=takeMVar(_4u),_4w=_4v,_=putMVar(_4u,new T(function(){var _4x=E(_4w);return [0,_4x[1],_4x[2],_4x[3],_4x[4],_4x[5],[0,_1M,[0,_1G,[1,_4s,E(_4t)]]],_4x[7]];}));return new F(function(){return A(_3T,[_]);});};};case 9:return function(_4y,_4z){return function(_){var _4A=E(_2l)[1],_4B=takeMVar(_4A),_4C=_4B,_=putMVar(_4A,new T(function(){var _4D=E(_4C);return [0,_4D[1],_4D[2],_4D[3],_4D[4],_4D[5],[0,_1M,[0,_1F,[1,_4y,E(_4z)]]],_4D[7]];}));return new F(function(){return A(_3T,[_]);});};};case 10:return function(_4E,_4F){return function(_){var _4G=E(_2l)[1],_4H=takeMVar(_4G),_4I=_4H,_=putMVar(_4G,new T(function(){var _4J=E(_4I);return [0,_4J[1],_4J[2],_4J[3],_4J[4],_4J[5],[0,_1M,[0,_1E,[1,_4E,E(_4F)]]],_4J[7]];}));return new F(function(){return A(_3T,[_]);});};};case 11:return function(_4K,_4L){return function(_){var _4M=E(_2l)[1],_4N=takeMVar(_4M),_4O=_4N,_=putMVar(_4M,new T(function(){var _4P=E(_4O);return [0,_4P[1],_4P[2],_4P[3],_4P[4],_4P[5],[0,_1M,[0,_1D,[1,_4K,E(_4L)]]],_4P[7]];}));return new F(function(){return A(_3T,[_]);});};};case 12:return function(_4Q,_){var _4R=E(_2l)[1],_4S=takeMVar(_4R),_4T=_4S,_=putMVar(_4R,new T(function(){var _4U=E(_4T);return [0,_4U[1],_4U[2],_4U[3],_4U[4],_4U[5],[0,_1M,[0,_1C,[4,_4Q]]],_4U[7]];}));return new F(function(){return A(_3T,[_]);});};case 13:return function(_4V,_){var _4W=E(_2l)[1],_4X=takeMVar(_4W),_4Y=_4X,_=putMVar(_4W,new T(function(){var _4Z=E(_4Y);return [0,_4Z[1],_4Z[2],_4Z[3],_4Z[4],_4Z[5],[0,_1M,[0,_1B,[4,_4V]]],_4Z[7]];}));return new F(function(){return A(_3T,[_]);});};case 14:return function(_50,_){var _51=E(_2l)[1],_52=takeMVar(_51),_53=_52,_=putMVar(_51,new T(function(){var _54=E(_53);return [0,_54[1],_54[2],_54[3],_54[4],_54[5],[0,_1M,[0,_1A,[4,_50]]],_54[7]];}));return new F(function(){return A(_3T,[_]);});};default:return E(_3D);}},_55=[0,_1H,_3R],_56=function(_57,_58,_){var _59=jsCreateTextNode(toJSStr(E(_57))),_5a=_59,_5b=jsAppendChild(_5a,E(_58)[1]);return [0,_5a];},_5c=0,_5d=function(_5e,_5f,_5g,_5h){return new F(function(){return A(_5e,[function(_){var _5i=jsSetAttr(E(_5f)[1],toJSStr(E(_5g)),toJSStr(E(_5h)));return _5c;}]);});},_5j=[0,112],_5k=function(_5l){var _5m=new T(function(){return E(E(_5l)[2]);});return function(_5n,_){return [0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_5m)[1],_9)),new T(function(){return E(E(_5l)[1]);},1)));})],new T(function(){var _5o=E(_5l);return [0,_5o[1],new T(function(){return [0,E(_5m)[1]+1|0];}),_5o[3],_5o[4],_5o[5],_5o[6],_5o[7]];})];};},_5p=new T(function(){return B(unCStr("id"));}),_5q=function(_5r){return E(_5r);},_5s=new T(function(){return B(unCStr("noid"));}),_5t=function(_5u,_){return _5u;},_5v=function(_5w,_5x,_){var _5y=jsFind(toJSStr(E(_5x))),_5z=_5y,_5A=E(_5z);if(!_5A[0]){var _5B=E(_2l)[1],_5C=takeMVar(_5B),_5D=_5C,_5E=B(A(_5w,[_5D,_])),_5F=_5E,_5G=E(_5F),_=putMVar(_5B,_5G[2]);return E(_5G[1])[2];}else{var _5H=E(_5A[1]),_5I=jsClearChildren(_5H[1]),_5J=E(_2l)[1],_5K=takeMVar(_5J),_5L=_5K,_5M=B(A(_5w,[_5L,_])),_5N=_5M,_5O=E(_5N),_5P=E(_5O[1]),_=putMVar(_5J,_5O[2]),_5Q=B(A(_5P[1],[_5H,_])),_5R=_5Q;return _5P[2];}},_5S=new T(function(){return B(unCStr("span"));}),_5T=function(_5U,_5V,_5W,_){var _5X=jsCreateElem(toJSStr(E(_5S))),_5Y=_5X,_5Z=jsAppendChild(_5Y,E(_5W)[1]),_60=[0,_5Y],_61=B(A(_5U,[_5V,_60,_])),_62=_61;return _60;},_63=function(_64){return E(_64);},_65=function(_66,_67,_68,_){var _69=B(A(_5k,[_68,_68,_])),_6a=_69,_6b=E(_6a),_6c=_6b[1],_6d=E(_6b[2]),_6e=_6d[2],_6f=E(_6d[4]),_6g=B(A(_66,[[0,_6d[1],_6e,_6d[3],[0,function(_){return new F(function(){return _5v(function(_6h,_){var _6i=B(A(_66,[new T(function(){var _6j=E(_6h);return [0,_6j[1],_6e,_6j[3],_6j[4],_6j[5],_6j[6],_6j[7]];}),_])),_6k=_6i;return [0,[0,_5t,E(E(_6k)[1])[2]],_6h];},_5s,_);});},function(_6l,_){var _6m=B(_5v(new T(function(){return B(A(_67,[_6l]));},1),_6c,_)),_6n=_6m,_6o=E(_6n);return _6o[0]==0?_28:B(A(_6f[2],[_6o[1],_]));}],_6d[5],_6d[6],_6d[7]],_])),_6p=_6g,_6q=E(_6p),_6r=_6q[2],_6s=E(_6q[1]),_6t=_6s[1],_6u=E(_6s[2]);if(!_6u[0]){return [0,[0,function(_6v,_){var _6w=B(A(_6t,[_6v,_])),_6x=_6w;if(!E(E(_68)[5])){var _6y=B(_5T(_63,_5t,_6v,_)),_6z=_6y,_6A=B(A(_5d,[_5q,_6z,_5p,_6c,_])),_6B=_6A;return _6v;}else{return _6v;}},_28],new T(function(){var _6C=E(_6r);return [0,_6C[1],_6C[2],_6C[3],_6f,_6C[5],_6C[6],_6C[7]];})];}else{var _6D=B(A(_67,[_6u[1],new T(function(){var _6E=E(_6r);return [0,_6E[1],_6E[2],_6E[3],_6f,_6E[5],_6E[6],_6E[7]];}),_])),_6F=_6D,_6G=E(_6F),_6H=E(_6G[1]),_6I=_6H[1];return [0,[0,function(_6J,_){var _6K=B(A(_6t,[_6J,_])),_6L=_6K;if(!E(E(_68)[5])){var _6M=B(_5T(_63,_6I,_6J,_)),_6N=_6M,_6O=B(A(_5d,[_5q,_6N,_5p,_6c,_])),_6P=_6O;return _6J;}else{var _6Q=B(A(_6I,[_6J,_])),_6R=_6Q;return _6J;}},_6H[2]],_6G[2]];}},_6S=function(_6T,_6U){switch(E(_6T)[0]){case 0:switch(E(_6U)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_6U)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_6U)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_6U)[0]==3?1:2;}},_6V=new T(function(){return B(unCStr("end of input"));}),_6W=new T(function(){return B(unCStr("unexpected"));}),_6X=new T(function(){return B(unCStr("expecting"));}),_6Y=new T(function(){return B(unCStr("unknown parse error"));}),_6Z=new T(function(){return B(unCStr("or"));}),_70=[0,58],_71=[0,34],_72=[0,41],_73=[1,_72,_9],_74=function(_75,_76,_77){var _78=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_76,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_77,_9)),_73));})));},1)));})));}),_79=E(_75);return _79[0]==0?E(_78):[1,_71,new T(function(){return B(_e(_79,new T(function(){return B(unAppCStr("\" ",_78));},1)));})];},_7a=function(_7b,_7c){while(1){var _7d=E(_7b);if(!_7d[0]){return E(_7c)[0]==0?true:false;}else{var _7e=E(_7c);if(!_7e[0]){return false;}else{if(E(_7d[1])[1]!=E(_7e[1])[1]){return false;}else{_7b=_7d[2];_7c=_7e[2];continue;}}}}},_7f=function(_7g,_7h){return !B(_7a(_7g,_7h))?true:false;},_7i=[0,_7a,_7f],_7j=function(_7k,_7l,_7m){var _7n=E(_7m);if(!_7n[0]){return E(_7l);}else{return new F(function(){return _e(_7l,new T(function(){return B(_e(_7k,new T(function(){return B(_7j(_7k,_7n[1],_7n[2]));},1)));},1));});}},_7o=function(_7p){return E(_7p)[0]==0?false:true;},_7q=new T(function(){return B(unCStr(", "));}),_7r=function(_7s){var _7t=E(_7s);if(!_7t[0]){return [0];}else{return new F(function(){return _e(_7t[1],new T(function(){return B(_7r(_7t[2]));},1));});}},_7u=function(_7v,_7w){while(1){var _7x=(function(_7y,_7z){var _7A=E(_7z);if(!_7A[0]){return [0];}else{var _7B=_7A[1],_7C=_7A[2];if(!B(A(_7y,[_7B]))){var _7D=_7y;_7w=_7C;_7v=_7D;return null;}else{return [1,_7B,new T(function(){return B(_7u(_7y,_7C));})];}}})(_7v,_7w);if(_7x!=null){return _7x;}}},_7E=function(_7F,_7G){var _7H=E(_7G);return _7H[0]==0?[0]:[1,_7F,new T(function(){return B(_7E(_7H[1],_7H[2]));})];},_7I=function(_7J,_7K){while(1){var _7L=E(_7K);if(!_7L[0]){return E(_7J);}else{_7J=_7L[1];_7K=_7L[2];continue;}}},_7M=function(_7N){switch(E(_7N)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_7O=function(_7P){return E(_7P)[0]==1?true:false;},_7Q=function(_7R){return E(_7R)[0]==2?true:false;},_7S=[0,10],_7T=[1,_7S,_9],_7U=function(_7V){return new F(function(){return _e(_7T,_7V);});},_7W=[0,32],_7X=function(_7Y,_7Z){var _80=E(_7Z);return _80[0]==0?[0]:[1,new T(function(){return B(A(_7Y,[_80[1]]));}),new T(function(){return B(_7X(_7Y,_80[2]));})];},_81=function(_82){var _83=E(_82);switch(_83[0]){case 0:return E(_83[1]);case 1:return E(_83[1]);case 2:return E(_83[1]);default:return E(_83[1]);}},_84=function(_85){return E(E(_85)[1]);},_86=function(_87,_88,_89){while(1){var _8a=E(_89);if(!_8a[0]){return false;}else{if(!B(A(_84,[_87,_88,_8a[1]]))){_89=_8a[2];continue;}else{return true;}}}},_8b=function(_8c,_8d){var _8e=function(_8f,_8g){while(1){var _8h=(function(_8i,_8j){var _8k=E(_8i);if(!_8k[0]){return [0];}else{var _8l=_8k[1],_8m=_8k[2];if(!B(_86(_8c,_8l,_8j))){return [1,_8l,new T(function(){return B(_8e(_8m,[1,_8l,_8j]));})];}else{_8f=_8m;var _8n=_8j;_8g=_8n;return null;}}})(_8f,_8g);if(_8h!=null){return _8h;}}};return new F(function(){return _8e(_8d,_9);});},_8o=function(_8p,_8q,_8r,_8s,_8t,_8u){var _8v=E(_8u);if(!_8v[0]){return E(_8q);}else{var _8w=new T(function(){var _8x=B(_3g(_7M,_8v));return [0,_8x[1],_8x[2]];}),_8y=new T(function(){var _8z=B(_3g(_7O,E(_8w)[2]));return [0,_8z[1],_8z[2]];}),_8A=new T(function(){return E(E(_8y)[1]);}),_8B=function(_8C,_8D){var _8E=E(_8D);if(!_8E[0]){return E(_8C);}else{var _8F=new T(function(){return B(_e(_8p,[1,_7W,new T(function(){return B(_7I(_8C,_8E));})]));}),_8G=B(_8b(_7i,B(_7u(_7o,B(_7E(_8C,_8E))))));if(!_8G[0]){return new F(function(){return _e(_9,[1,_7W,_8F]);});}else{var _8H=_8G[1],_8I=E(_8G[2]);if(!_8I[0]){return new F(function(){return _e(_8H,[1,_7W,_8F]);});}else{return new F(function(){return _e(B(_e(_8H,new T(function(){return B(_e(_7q,new T(function(){return B(_7j(_7q,_8I[1],_8I[2]));},1)));},1))),[1,_7W,_8F]);});}}}},_8J=function(_8K,_8L){var _8M=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_8L))))));if(!_8M[0]){return [0];}else{var _8N=_8M[1],_8O=_8M[2],_8P=E(_8K);return _8P[0]==0?B(_8B(_8N,_8O)):B(_e(_8P,[1,_7W,new T(function(){return B(_8B(_8N,_8O));})]));}},_8Q=new T(function(){var _8R=B(_3g(_7Q,E(_8y)[2]));return [0,_8R[1],_8R[2]];});return new F(function(){return _7r(B(_7X(_7U,B(_8b(_7i,B(_7u(_7o,[1,new T(function(){if(!E(_8A)[0]){var _8S=E(E(_8w)[1]);if(!_8S[0]){var _8T=[0];}else{var _8U=E(_8S[1]);switch(_8U[0]){case 0:var _8V=E(_8U[1]),_8W=_8V[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8V]));break;case 1:var _8X=E(_8U[1]),_8W=_8X[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8X]));break;case 2:var _8Y=E(_8U[1]),_8W=_8Y[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Y]));break;default:var _8Z=E(_8U[1]),_8W=_8Z[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Z]));}var _8T=_8W;}var _90=_8T,_91=_90;}else{var _91=[0];}return _91;}),[1,new T(function(){return B(_8J(_8s,_8A));}),[1,new T(function(){return B(_8J(_8r,E(_8Q)[1]));}),[1,new T(function(){return B((function(_92){var _93=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_92))))));return _93[0]==0?[0]:B(_8B(_93[1],_93[2]));})(E(_8Q)[2]));}),_9]]]])))))));});}},_94=[1,_9,_9],_95=function(_96,_97){var _98=function(_99,_9a){var _9b=E(_99);if(!_9b[0]){return E(_9a);}else{var _9c=_9b[1],_9d=E(_9a);if(!_9d[0]){return E(_9b);}else{var _9e=_9d[1];return B(A(_96,[_9c,_9e]))==2?[1,_9e,new T(function(){return B(_98(_9b,_9d[2]));})]:[1,_9c,new T(function(){return B(_98(_9b[2],_9d));})];}}},_9f=function(_9g){var _9h=E(_9g);if(!_9h[0]){return [0];}else{var _9i=E(_9h[2]);return _9i[0]==0?E(_9h):[1,new T(function(){return B(_98(_9h[1],_9i[1]));}),new T(function(){return B(_9f(_9i[2]));})];}},_9j=function(_9k){while(1){var _9l=E(_9k);if(!_9l[0]){return E(new T(function(){return B(_9j(B(_9f(_9))));}));}else{if(!E(_9l[2])[0]){return E(_9l[1]);}else{_9k=B(_9f(_9l));continue;}}}},_9m=new T(function(){return B(_9n(_9));}),_9n=function(_9o){var _9p=E(_9o);if(!_9p[0]){return E(_94);}else{var _9q=_9p[1],_9r=E(_9p[2]);if(!_9r[0]){return [1,_9p,_9];}else{var _9s=_9r[1],_9t=_9r[2];if(B(A(_96,[_9q,_9s]))==2){return new F(function(){return (function(_9u,_9v,_9w){while(1){var _9x=(function(_9y,_9z,_9A){var _9B=E(_9A);if(!_9B[0]){return [1,[1,_9y,_9z],_9m];}else{var _9C=_9B[1];if(B(A(_96,[_9y,_9C]))==2){_9u=_9C;var _9D=[1,_9y,_9z];_9w=_9B[2];_9v=_9D;return null;}else{return [1,[1,_9y,_9z],new T(function(){return B(_9n(_9B));})];}}})(_9u,_9v,_9w);if(_9x!=null){return _9x;}}})(_9s,[1,_9q,_9],_9t);});}else{return new F(function(){return (function(_9E,_9F,_9G){while(1){var _9H=(function(_9I,_9J,_9K){var _9L=E(_9K);if(!_9L[0]){return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),_9m];}else{var _9M=_9L[1],_9N=_9L[2];switch(B(A(_96,[_9I,_9M]))){case 0:_9E=_9M;_9F=function(_9O){return new F(function(){return A(_9J,[[1,_9I,_9O]]);});};_9G=_9N;return null;case 1:_9E=_9M;_9F=function(_9P){return new F(function(){return A(_9J,[[1,_9I,_9P]]);});};_9G=_9N;return null;default:return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),new T(function(){return B(_9n(_9L));})];}}})(_9E,_9F,_9G);if(_9H!=null){return _9H;}}})(_9s,function(_9Q){return [1,_9q,_9Q];},_9t);});}}}};return new F(function(){return _9j(B(_9n(_97)));});},_9R=function(_9S,_9T,_9U,_9V){return new F(function(){return _e(B(_74(_9S,_9T,_9U)),[1,_70,new T(function(){return B(_8o(_6Z,_6Y,_6X,_6W,_6V,B(_95(_6S,_9V))));})]);});},_9W=function(_9X){var _9Y=E(_9X),_9Z=E(_9Y[1]);return new F(function(){return _9R(_9Z[1],_9Z[2],_9Z[3],_9Y[2]);});},_a0=new T(function(){return B(unCStr(" . "));}),_a1=function(_a2){var _a3=E(_a2);switch(_a3[0]){case 0:return E(_a3[3]);case 1:return E(_a3[3]);case 2:return E(_a3[3]);case 3:return E(_a3[3]);case 4:return E(_a3[3]);case 5:return E(_a3[3]);case 6:return E(_a3[3]);case 7:return E(_a3[3]);case 8:return E(_a3[3]);default:return E(_a3[3]);}},_a4=[0,41],_a5=[1,_a4,_9],_a6=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_a7=[0,44],_a8=[0,40],_a9=function(_aa,_ab,_ac){var _ad=E(_ac);switch(_ad[0]){case 0:return E(_a6);case 1:return new F(function(){return A(_aa,[_ad[2],_9]);});break;case 2:return new F(function(){return _a1(_ad[2]);});break;case 3:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),[1,new T(function(){return B(_a9(_aa,_ab,_ad[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[4])),_a5));})]));})]);});}},_ae=[0],_af=function(_ag,_ah,_ai,_aj,_ak,_al,_am,_an){var _ao=E(_an);switch(_ao[0]){case 0:return [0];case 1:return new F(function(){return A(_aj,[_ao[2],_9]);});break;case 2:return new F(function(){return _a1(_ao[2]);});break;case 3:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),[1,new T(function(){return B(_a9(_aj,_ak,_ao[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[4])),_a5));})]));})]);});break;case 7:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_a1(_ao[2])),new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));},1));});break;case 9:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4]));}),_9]]]);});break;case 10:return [1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3])),new T(function(){return B(_e(B(_a1(_ao[2])),new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4])),_a5));},1)));},1)));})];case 11:var _ap=_ao[2],_aq=_ao[3];return new F(function(){return A(_ai,[_ap,[1,new T(function(){return B(A(_al,[new T(function(){return B(A(_aq,[_ae]));}),_ap]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_aq,[_ae]))));}),_9]]]);});break;default:var _ar=_ao[2],_as=_ao[3];return new F(function(){return _e(B(_a1(_ar)),new T(function(){return B(_e(B(A(_am,[new T(function(){return B(A(_as,[_ae]));}),_ar])),[1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_as,[_ae])))),_a5));})]));},1));});}},_at=function(_au){var _av=E(_au);if(!_av[0]){return [0];}else{return new F(function(){return _e(_av[1],new T(function(){return B(_at(_av[2]));},1));});}},_aw=function(_ax,_ay){var _az=E(_ay);return _az[0]==0?[0]:[1,_ax,[1,_az[1],new T(function(){return B(_aw(_ax,_az[2]));})]];},_aA=function(_aB,_aC,_aD,_aE,_aF,_aG,_aH,_aI){var _aJ=E(_aI);if(!_aJ[0]){return new F(function(){return _a1(_aJ[1]);});}else{var _aK=B(_7X(function(_aL){return new F(function(){return _af(_aB,_aC,_aD,_aF,_aE,_aG,_aH,_aL);});},_aJ[1]));return _aK[0]==0?[0]:B(_at([1,_aK[1],new T(function(){return B(_aw(_a0,_aK[2]));})]));}},_aM=function(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aU,_aV){return new F(function(){return _2T(function(_aW,_aX){return new F(function(){return _e(B(_aA(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aW)),_aX);});},_aU,_aV);});},_aY=function(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,_b8){return new F(function(){return _e(B(_aA(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b7)),_b8);});},_b9=function(_ba,_bb,_bc,_bd,_be,_bf,_bg){return [0,function(_bh,_bi,_bj){return new F(function(){return _aY(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bh,_bi,_bj);});},function(_bj){return new F(function(){return _aA(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bj);});},function(_bi,_bj){return new F(function(){return _aM(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bi,_bj);});}];},_bk=new T(function(){return B(unCStr(" . "));}),_bl=new T(function(){return B(unCStr(" \u2234 "));}),_bm=function(_bn){return E(E(_bn)[2]);},_bo=function(_bp,_bq,_br){var _bs=B(_7X(new T(function(){return B(_bm(_bp));}),_bq));if(!_bs[0]){return new F(function(){return _e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1));});}else{return new F(function(){return _e(B(_at([1,_bs[1],new T(function(){return B(_aw(_bk,_bs[2]));})])),new T(function(){return B(_e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1)));},1));});}},_bt=2,_bu=function(_bv,_){return [0,[0,_5t,[1,_bv]],_bv];},_bw=function(_bx){return function(_by,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bz=E(_bx);return B(_e(B(_F(0,E(_bz[2])[1],_9)),_bz[1]));})]]],_by];};},_bA=function(_bB,_){return new F(function(){return _65(_bu,_bw,_bB,_);});},_bC=function(_bD){return function(_bE,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bF=E(_bD);return B(_e(B(_F(0,E(_bF[2])[1],_9)),_bF[1]));})]]],_bE];};},_bG=function(_bB,_){return new F(function(){return _65(_bu,_bC,_bB,_);});},_bH=function(_bI){return function(_bJ,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bK=E(_bI);return B(_e(B(_F(0,E(_bK[2])[1],_9)),_bK[1]));})]]],_bJ];};},_bL=function(_bB,_){return new F(function(){return _65(_bu,_bH,_bB,_);});},_bM=new T(function(){return B(unCStr("rslt"));}),_bN=new T(function(){return B(unCStr("root"));}),_bO=new T(function(){return B(unCStr("analysis"));}),_bP=new T(function(){return B(unCStr("class"));}),_bQ=new T(function(){return B(unCStr("invalid"));}),_bR=function(_bB,_){return new F(function(){return _5T(_56,_bQ,_bB,_);});},_bS=[1,_5c],_bT=[0,_bR,_bS],_bU=function(_bV,_){return [0,_bT,_bV];},_bW=new T(function(){return B(unCStr("div"));}),_bX=function(_bY,_bZ,_c0,_){var _c1=jsCreateElem(toJSStr(E(_bW))),_c2=_c1,_c3=jsAppendChild(_c2,E(_c0)[1]),_c4=[0,_c2],_c5=B(A(_bY,[_bZ,_c4,_])),_c6=_c5;return _c4;},_c7=function(_c8,_c9,_){var _ca=E(_c8);if(!_ca[0]){return _c9;}else{var _cb=B(_bX(_56,_ca[1],_c9,_)),_cc=_cb,_cd=B(_c7(_ca[2],_c9,_)),_ce=_cd;return _c9;}},_cf=new T(function(){return B(unCStr("lined"));}),_cg=new T(function(){return B(unCStr("span"));}),_ch=function(_ci,_cj,_ck,_cl,_){var _cm=B(A(_ck,[_cl,_])),_cn=_cm,_co=E(_cn),_cp=E(_co[1]),_cq=_cp[1];return [0,[0,function(_cr,_){var _cs=jsFind(toJSStr(E(_ci))),_ct=_cs,_cu=E(_ct);if(!_cu[0]){return _cr;}else{var _cv=_cu[1];switch(E(_cj)){case 0:var _cw=B(A(_cq,[_cv,_])),_cx=_cw;return _cr;case 1:var _cy=E(_cv),_cz=_cy[1],_cA=jsGetChildren(_cz),_cB=_cA,_cC=E(_cB);if(!_cC[0]){var _cD=B(A(_cq,[_cy,_])),_cE=_cD;return _cr;}else{var _cF=jsCreateElem(toJSStr(E(_cg))),_cG=_cF,_cH=jsAddChildBefore(_cG,_cz,E(_cC[1])[1]),_cI=B(A(_cq,[[0,_cG],_])),_cJ=_cI;return _cr;}break;default:var _cK=E(_cv),_cL=jsClearChildren(_cK[1]),_cM=B(A(_cq,[_cK,_])),_cN=_cM;return _cr;}}},_cp[2]],_co[2]];},_cO=function(_cP,_cQ){while(1){var _cR=E(_cP);if(!_cR[0]){return E(_cQ)[0]==0?1:0;}else{var _cS=E(_cQ);if(!_cS[0]){return 2;}else{var _cT=E(_cR[1])[1],_cU=E(_cS[1])[1];if(_cT!=_cU){return _cT>_cU?2:0;}else{_cP=_cR[2];_cQ=_cS[2];continue;}}}}},_cV=new T(function(){return B(_e(_9,_9));}),_cW=function(_cX,_cY,_cZ,_d0,_d1,_d2,_d3,_d4){var _d5=[0,_cX,_cY,_cZ],_d6=function(_d7){var _d8=E(_d0);if(!_d8[0]){var _d9=E(_d4);if(!_d9[0]){switch(B(_cO(_cX,_d1))){case 0:return [0,[0,_d1,_d2,_d3],_9];case 1:return _cY>=_d2?_cY!=_d2?[0,_d5,_9]:_cZ>=_d3?_cZ!=_d3?[0,_d5,_9]:[0,_d5,_cV]:[0,[0,_d1,_d2,_d3],_9]:[0,[0,_d1,_d2,_d3],_9];default:return [0,_d5,_9];}}else{return [0,[0,_d1,_d2,_d3],_d9];}}else{switch(B(_cO(_cX,_d1))){case 0:return [0,[0,_d1,_d2,_d3],_d4];case 1:return _cY>=_d2?_cY!=_d2?[0,_d5,_d8]:_cZ>=_d3?_cZ!=_d3?[0,_d5,_d8]:[0,_d5,new T(function(){return B(_e(_d8,_d4));})]:[0,[0,_d1,_d2,_d3],_d4]:[0,[0,_d1,_d2,_d3],_d4];default:return [0,_d5,_d8];}}};if(!E(_d4)[0]){var _da=E(_d0);return _da[0]==0?B(_d6(_)):[0,_d5,_da];}else{return new F(function(){return _d6(_);});}},_db=function(_dc,_dd){while(1){var _de=E(_dc);if(!_de[0]){return E(_dd);}else{_dc=_de[2];var _df=[1,_de[1],_dd];_dd=_df;continue;}}},_dg=new T(function(){return B(_db(_9,_9));}),_dh=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_di=new T(function(){return B(err(_dh));}),_dj=function(_dk,_dl,_dm,_dn,_do){var _dp=function(_dq,_dr,_ds){var _dt=[1,_dr,_dq];return new F(function(){return A(_dk,[_ds,new T(function(){var _du=E(_dq);return function(_dv,_dw,_dx){return new F(function(){return _dp(_dt,_dv,_dw);});};}),_dn,_di,function(_dy){return new F(function(){return A(_dm,[new T(function(){return B(_db(_dt,_9));}),_ds,new T(function(){var _dz=E(E(_ds)[2]),_dA=E(_dy),_dB=E(_dA[1]),_dC=B(_cW(_dB[1],_dB[2],_dB[3],_dA[2],_dz[1],_dz[2],_dz[3],_9));return [0,E(_dC[1]),_dC[2]];})]);});}]);});};return new F(function(){return A(_dk,[_dl,function(_dD,_dE,_dF){return new F(function(){return _dp(_9,_dD,_dE);});},_dn,_di,function(_dG){return new F(function(){return A(_do,[_dg,_dl,new T(function(){var _dH=E(E(_dl)[2]),_dI=E(_dG),_dJ=E(_dI[1]),_dK=B(_cW(_dJ[1],_dJ[2],_dJ[3],_dI[2],_dH[1],_dH[2],_dH[3],_9));return [0,E(_dK[1]),_dK[2]];})]);});}]);});},_dL=function(_dM,_dN){var _dO=E(_dM),_dP=E(_dO[1]),_dQ=E(_dN),_dR=E(_dQ[1]),_dS=B(_cW(_dP[1],_dP[2],_dP[3],_dO[2],_dR[1],_dR[2],_dR[3],_dQ[2]));return [0,E(_dS[1]),_dS[2]];},_dT=function(_dU,_dV,_dW,_dX,_dY,_dZ){var _e0=function(_e1,_e2,_e3,_e4,_e5){return new F(function(){return _dj(_dU,_e2,function(_e6,_e7,_e8){return new F(function(){return A(_e3,[[1,_e1,_e6],_e7,new T(function(){var _e9=E(E(_e7)[2]),_ea=E(_e8),_eb=E(_ea[1]),_ec=B(_cW(_eb[1],_eb[2],_eb[3],_ea[2],_e9[1],_e9[2],_e9[3],_9));return [0,E(_ec[1]),_ec[2]];})]);});},_e4,function(_ed,_ee,_ef){return new F(function(){return A(_e5,[[1,_e1,_ed],_ee,new T(function(){var _eg=E(E(_ee)[2]),_eh=E(_ef),_ei=E(_eh[1]),_ej=B(_cW(_ei[1],_ei[2],_ei[3],_eh[2],_eg[1],_eg[2],_eg[3],_9));return [0,E(_ej[1]),_ej[2]];})]);});});});};return new F(function(){return A(_dU,[_dV,function(_ek,_el,_em){return new F(function(){return _e0(_ek,_el,_dW,_dX,function(_en,_eo,_ep){return new F(function(){return A(_dW,[_en,_eo,new T(function(){return B(_dL(_em,_ep));})]);});});});},_dX,function(_eq,_er,_es){return new F(function(){return _e0(_eq,_er,_dW,_dX,function(_et,_eu,_ev){return new F(function(){return A(_dY,[_et,_eu,new T(function(){return B(_dL(_es,_ev));})]);});});});},_dZ]);});},_ew=function(_ex,_ey,_ez,_eA,_eB){var _eC=function(_eD,_eE){return new F(function(){return A(_ex,[_eE,new T(function(){var _eF=E(_eD);return function(_eG,_eH,_eI){return new F(function(){return _eC(_9,_eH);});};}),_eA,_di,function(_eJ){return new F(function(){return A(_ez,[_5c,_eE,new T(function(){var _eK=E(E(_eE)[2]),_eL=E(_eJ),_eM=E(_eL[1]),_eN=B(_cW(_eM[1],_eM[2],_eM[3],_eL[2],_eK[1],_eK[2],_eK[3],_9));return [0,E(_eN[1]),_eN[2]];})]);});}]);});};return new F(function(){return A(_ex,[_ey,function(_eO,_eP,_eQ){return new F(function(){return _eC(_9,_eP);});},_eA,_di,function(_eR){return new F(function(){return A(_eB,[_5c,_ey,new T(function(){var _eS=E(E(_ey)[2]),_eT=E(_eR),_eU=E(_eT[1]),_eV=B(_cW(_eU[1],_eU[2],_eU[3],_eT[2],_eS[1],_eS[2],_eS[3],_9));return [0,E(_eV[1]),_eV[2]];})]);});}]);});},_eW=function(_eX,_eY,_eZ,_f0,_f1,_f2,_f3){var _f4=function(_f5,_f6,_f7,_f8,_f9){var _fa=[1,_f5,_9],_fb=function(_fc,_fd,_fe,_ff){return new F(function(){return _eW(_eX,_eY,_fc,function(_fg,_fh,_fi){return new F(function(){return A(_fd,[[1,_f5,_fg],_fh,new T(function(){var _fj=E(E(_fh)[2]),_fk=E(_fi),_fl=E(_fk[1]),_fm=B(_cW(_fl[1],_fl[2],_fl[3],_fk[2],_fj[1],_fj[2],_fj[3],_9));return [0,E(_fm[1]),_fm[2]];})]);});},_fe,function(_fn,_fo,_fp){return new F(function(){return A(_ff,[[1,_f5,_fn],_fo,new T(function(){var _fq=E(E(_fo)[2]),_fr=E(_fp),_fs=E(_fr[1]),_ft=B(_cW(_fs[1],_fs[2],_fs[3],_fr[2],_fq[1],_fq[2],_fq[3],_9));return [0,E(_ft[1]),_ft[2]];})]);});},function(_fu){return new F(function(){return A(_ff,[_fa,_fc,new T(function(){var _fv=E(E(_fc)[2]),_fw=_fv[1],_fx=_fv[2],_fy=_fv[3],_fz=E(_fu),_fA=E(_fz[1]),_fB=B(_cW(_fA[1],_fA[2],_fA[3],_fz[2],_fw,_fx,_fy,_9)),_fC=E(_fB[1]),_fD=B(_cW(_fC[1],_fC[2],_fC[3],_fB[2],_fw,_fx,_fy,_9));return [0,E(_fD[1]),_fD[2]];})]);});});});};return new F(function(){return A(_eY,[_f6,function(_fE,_fF,_fG){return new F(function(){return _fb(_fF,_f7,_f8,function(_fH,_fI,_fJ){return new F(function(){return A(_f7,[_fH,_fI,new T(function(){return B(_dL(_fG,_fJ));})]);});});});},_f8,function(_fK,_fL,_fM){return new F(function(){return _fb(_fL,_f7,_f8,function(_fN,_fO,_fP){return new F(function(){return A(_f9,[_fN,_fO,new T(function(){return B(_dL(_fM,_fP));})]);});});});},function(_fQ){return new F(function(){return A(_f9,[_fa,_f6,new T(function(){var _fR=E(E(_f6)[2]),_fS=E(_fQ),_fT=E(_fS[1]),_fU=B(_cW(_fT[1],_fT[2],_fT[3],_fS[2],_fR[1],_fR[2],_fR[3],_9));return [0,E(_fU[1]),_fU[2]];})]);});}]);});};return new F(function(){return A(_eX,[_eZ,function(_fV,_fW,_fX){return new F(function(){return _f4(_fV,_fW,_f0,_f1,function(_fY,_fZ,_g0){return new F(function(){return A(_f0,[_fY,_fZ,new T(function(){return B(_dL(_fX,_g0));})]);});});});},_f1,function(_g1,_g2,_g3){return new F(function(){return _f4(_g1,_g2,_f0,_f1,function(_g4,_g5,_g6){return new F(function(){return A(_f2,[_g4,_g5,new T(function(){return B(_dL(_g3,_g6));})]);});});});},_f3]);});},_g7=function(_g8,_g9){return new F(function(){return A(_g9,[_g8]);});},_ga=[0,34],_gb=[1,_ga,_9],_gc=[0,E(_9)],_gd=[1,_gc,_9],_ge=function(_gf,_gg){var _gh=_gf%_gg;if(_gf<=0){if(_gf>=0){return E(_gh);}else{if(_gg<=0){return E(_gh);}else{var _gi=E(_gh);return _gi==0?0:_gi+_gg|0;}}}else{if(_gg>=0){if(_gf>=0){return E(_gh);}else{if(_gg<=0){return E(_gh);}else{var _gj=E(_gh);return _gj==0?0:_gj+_gg|0;}}}else{var _gk=E(_gh);return _gk==0?0:_gk+_gg|0;}}},_gl=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_gm=new T(function(){return B(err(_gl));}),_gn=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_go=new T(function(){return B(err(_gn));}),_gp=function(_gq,_gr){while(1){var _gs=E(_gq);if(!_gs[0]){return E(_go);}else{var _gt=E(_gr);if(!_gt){return E(_gs[1]);}else{_gq=_gs[2];_gr=_gt-1|0;continue;}}}},_gu=new T(function(){return B(unCStr("ACK"));}),_gv=new T(function(){return B(unCStr("BEL"));}),_gw=new T(function(){return B(unCStr("BS"));}),_gx=new T(function(){return B(unCStr("SP"));}),_gy=[1,_gx,_9],_gz=new T(function(){return B(unCStr("US"));}),_gA=[1,_gz,_gy],_gB=new T(function(){return B(unCStr("RS"));}),_gC=[1,_gB,_gA],_gD=new T(function(){return B(unCStr("GS"));}),_gE=[1,_gD,_gC],_gF=new T(function(){return B(unCStr("FS"));}),_gG=[1,_gF,_gE],_gH=new T(function(){return B(unCStr("ESC"));}),_gI=[1,_gH,_gG],_gJ=new T(function(){return B(unCStr("SUB"));}),_gK=[1,_gJ,_gI],_gL=new T(function(){return B(unCStr("EM"));}),_gM=[1,_gL,_gK],_gN=new T(function(){return B(unCStr("CAN"));}),_gO=[1,_gN,_gM],_gP=new T(function(){return B(unCStr("ETB"));}),_gQ=[1,_gP,_gO],_gR=new T(function(){return B(unCStr("SYN"));}),_gS=[1,_gR,_gQ],_gT=new T(function(){return B(unCStr("NAK"));}),_gU=[1,_gT,_gS],_gV=new T(function(){return B(unCStr("DC4"));}),_gW=[1,_gV,_gU],_gX=new T(function(){return B(unCStr("DC3"));}),_gY=[1,_gX,_gW],_gZ=new T(function(){return B(unCStr("DC2"));}),_h0=[1,_gZ,_gY],_h1=new T(function(){return B(unCStr("DC1"));}),_h2=[1,_h1,_h0],_h3=new T(function(){return B(unCStr("DLE"));}),_h4=[1,_h3,_h2],_h5=new T(function(){return B(unCStr("SI"));}),_h6=[1,_h5,_h4],_h7=new T(function(){return B(unCStr("SO"));}),_h8=[1,_h7,_h6],_h9=new T(function(){return B(unCStr("CR"));}),_ha=[1,_h9,_h8],_hb=new T(function(){return B(unCStr("FF"));}),_hc=[1,_hb,_ha],_hd=new T(function(){return B(unCStr("VT"));}),_he=[1,_hd,_hc],_hf=new T(function(){return B(unCStr("LF"));}),_hg=[1,_hf,_he],_hh=new T(function(){return B(unCStr("HT"));}),_hi=[1,_hh,_hg],_hj=[1,_gw,_hi],_hk=[1,_gv,_hj],_hl=[1,_gu,_hk],_hm=new T(function(){return B(unCStr("ENQ"));}),_hn=[1,_hm,_hl],_ho=new T(function(){return B(unCStr("EOT"));}),_hp=[1,_ho,_hn],_hq=new T(function(){return B(unCStr("ETX"));}),_hr=[1,_hq,_hp],_hs=new T(function(){return B(unCStr("STX"));}),_ht=[1,_hs,_hr],_hu=new T(function(){return B(unCStr("SOH"));}),_hv=[1,_hu,_ht],_hw=new T(function(){return B(unCStr("NUL"));}),_hx=[1,_hw,_hv],_hy=[0,92],_hz=new T(function(){return B(unCStr("\\DEL"));}),_hA=new T(function(){return B(unCStr("\\a"));}),_hB=new T(function(){return B(unCStr("\\\\"));}),_hC=new T(function(){return B(unCStr("\\SO"));}),_hD=new T(function(){return B(unCStr("\\r"));}),_hE=new T(function(){return B(unCStr("\\f"));}),_hF=new T(function(){return B(unCStr("\\v"));}),_hG=new T(function(){return B(unCStr("\\n"));}),_hH=new T(function(){return B(unCStr("\\t"));}),_hI=new T(function(){return B(unCStr("\\b"));}),_hJ=function(_hK,_hL){if(_hK<=127){var _hM=E(_hK);switch(_hM){case 92:return new F(function(){return _e(_hB,_hL);});break;case 127:return new F(function(){return _e(_hz,_hL);});break;default:if(_hM<32){var _hN=E(_hM);switch(_hN){case 7:return new F(function(){return _e(_hA,_hL);});break;case 8:return new F(function(){return _e(_hI,_hL);});break;case 9:return new F(function(){return _e(_hH,_hL);});break;case 10:return new F(function(){return _e(_hG,_hL);});break;case 11:return new F(function(){return _e(_hF,_hL);});break;case 12:return new F(function(){return _e(_hE,_hL);});break;case 13:return new F(function(){return _e(_hD,_hL);});break;case 14:return new F(function(){return _e(_hC,new T(function(){var _hO=E(_hL);if(!_hO[0]){var _hP=[0];}else{var _hP=E(E(_hO[1])[1])==72?B(unAppCStr("\\&",_hO)):E(_hO);}return _hP;},1));});break;default:return new F(function(){return _e([1,_hy,new T(function(){var _hQ=_hN;return _hQ>=0?B(_gp(_hx,_hQ)):E(_gm);})],_hL);});}}else{return [1,[0,_hM],_hL];}}}else{return [1,_hy,new T(function(){var _hR=jsShowI(_hK),_hS=_hR;return B(_e(fromJSStr(_hS),new T(function(){var _hT=E(_hL);if(!_hT[0]){var _hU=[0];}else{var _hV=E(_hT[1])[1];if(_hV<48){var _hW=E(_hT);}else{var _hW=_hV>57?E(_hT):B(unAppCStr("\\&",_hT));}var _hX=_hW,_hY=_hX,_hU=_hY;}return _hU;},1)));})];}},_hZ=new T(function(){return B(unCStr("\\\""));}),_i0=function(_i1,_i2){var _i3=E(_i1);if(!_i3[0]){return E(_i2);}else{var _i4=_i3[2],_i5=E(E(_i3[1])[1]);if(_i5==34){return new F(function(){return _e(_hZ,new T(function(){return B(_i0(_i4,_i2));},1));});}else{return new F(function(){return _hJ(_i5,new T(function(){return B(_i0(_i4,_i2));}));});}}},_i6=function(_i7,_i8,_i9,_ia,_ib,_ic,_id,_ie,_if,_ig){var _ih=[0,_ib,_ic,_id];return new F(function(){return A(_i7,[new T(function(){return B(A(_i8,[_ia]));}),function(_ii){var _ij=E(_ii);if(!_ij[0]){return E(new T(function(){return B(A(_ig,[[0,E(_ih),_gd]]));}));}else{var _ik=E(_ij[1]),_il=_ik[1],_im=_ik[2];if(!B(A(_i9,[_il]))){return new F(function(){return A(_ig,[[0,E(_ih),[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_il,_9],_gb));})])],_9]]]);});}else{var _in=E(_il);switch(E(_in[1])){case 9:var _io=[0,_ib,_ic,(_id+8|0)-B(_ge(_id-1|0,8))|0];break;case 10:var _io=E([0,_ib,_ic+1|0,1]);break;default:var _io=E([0,_ib,_ic,_id+1|0]);}var _ip=_io,_iq=[0,E(_ip),_9],_ir=[0,_im,E(_ip),E(_ie)];return new F(function(){return A(_if,[_in,_ir,_iq]);});}}}]);});},_is=function(_it,_iu){return E(_it)[1]!=E(_iu)[1];},_iv=function(_iw,_ix){return E(_iw)[1]==E(_ix)[1];},_iy=[0,_iv,_is],_iz=new T(function(){return B(unCStr(" 	"));}),_iA=function(_iB){return new F(function(){return _86(_iy,_iB,_iz);});},_iC=function(_iD,_iE){return E(_iE);},_iF=function(_iG){return new F(function(){return err(_iG);});},_iH=function(_iI){return E(_iI);},_iJ=[0,_g7,_iC,_iH,_iF],_iK=function(_iL){return E(E(_iL)[3]);},_iM=function(_iN,_iO){var _iP=E(_iO);return _iP[0]==0?B(A(_iK,[_iN,_28])):B(A(_iK,[_iN,[1,[0,_iP[1],_iP[2]]]]));},_iQ=function(_iR){return new F(function(){return _iM(_iJ,_iR);});},_iS=function(_iT,_iU,_iV,_iW,_iX){var _iY=E(_iT),_iZ=E(_iY[2]);return new F(function(){return _i6(_g7,_iQ,_iA,_iY[1],_iZ[1],_iZ[2],_iZ[3],_iY[3],_iU,_iX);});},_j0=function(_j1){return [2,E(E(_j1))];},_j2=function(_j3,_j4){switch(E(_j3)[0]){case 0:switch(E(_j4)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_j4)[0]==1?false:true;case 2:return E(_j4)[0]==2?false:true;default:return E(_j4)[0]==3?false:true;}},_j5=[2,E(_9)],_j6=function(_j7){return new F(function(){return _j2(_j5,_j7);});},_j8=function(_j9,_ja,_jb){var _jc=E(_jb);if(!_jc[0]){return [0,_j9,[1,_j5,new T(function(){return B(_7u(_j6,_ja));})]];}else{var _jd=_jc[1],_je=E(_jc[2]);if(!_je[0]){var _jf=new T(function(){return [2,E(E(_jd))];});return [0,_j9,[1,_jf,new T(function(){return B(_7u(function(_j7){return new F(function(){return _j2(_jf,_j7);});},_ja));})]];}else{var _jg=new T(function(){return [2,E(E(_jd))];}),_jh=function(_ji){var _jj=E(_ji);if(!_jj[0]){return [0,_j9,[1,_jg,new T(function(){return B(_7u(function(_j7){return new F(function(){return _j2(_jg,_j7);});},_ja));})]];}else{var _jk=B(_jh(_jj[2]));return [0,_jk[1],[1,new T(function(){return B(_j0(_jj[1]));}),_jk[2]]];}};return new F(function(){return (function(_jl,_jm){var _jn=B(_jh(_jm));return [0,_jn[1],[1,new T(function(){return B(_j0(_jl));}),_jn[2]]];})(_je[1],_je[2]);});}}},_jo=function(_jp,_jq){var _jr=E(_jp),_js=B(_j8(_jr[1],_jr[2],_jq));return [0,E(_js[1]),_js[2]];},_jt=function(_ju,_jv,_jw,_jx,_jy,_jz,_jA){return new F(function(){return A(_ju,[_jw,_jx,_jy,function(_jB,_jC,_jD){return new F(function(){return A(_jz,[_jB,_jC,new T(function(){var _jE=E(_jD),_jF=E(_jE[2]);if(!_jF[0]){var _jG=E(_jE);}else{var _jH=B(_j8(_jE[1],_jF,_jv)),_jG=[0,E(_jH[1]),_jH[2]];}var _jI=_jG;return _jI;})]);});},function(_jJ){return new F(function(){return A(_jA,[new T(function(){return B(_jo(_jJ,_jv));})]);});}]);});},_jK=new T(function(){return B(unCStr("digit"));}),_jL=[1,_jK,_9],_jM=function(_jN){return new F(function(){return _iM(_iJ,_jN);});},_jO=function(_jP){var _jQ=E(_jP)[1];return _jQ<48?false:_jQ<=57;},_jR=function(_jS,_jT,_jU,_jV,_jW){var _jX=E(_jS),_jY=E(_jX[2]);return new F(function(){return _i6(_g7,_jM,_jO,_jX[1],_jY[1],_jY[2],_jY[3],_jX[3],_jT,_jW);});},_jZ=function(_k0,_k1,_k2,_k3,_k4){return new F(function(){return _jt(_jR,_jL,_k0,_k1,_k2,_k3,_k4);});},_k5=function(_k6,_k7,_k8,_k9,_ka){return new F(function(){return _dT(_jZ,_k6,_k7,_k8,_k9,_ka);});},_kb=function(_kc){return [0,_kc,function(_j7){return new F(function(){return _iM(_kc,_j7);});}];},_kd=new T(function(){return B(_kb(_iJ));}),_ke=function(_kf,_kg){return function(_kh,_ki,_kj,_kk,_kl){return new F(function(){return _jt(function(_km,_kn,_ko,_kp,_kq){var _kr=E(_kf),_ks=E(_km),_kt=E(_ks[2]);return new F(function(){return _i6(E(_kr[1])[1],_kr[2],function(_ku){return new F(function(){return _iv(_ku,_kg);});},_ks[1],_kt[1],_kt[2],_kt[3],_ks[3],_kn,_kq);});},[1,[1,_ga,new T(function(){return B(_i0([1,_kg,_9],_gb));})],_9],_kh,_ki,_kj,_kk,_kl);});};},_kv=[0,44],_kw=new T(function(){return B(_ke(_kd,_kv));}),_kx=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_ky=new T(function(){return B(err(_kx));}),_kz=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kA=new T(function(){return B(err(_kz));}),_kB=new T(function(){return B(_3B("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_kC=function(_kD,_kE){while(1){var _kF=(function(_kG,_kH){var _kI=E(_kG);switch(_kI[0]){case 0:var _kJ=E(_kH);if(!_kJ[0]){return [0];}else{_kD=B(A(_kI[1],[_kJ[1]]));_kE=_kJ[2];return null;}break;case 1:var _kK=B(A(_kI[1],[_kH])),_kL=_kH;_kD=_kK;_kE=_kL;return null;case 2:return [0];case 3:return [1,[0,_kI[1],_kH],new T(function(){return B(_kC(_kI[2],_kH));})];default:return E(_kI[1]);}})(_kD,_kE);if(_kF!=null){return _kF;}}},_kM=function(_kN,_kO){var _kP=function(_kQ){var _kR=E(_kO);if(_kR[0]==3){return [3,_kR[1],new T(function(){return B(_kM(_kN,_kR[2]));})];}else{var _kS=E(_kN);if(_kS[0]==2){return E(_kR);}else{var _kT=E(_kR);if(_kT[0]==2){return E(_kS);}else{var _kU=function(_kV){var _kW=E(_kT);if(_kW[0]==4){return [1,function(_kX){return [4,new T(function(){return B(_e(B(_kC(_kS,_kX)),_kW[1]));})];}];}else{var _kY=E(_kS);if(_kY[0]==1){var _kZ=_kY[1],_l0=E(_kW);return _l0[0]==0?[1,function(_l1){return new F(function(){return _kM(B(A(_kZ,[_l1])),_l0);});}]:[1,function(_l2){return new F(function(){return _kM(B(A(_kZ,[_l2])),new T(function(){return B(A(_l0[1],[_l2]));}));});}];}else{var _l3=E(_kW);return _l3[0]==0?E(_kB):[1,function(_l4){return new F(function(){return _kM(_kY,new T(function(){return B(A(_l3[1],[_l4]));}));});}];}}},_l5=E(_kS);switch(_l5[0]){case 1:var _l6=E(_kT);if(_l6[0]==4){return [1,function(_l7){return [4,new T(function(){return B(_e(B(_kC(B(A(_l5[1],[_l7])),_l7)),_l6[1]));})];}];}else{return new F(function(){return _kU(_);});}break;case 4:var _l8=_l5[1],_l9=E(_kT);switch(_l9[0]){case 0:return [1,function(_la){return [4,new T(function(){return B(_e(_l8,new T(function(){return B(_kC(_l9,_la));},1)));})];}];case 1:return [1,function(_lb){return [4,new T(function(){return B(_e(_l8,new T(function(){return B(_kC(B(A(_l9[1],[_lb])),_lb));},1)));})];}];default:return [4,new T(function(){return B(_e(_l8,_l9[1]));})];}break;default:return new F(function(){return _kU(_);});}}}}},_lc=E(_kN);switch(_lc[0]){case 0:var _ld=E(_kO);if(!_ld[0]){return [0,function(_le){return new F(function(){return _kM(B(A(_lc[1],[_le])),new T(function(){return B(A(_ld[1],[_le]));}));});}];}else{return new F(function(){return _kP(_);});}break;case 3:return [3,_lc[1],new T(function(){return B(_kM(_lc[2],_kO));})];default:return new F(function(){return _kP(_);});}},_lf=[0,41],_lg=[1,_lf,_9],_lh=[0,40],_li=[1,_lh,_9],_lj=function(_lk,_ll){while(1){var _lm=E(_lk);if(!_lm[0]){return E(_ll)[0]==0?true:false;}else{var _ln=E(_ll);if(!_ln[0]){return false;}else{if(E(_lm[1])[1]!=E(_ln[1])[1]){return false;}else{_lk=_lm[2];_ll=_ln[2];continue;}}}}},_lo=function(_lp,_lq){var _lr=E(_lp);switch(_lr[0]){case 0:return [0,function(_ls){return new F(function(){return _lo(B(A(_lr[1],[_ls])),_lq);});}];case 1:return [1,function(_lt){return new F(function(){return _lo(B(A(_lr[1],[_lt])),_lq);});}];case 2:return [2];case 3:return new F(function(){return _kM(B(A(_lq,[_lr[1]])),new T(function(){return B(_lo(_lr[2],_lq));}));});break;default:var _lu=function(_lv){var _lw=E(_lv);if(!_lw[0]){return [0];}else{var _lx=E(_lw[1]);return new F(function(){return _e(B(_kC(B(A(_lq,[_lx[1]])),_lx[2])),new T(function(){return B(_lu(_lw[2]));},1));});}},_ly=B(_lu(_lr[1]));return _ly[0]==0?[2]:[4,_ly];}},_lz=[2],_lA=function(_lB){return [3,_lB,_lz];},_lC=function(_lD,_lE){var _lF=E(_lD);if(!_lF){return new F(function(){return A(_lE,[_5c]);});}else{return [0,function(_lG){return E(new T(function(){return B(_lC(_lF-1|0,_lE));}));}];}},_lH=function(_lI,_lJ,_lK){return function(_lL){return new F(function(){return A(function(_lM,_lN,_lO){while(1){var _lP=(function(_lQ,_lR,_lS){var _lT=E(_lQ);switch(_lT[0]){case 0:var _lU=E(_lR);if(!_lU[0]){return E(_lJ);}else{_lM=B(A(_lT[1],[_lU[1]]));_lN=_lU[2];var _lV=_lS+1|0;_lO=_lV;return null;}break;case 1:var _lW=B(A(_lT[1],[_lR])),_lX=_lR,_lV=_lS;_lM=_lW;_lN=_lX;_lO=_lV;return null;case 2:return E(_lJ);case 3:return function(_lY){return new F(function(){return _lC(_lS,function(_lZ){return E(new T(function(){return B(_lo(_lT,_lY));}));});});};default:return function(_m0){return new F(function(){return _lo(_lT,_m0);});};}})(_lM,_lN,_lO);if(_lP!=null){return _lP;}}},[new T(function(){return B(A(_lI,[_lA]));}),_lL,0,_lK]);});};},_m1=function(_m2){return new F(function(){return A(_m2,[_9]);});},_m3=function(_m4,_m5){var _m6=function(_m7){var _m8=E(_m7);if(!_m8[0]){return E(_m1);}else{var _m9=_m8[1];return !B(A(_m4,[_m9]))?E(_m1):function(_ma){return [0,function(_mb){return E(new T(function(){return B(A(new T(function(){return B(_m6(_m8[2]));}),[function(_mc){return new F(function(){return A(_ma,[[1,_m9,_mc]]);});}]));}));}];};}};return function(_md){return new F(function(){return A(_m6,[_md,_m5]);});};},_me=[6],_mf=new T(function(){return B(unCStr("valDig: Bad base"));}),_mg=new T(function(){return B(err(_mf));}),_mh=function(_mi,_mj){var _mk=function(_ml,_mm){var _mn=E(_ml);if(!_mn[0]){return function(_mo){return new F(function(){return A(_mo,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{var _mp=E(_mn[1])[1],_mq=function(_mr){return function(_ms){return [0,function(_mt){return E(new T(function(){return B(A(new T(function(){return B(_mk(_mn[2],function(_mu){return new F(function(){return A(_mm,[[1,_mr,_mu]]);});}));}),[_ms]));}));}];};};switch(E(E(_mi)[1])){case 8:if(48>_mp){return function(_mv){return new F(function(){return A(_mv,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{if(_mp>55){return function(_mw){return new F(function(){return A(_mw,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{return new F(function(){return _mq([0,_mp-48|0]);});}}break;case 10:if(48>_mp){return function(_mx){return new F(function(){return A(_mx,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{if(_mp>57){return function(_my){return new F(function(){return A(_my,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{return new F(function(){return _mq([0,_mp-48|0]);});}}break;case 16:if(48>_mp){if(97>_mp){if(65>_mp){return function(_mz){return new F(function(){return A(_mz,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{if(_mp>70){return function(_mA){return new F(function(){return A(_mA,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{return new F(function(){return _mq([0,(_mp-65|0)+10|0]);});}}}else{if(_mp>102){if(65>_mp){return function(_mB){return new F(function(){return A(_mB,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{if(_mp>70){return function(_mC){return new F(function(){return A(_mC,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{return new F(function(){return _mq([0,(_mp-65|0)+10|0]);});}}}else{return new F(function(){return _mq([0,(_mp-97|0)+10|0]);});}}}else{if(_mp>57){if(97>_mp){if(65>_mp){return function(_mD){return new F(function(){return A(_mD,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{if(_mp>70){return function(_mE){return new F(function(){return A(_mE,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{return new F(function(){return _mq([0,(_mp-65|0)+10|0]);});}}}else{if(_mp>102){if(65>_mp){return function(_mF){return new F(function(){return A(_mF,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{if(_mp>70){return function(_mG){return new F(function(){return A(_mG,[new T(function(){return B(A(_mm,[_9]));})]);});};}else{return new F(function(){return _mq([0,(_mp-65|0)+10|0]);});}}}else{return new F(function(){return _mq([0,(_mp-97|0)+10|0]);});}}}else{return new F(function(){return _mq([0,_mp-48|0]);});}}break;default:return E(_mg);}}};return function(_mH){return new F(function(){return A(_mk,[_mH,_5q,function(_mI){var _mJ=E(_mI);return _mJ[0]==0?[2]:B(A(_mj,[_mJ]));}]);});};},_mK=[0,10],_mL=[0,1],_mM=[0,2147483647],_mN=function(_mO,_mP){while(1){var _mQ=E(_mO);if(!_mQ[0]){var _mR=_mQ[1],_mS=E(_mP);if(!_mS[0]){var _mT=_mS[1],_mU=addC(_mR,_mT);if(!E(_mU[2])){return [0,_mU[1]];}else{_mO=[1,I_fromInt(_mR)];_mP=[1,I_fromInt(_mT)];continue;}}else{_mO=[1,I_fromInt(_mR)];_mP=_mS;continue;}}else{var _mV=E(_mP);if(!_mV[0]){_mO=_mQ;_mP=[1,I_fromInt(_mV[1])];continue;}else{return [1,I_add(_mQ[1],_mV[1])];}}}},_mW=new T(function(){return B(_mN(_mM,_mL));}),_mX=function(_mY){var _mZ=E(_mY);if(!_mZ[0]){var _n0=E(_mZ[1]);return _n0==(-2147483648)?E(_mW):[0, -_n0];}else{return [1,I_negate(_mZ[1])];}},_n1=[0,10],_n2=[0,0],_n3=function(_n4){return [0,_n4];},_n5=function(_n6,_n7){while(1){var _n8=E(_n6);if(!_n8[0]){var _n9=_n8[1],_na=E(_n7);if(!_na[0]){var _nb=_na[1];if(!(imul(_n9,_nb)|0)){return [0,imul(_n9,_nb)|0];}else{_n6=[1,I_fromInt(_n9)];_n7=[1,I_fromInt(_nb)];continue;}}else{_n6=[1,I_fromInt(_n9)];_n7=_na;continue;}}else{var _nc=E(_n7);if(!_nc[0]){_n6=_n8;_n7=[1,I_fromInt(_nc[1])];continue;}else{return [1,I_mul(_n8[1],_nc[1])];}}}},_nd=function(_ne,_nf,_ng){while(1){var _nh=E(_ng);if(!_nh[0]){return E(_nf);}else{var _ni=B(_mN(B(_n5(_nf,_ne)),B(_n3(E(_nh[1])[1]))));_ng=_nh[2];_nf=_ni;continue;}}},_nj=function(_nk){var _nl=new T(function(){return B(_kM(B(_kM([0,function(_nm){return E(E(_nm)[1])==45?[1,B(_mh(_mK,function(_nn){return new F(function(){return A(_nk,[[1,new T(function(){return B(_mX(B(_nd(_n1,_n2,_nn))));})]]);});}))]:[2];}],[0,function(_no){return E(E(_no)[1])==43?[1,B(_mh(_mK,function(_np){return new F(function(){return A(_nk,[[1,new T(function(){return B(_nd(_n1,_n2,_np));})]]);});}))]:[2];}])),new T(function(){return [1,B(_mh(_mK,function(_nq){return new F(function(){return A(_nk,[[1,new T(function(){return B(_nd(_n1,_n2,_nq));})]]);});}))];})));});return new F(function(){return _kM([0,function(_nr){return E(E(_nr)[1])==101?E(_nl):[2];}],[0,function(_ns){return E(E(_ns)[1])==69?E(_nl):[2];}]);});},_nt=function(_nu){return new F(function(){return A(_nu,[_28]);});},_nv=function(_nw){return new F(function(){return A(_nw,[_28]);});},_nx=function(_ny){return function(_nz){return E(E(_nz)[1])==46?[1,B(_mh(_mK,function(_nA){return new F(function(){return A(_ny,[[1,_nA]]);});}))]:[2];};},_nB=function(_nC){return [0,B(_nx(_nC))];},_nD=function(_nE){return new F(function(){return _mh(_mK,function(_nF){return [1,B(_lH(_nB,_nt,function(_nG){return [1,B(_lH(_nj,_nv,function(_nH){return new F(function(){return A(_nE,[[5,[1,_nF,_nG,_nH]]]);});}))];}))];});});},_nI=function(_nJ){return [1,B(_nD(_nJ))];},_nK=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_nL=function(_nM){return new F(function(){return _86(_iy,_nM,_nK);});},_nN=[0,8],_nO=[0,16],_nP=function(_nQ){var _nR=function(_nS){return new F(function(){return A(_nQ,[[5,[0,_nN,_nS]]]);});},_nT=function(_nU){return new F(function(){return A(_nQ,[[5,[0,_nO,_nU]]]);});};return function(_nV){return E(E(_nV)[1])==48?E([0,function(_nW){switch(E(E(_nW)[1])){case 79:return [1,B(_mh(_nN,_nR))];case 88:return [1,B(_mh(_nO,_nT))];case 111:return [1,B(_mh(_nN,_nR))];case 120:return [1,B(_mh(_nO,_nT))];default:return [2];}}]):[2];};},_nX=function(_nY){return [0,B(_nP(_nY))];},_nZ=true,_o0=function(_o1){var _o2=new T(function(){return B(A(_o1,[_nN]));}),_o3=new T(function(){return B(A(_o1,[_nO]));});return function(_o4){switch(E(E(_o4)[1])){case 79:return E(_o2);case 88:return E(_o3);case 111:return E(_o2);case 120:return E(_o3);default:return [2];}};},_o5=function(_o6){return [0,B(_o0(_o6))];},_o7=[0,92],_o8=function(_o9){return new F(function(){return A(_o9,[_mK]);});},_oa=function(_ob){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_ob,_9));}))));});},_oc=function(_od){var _oe=E(_od);return _oe[0]==0?E(_oe[1]):I_toInt(_oe[1]);},_of=function(_og,_oh){var _oi=E(_og);if(!_oi[0]){var _oj=_oi[1],_ok=E(_oh);return _ok[0]==0?_oj<=_ok[1]:I_compareInt(_ok[1],_oj)>=0;}else{var _ol=_oi[1],_om=E(_oh);return _om[0]==0?I_compareInt(_ol,_om[1])<=0:I_compare(_ol,_om[1])<=0;}},_on=function(_oo){return [2];},_op=function(_oq){var _or=E(_oq);if(!_or[0]){return E(_on);}else{var _os=_or[1],_ot=E(_or[2]);return _ot[0]==0?E(_os):function(_ou){return new F(function(){return _kM(B(A(_os,[_ou])),new T(function(){return B(A(new T(function(){return B(_op(_ot));}),[_ou]));}));});};}},_ov=function(_ow){return [2];},_ox=function(_oy,_oz){var _oA=function(_oB,_oC){var _oD=E(_oB);if(!_oD[0]){return function(_oE){return new F(function(){return A(_oE,[_oy]);});};}else{var _oF=E(_oC);return _oF[0]==0?E(_ov):E(_oD[1])[1]!=E(_oF[1])[1]?E(_ov):function(_oG){return [0,function(_oH){return E(new T(function(){return B(A(new T(function(){return B(_oA(_oD[2],_oF[2]));}),[_oG]));}));}];};}};return function(_oI){return new F(function(){return A(_oA,[_oy,_oI,_oz]);});};},_oJ=new T(function(){return B(unCStr("SOH"));}),_oK=[0,1],_oL=function(_oM){return [1,B(_ox(_oJ,function(_oN){return E(new T(function(){return B(A(_oM,[_oK]));}));}))];},_oO=new T(function(){return B(unCStr("SO"));}),_oP=[0,14],_oQ=function(_oR){return [1,B(_ox(_oO,function(_oS){return E(new T(function(){return B(A(_oR,[_oP]));}));}))];},_oT=function(_oU){return [1,B(_lH(_oL,_oQ,_oU))];},_oV=new T(function(){return B(unCStr("NUL"));}),_oW=[0,0],_oX=function(_oY){return [1,B(_ox(_oV,function(_oZ){return E(new T(function(){return B(A(_oY,[_oW]));}));}))];},_p0=new T(function(){return B(unCStr("STX"));}),_p1=[0,2],_p2=function(_p3){return [1,B(_ox(_p0,function(_p4){return E(new T(function(){return B(A(_p3,[_p1]));}));}))];},_p5=new T(function(){return B(unCStr("ETX"));}),_p6=[0,3],_p7=function(_p8){return [1,B(_ox(_p5,function(_p9){return E(new T(function(){return B(A(_p8,[_p6]));}));}))];},_pa=new T(function(){return B(unCStr("EOT"));}),_pb=[0,4],_pc=function(_pd){return [1,B(_ox(_pa,function(_pe){return E(new T(function(){return B(A(_pd,[_pb]));}));}))];},_pf=new T(function(){return B(unCStr("ENQ"));}),_pg=[0,5],_ph=function(_pi){return [1,B(_ox(_pf,function(_pj){return E(new T(function(){return B(A(_pi,[_pg]));}));}))];},_pk=new T(function(){return B(unCStr("ACK"));}),_pl=[0,6],_pm=function(_pn){return [1,B(_ox(_pk,function(_po){return E(new T(function(){return B(A(_pn,[_pl]));}));}))];},_pp=new T(function(){return B(unCStr("BEL"));}),_pq=[0,7],_pr=function(_ps){return [1,B(_ox(_pp,function(_pt){return E(new T(function(){return B(A(_ps,[_pq]));}));}))];},_pu=new T(function(){return B(unCStr("BS"));}),_pv=[0,8],_pw=function(_px){return [1,B(_ox(_pu,function(_py){return E(new T(function(){return B(A(_px,[_pv]));}));}))];},_pz=new T(function(){return B(unCStr("HT"));}),_pA=[0,9],_pB=function(_pC){return [1,B(_ox(_pz,function(_pD){return E(new T(function(){return B(A(_pC,[_pA]));}));}))];},_pE=new T(function(){return B(unCStr("LF"));}),_pF=[0,10],_pG=function(_pH){return [1,B(_ox(_pE,function(_pI){return E(new T(function(){return B(A(_pH,[_pF]));}));}))];},_pJ=new T(function(){return B(unCStr("VT"));}),_pK=[0,11],_pL=function(_pM){return [1,B(_ox(_pJ,function(_pN){return E(new T(function(){return B(A(_pM,[_pK]));}));}))];},_pO=new T(function(){return B(unCStr("FF"));}),_pP=[0,12],_pQ=function(_pR){return [1,B(_ox(_pO,function(_pS){return E(new T(function(){return B(A(_pR,[_pP]));}));}))];},_pT=new T(function(){return B(unCStr("CR"));}),_pU=[0,13],_pV=function(_pW){return [1,B(_ox(_pT,function(_pX){return E(new T(function(){return B(A(_pW,[_pU]));}));}))];},_pY=new T(function(){return B(unCStr("SI"));}),_pZ=[0,15],_q0=function(_q1){return [1,B(_ox(_pY,function(_q2){return E(new T(function(){return B(A(_q1,[_pZ]));}));}))];},_q3=new T(function(){return B(unCStr("DLE"));}),_q4=[0,16],_q5=function(_q6){return [1,B(_ox(_q3,function(_q7){return E(new T(function(){return B(A(_q6,[_q4]));}));}))];},_q8=new T(function(){return B(unCStr("DC1"));}),_q9=[0,17],_qa=function(_qb){return [1,B(_ox(_q8,function(_qc){return E(new T(function(){return B(A(_qb,[_q9]));}));}))];},_qd=new T(function(){return B(unCStr("DC2"));}),_qe=[0,18],_qf=function(_qg){return [1,B(_ox(_qd,function(_qh){return E(new T(function(){return B(A(_qg,[_qe]));}));}))];},_qi=new T(function(){return B(unCStr("DC3"));}),_qj=[0,19],_qk=function(_ql){return [1,B(_ox(_qi,function(_qm){return E(new T(function(){return B(A(_ql,[_qj]));}));}))];},_qn=new T(function(){return B(unCStr("DC4"));}),_qo=[0,20],_qp=function(_qq){return [1,B(_ox(_qn,function(_qr){return E(new T(function(){return B(A(_qq,[_qo]));}));}))];},_qs=new T(function(){return B(unCStr("NAK"));}),_qt=[0,21],_qu=function(_qv){return [1,B(_ox(_qs,function(_qw){return E(new T(function(){return B(A(_qv,[_qt]));}));}))];},_qx=new T(function(){return B(unCStr("SYN"));}),_qy=[0,22],_qz=function(_qA){return [1,B(_ox(_qx,function(_qB){return E(new T(function(){return B(A(_qA,[_qy]));}));}))];},_qC=new T(function(){return B(unCStr("ETB"));}),_qD=[0,23],_qE=function(_qF){return [1,B(_ox(_qC,function(_qG){return E(new T(function(){return B(A(_qF,[_qD]));}));}))];},_qH=new T(function(){return B(unCStr("CAN"));}),_qI=[0,24],_qJ=function(_qK){return [1,B(_ox(_qH,function(_qL){return E(new T(function(){return B(A(_qK,[_qI]));}));}))];},_qM=new T(function(){return B(unCStr("EM"));}),_qN=[0,25],_qO=function(_qP){return [1,B(_ox(_qM,function(_qQ){return E(new T(function(){return B(A(_qP,[_qN]));}));}))];},_qR=new T(function(){return B(unCStr("SUB"));}),_qS=[0,26],_qT=function(_qU){return [1,B(_ox(_qR,function(_qV){return E(new T(function(){return B(A(_qU,[_qS]));}));}))];},_qW=new T(function(){return B(unCStr("ESC"));}),_qX=[0,27],_qY=function(_qZ){return [1,B(_ox(_qW,function(_r0){return E(new T(function(){return B(A(_qZ,[_qX]));}));}))];},_r1=new T(function(){return B(unCStr("FS"));}),_r2=[0,28],_r3=function(_r4){return [1,B(_ox(_r1,function(_r5){return E(new T(function(){return B(A(_r4,[_r2]));}));}))];},_r6=new T(function(){return B(unCStr("GS"));}),_r7=[0,29],_r8=function(_r9){return [1,B(_ox(_r6,function(_ra){return E(new T(function(){return B(A(_r9,[_r7]));}));}))];},_rb=new T(function(){return B(unCStr("RS"));}),_rc=[0,30],_rd=function(_re){return [1,B(_ox(_rb,function(_rf){return E(new T(function(){return B(A(_re,[_rc]));}));}))];},_rg=new T(function(){return B(unCStr("US"));}),_rh=[0,31],_ri=function(_rj){return [1,B(_ox(_rg,function(_rk){return E(new T(function(){return B(A(_rj,[_rh]));}));}))];},_rl=new T(function(){return B(unCStr("SP"));}),_rm=[0,32],_rn=function(_ro){return [1,B(_ox(_rl,function(_rp){return E(new T(function(){return B(A(_ro,[_rm]));}));}))];},_rq=new T(function(){return B(unCStr("DEL"));}),_rr=[0,127],_rs=function(_rt){return [1,B(_ox(_rq,function(_ru){return E(new T(function(){return B(A(_rt,[_rr]));}));}))];},_rv=[1,_rs,_9],_rw=[1,_rn,_rv],_rx=[1,_ri,_rw],_ry=[1,_rd,_rx],_rz=[1,_r8,_ry],_rA=[1,_r3,_rz],_rB=[1,_qY,_rA],_rC=[1,_qT,_rB],_rD=[1,_qO,_rC],_rE=[1,_qJ,_rD],_rF=[1,_qE,_rE],_rG=[1,_qz,_rF],_rH=[1,_qu,_rG],_rI=[1,_qp,_rH],_rJ=[1,_qk,_rI],_rK=[1,_qf,_rJ],_rL=[1,_qa,_rK],_rM=[1,_q5,_rL],_rN=[1,_q0,_rM],_rO=[1,_pV,_rN],_rP=[1,_pQ,_rO],_rQ=[1,_pL,_rP],_rR=[1,_pG,_rQ],_rS=[1,_pB,_rR],_rT=[1,_pw,_rS],_rU=[1,_pr,_rT],_rV=[1,_pm,_rU],_rW=[1,_ph,_rV],_rX=[1,_pc,_rW],_rY=[1,_p7,_rX],_rZ=[1,_p2,_rY],_s0=[1,_oX,_rZ],_s1=[1,_oT,_s0],_s2=new T(function(){return B(_op(_s1));}),_s3=[0,1114111],_s4=[0,34],_s5=[0,39],_s6=function(_s7){var _s8=new T(function(){return B(A(_s7,[_pq]));}),_s9=new T(function(){return B(A(_s7,[_pv]));}),_sa=new T(function(){return B(A(_s7,[_pA]));}),_sb=new T(function(){return B(A(_s7,[_pF]));}),_sc=new T(function(){return B(A(_s7,[_pK]));}),_sd=new T(function(){return B(A(_s7,[_pP]));}),_se=new T(function(){return B(A(_s7,[_pU]));});return new F(function(){return _kM([0,function(_sf){switch(E(E(_sf)[1])){case 34:return E(new T(function(){return B(A(_s7,[_s4]));}));case 39:return E(new T(function(){return B(A(_s7,[_s5]));}));case 92:return E(new T(function(){return B(A(_s7,[_o7]));}));case 97:return E(_s8);case 98:return E(_s9);case 102:return E(_sd);case 110:return E(_sb);case 114:return E(_se);case 116:return E(_sa);case 118:return E(_sc);default:return [2];}}],new T(function(){return B(_kM([1,B(_lH(_o5,_o8,function(_sg){return [1,B(_mh(_sg,function(_sh){var _si=B(_nd(new T(function(){return B(_n3(E(_sg)[1]));}),_n2,_sh));return !B(_of(_si,_s3))?[2]:B(A(_s7,[new T(function(){var _sj=B(_oc(_si));if(_sj>>>0>1114111){var _sk=B(_oa(_sj));}else{var _sk=[0,_sj];}var _sl=_sk,_sm=_sl,_sn=_sm;return _sn;})]));}))];}))],new T(function(){return B(_kM([0,function(_so){return E(E(_so)[1])==94?E([0,function(_sp){switch(E(E(_sp)[1])){case 64:return E(new T(function(){return B(A(_s7,[_oW]));}));case 65:return E(new T(function(){return B(A(_s7,[_oK]));}));case 66:return E(new T(function(){return B(A(_s7,[_p1]));}));case 67:return E(new T(function(){return B(A(_s7,[_p6]));}));case 68:return E(new T(function(){return B(A(_s7,[_pb]));}));case 69:return E(new T(function(){return B(A(_s7,[_pg]));}));case 70:return E(new T(function(){return B(A(_s7,[_pl]));}));case 71:return E(_s8);case 72:return E(_s9);case 73:return E(_sa);case 74:return E(_sb);case 75:return E(_sc);case 76:return E(_sd);case 77:return E(_se);case 78:return E(new T(function(){return B(A(_s7,[_oP]));}));case 79:return E(new T(function(){return B(A(_s7,[_pZ]));}));case 80:return E(new T(function(){return B(A(_s7,[_q4]));}));case 81:return E(new T(function(){return B(A(_s7,[_q9]));}));case 82:return E(new T(function(){return B(A(_s7,[_qe]));}));case 83:return E(new T(function(){return B(A(_s7,[_qj]));}));case 84:return E(new T(function(){return B(A(_s7,[_qo]));}));case 85:return E(new T(function(){return B(A(_s7,[_qt]));}));case 86:return E(new T(function(){return B(A(_s7,[_qy]));}));case 87:return E(new T(function(){return B(A(_s7,[_qD]));}));case 88:return E(new T(function(){return B(A(_s7,[_qI]));}));case 89:return E(new T(function(){return B(A(_s7,[_qN]));}));case 90:return E(new T(function(){return B(A(_s7,[_qS]));}));case 91:return E(new T(function(){return B(A(_s7,[_qX]));}));case 92:return E(new T(function(){return B(A(_s7,[_r2]));}));case 93:return E(new T(function(){return B(A(_s7,[_r7]));}));case 94:return E(new T(function(){return B(A(_s7,[_rc]));}));case 95:return E(new T(function(){return B(A(_s7,[_rh]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_s2,[_s7]));})));})));}));});},_sq=function(_sr){return new F(function(){return A(_sr,[_5c]);});},_ss=function(_st){var _su=E(_st);if(!_su[0]){return E(_sq);}else{var _sv=_su[2],_sw=E(E(_su[1])[1]);switch(_sw){case 9:return function(_sx){return [0,function(_sy){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sx]));}));}];};case 10:return function(_sz){return [0,function(_sA){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sz]));}));}];};case 11:return function(_sB){return [0,function(_sC){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sB]));}));}];};case 12:return function(_sD){return [0,function(_sE){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sD]));}));}];};case 13:return function(_sF){return [0,function(_sG){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sF]));}));}];};case 32:return function(_sH){return [0,function(_sI){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sH]));}));}];};case 160:return function(_sJ){return [0,function(_sK){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sJ]));}));}];};default:var _sL=u_iswspace(_sw),_sM=_sL;return E(_sM)==0?E(_sq):function(_sN){return [0,function(_sO){return E(new T(function(){return B(A(new T(function(){return B(_ss(_sv));}),[_sN]));}));}];};}}},_sP=function(_sQ){var _sR=new T(function(){return B(_sP(_sQ));}),_sS=[1,function(_sT){return new F(function(){return A(_ss,[_sT,function(_sU){return E([0,function(_sV){return E(E(_sV)[1])==92?E(_sR):[2];}]);}]);});}];return new F(function(){return _kM([0,function(_sW){return E(E(_sW)[1])==92?E([0,function(_sX){var _sY=E(E(_sX)[1]);switch(_sY){case 9:return E(_sS);case 10:return E(_sS);case 11:return E(_sS);case 12:return E(_sS);case 13:return E(_sS);case 32:return E(_sS);case 38:return E(_sR);case 160:return E(_sS);default:var _sZ=u_iswspace(_sY),_t0=_sZ;return E(_t0)==0?[2]:E(_sS);}}]):[2];}],[0,function(_t1){var _t2=E(_t1);return E(_t2[1])==92?E(new T(function(){return B(_s6(function(_t3){return new F(function(){return A(_sQ,[[0,_t3,_nZ]]);});}));})):B(A(_sQ,[[0,_t2,_1S]]));}]);});},_t4=function(_t5,_t6){return new F(function(){return _sP(function(_t7){var _t8=E(_t7),_t9=E(_t8[1]);if(E(_t9[1])==34){if(!E(_t8[2])){return E(new T(function(){return B(A(_t6,[[1,new T(function(){return B(A(_t5,[_9]));})]]));}));}else{return new F(function(){return _t4(function(_ta){return new F(function(){return A(_t5,[[1,_t9,_ta]]);});},_t6);});}}else{return new F(function(){return _t4(function(_tb){return new F(function(){return A(_t5,[[1,_t9,_tb]]);});},_t6);});}});});},_tc=new T(function(){return B(unCStr("_\'"));}),_td=function(_te){var _tf=u_iswalnum(_te),_tg=_tf;return E(_tg)==0?B(_86(_iy,[0,_te],_tc)):true;},_th=function(_ti){return new F(function(){return _td(E(_ti)[1]);});},_tj=new T(function(){return B(unCStr(",;()[]{}`"));}),_tk=new T(function(){return B(unCStr(".."));}),_tl=new T(function(){return B(unCStr("::"));}),_tm=new T(function(){return B(unCStr("->"));}),_tn=[0,64],_to=[1,_tn,_9],_tp=[0,126],_tq=[1,_tp,_9],_tr=new T(function(){return B(unCStr("=>"));}),_ts=[1,_tr,_9],_tt=[1,_tq,_ts],_tu=[1,_to,_tt],_tv=[1,_tm,_tu],_tw=new T(function(){return B(unCStr("<-"));}),_tx=[1,_tw,_tv],_ty=[0,124],_tz=[1,_ty,_9],_tA=[1,_tz,_tx],_tB=[1,_o7,_9],_tC=[1,_tB,_tA],_tD=[0,61],_tE=[1,_tD,_9],_tF=[1,_tE,_tC],_tG=[1,_tl,_tF],_tH=[1,_tk,_tG],_tI=function(_tJ){return new F(function(){return _kM([1,function(_tK){return E(_tK)[0]==0?E(new T(function(){return B(A(_tJ,[_me]));})):[2];}],new T(function(){return B(_kM([0,function(_tL){return E(E(_tL)[1])==39?E([0,function(_tM){var _tN=E(_tM);switch(E(_tN[1])){case 39:return [2];case 92:return E(new T(function(){return B(_s6(function(_tO){return [0,function(_tP){return E(E(_tP)[1])==39?E(new T(function(){return B(A(_tJ,[[0,_tO]]));})):[2];}];}));}));default:return [0,function(_tQ){return E(E(_tQ)[1])==39?E(new T(function(){return B(A(_tJ,[[0,_tN]]));})):[2];}];}}]):[2];}],new T(function(){return B(_kM([0,function(_tR){return E(E(_tR)[1])==34?E(new T(function(){return B(_t4(_5q,_tJ));})):[2];}],new T(function(){return B(_kM([0,function(_tS){return !B(_86(_iy,_tS,_tj))?[2]:B(A(_tJ,[[2,[1,_tS,_9]]]));}],new T(function(){return B(_kM([0,function(_tT){return !B(_86(_iy,_tT,_nK))?[2]:[1,B(_m3(_nL,function(_tU){var _tV=[1,_tT,_tU];return !B(_86(_7i,_tV,_tH))?B(A(_tJ,[[4,_tV]])):B(A(_tJ,[[2,_tV]]));}))];}],new T(function(){return B(_kM([0,function(_tW){var _tX=E(_tW),_tY=_tX[1],_tZ=u_iswalpha(_tY),_u0=_tZ;return E(_u0)==0?E(_tY)==95?[1,B(_m3(_th,function(_u1){return new F(function(){return A(_tJ,[[3,[1,_tX,_u1]]]);});}))]:[2]:[1,B(_m3(_th,function(_u2){return new F(function(){return A(_tJ,[[3,[1,_tX,_u2]]]);});}))];}],new T(function(){return [1,B(_lH(_nX,_nI,_tJ))];})));})));})));})));})));}));});},_u3=[0,0],_u4=function(_u5,_u6){return function(_u7){return new F(function(){return A(_ss,[_u7,function(_u8){return E(new T(function(){return B(_tI(function(_u9){var _ua=E(_u9);return _ua[0]==2?!B(_lj(_ua[1],_li))?[2]:E(new T(function(){return B(A(_u5,[_u3,function(_ub){return [1,function(_uc){return new F(function(){return A(_ss,[_uc,function(_ud){return E(new T(function(){return B(_tI(function(_ue){var _uf=E(_ue);return _uf[0]==2?!B(_lj(_uf[1],_lg))?[2]:E(new T(function(){return B(A(_u6,[_ub]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_ug=function(_uh,_ui,_uj){var _uk=function(_ul,_um){return new F(function(){return _kM([1,function(_un){return new F(function(){return A(_ss,[_un,function(_uo){return E(new T(function(){return B(_tI(function(_up){var _uq=E(_up);if(_uq[0]==4){var _ur=E(_uq[1]);if(!_ur[0]){return new F(function(){return A(_uh,[_uq,_ul,_um]);});}else{return E(E(_ur[1])[1])==45?E(_ur[2])[0]==0?E([1,function(_us){return new F(function(){return A(_ss,[_us,function(_ut){return E(new T(function(){return B(_tI(function(_uu){return new F(function(){return A(_uh,[_uu,_ul,function(_uv){return new F(function(){return A(_um,[new T(function(){return [0, -E(_uv)[1]];})]);});}]);});}));}));}]);});}]):B(A(_uh,[_uq,_ul,_um])):B(A(_uh,[_uq,_ul,_um]));}}else{return new F(function(){return A(_uh,[_uq,_ul,_um]);});}}));}));}]);});}],new T(function(){return [1,B(_u4(_uk,_um))];}));});};return new F(function(){return _uk(_ui,_uj);});},_uw=function(_ux,_uy){return [2];},_uz=function(_uA){var _uB=E(_uA);return _uB[0]==0?[1,new T(function(){return B(_nd(new T(function(){return B(_n3(E(_uB[1])[1]));}),_n2,_uB[2]));})]:E(_uB[2])[0]==0?E(_uB[3])[0]==0?[1,new T(function(){return B(_nd(_n1,_n2,_uB[1]));})]:[0]:[0];},_uC=function(_uD){var _uE=E(_uD);if(_uE[0]==5){var _uF=B(_uz(_uE[1]));return _uF[0]==0?E(_uw):function(_uG,_uH){return new F(function(){return A(_uH,[new T(function(){return [0,B(_oc(_uF[1]))];})]);});};}else{return E(_uw);}},_uI=function(_uJ){return [1,function(_uK){return new F(function(){return A(_ss,[_uK,function(_uL){return E([3,_uJ,_lz]);}]);});}];},_uM=new T(function(){return B(_ug(_uC,_u3,_uI));}),_uN=function(_uO){while(1){var _uP=(function(_uQ){var _uR=E(_uQ);if(!_uR[0]){return [0];}else{var _uS=_uR[2],_uT=E(_uR[1]);if(!E(_uT[2])[0]){return [1,_uT[1],new T(function(){return B(_uN(_uS));})];}else{_uO=_uS;return null;}}})(_uO);if(_uP!=null){return _uP;}}},_uU=function(_uV){var _uW=B(_uN(B(_kC(_uM,_uV))));return _uW[0]==0?E(_ky):E(_uW[2])[0]==0?E(_uW[1]):E(_kA);},_uX=function(_uY,_uZ,_v0,_v1,_v2){var _v3=function(_v4,_v5,_v6){var _v7=function(_v8,_v9,_va){return new F(function(){return A(_v6,[[0,_uY,new T(function(){return B(_7X(_uU,_v8));})],_v9,new T(function(){var _vb=E(E(_v9)[2]),_vc=E(_va),_vd=E(_vc[1]),_ve=B(_cW(_vd[1],_vd[2],_vd[3],_vc[2],_vb[1],_vb[2],_vb[3],_9));return [0,E(_ve[1]),_ve[2]];})]);});},_vf=function(_vg){return new F(function(){return _v7(_9,_v4,new T(function(){var _vh=E(E(_v4)[2]),_vi=E(_vg),_vj=E(_vi[1]),_vk=B(_cW(_vj[1],_vj[2],_vj[3],_vi[2],_vh[1],_vh[2],_vh[3],_9));return [0,E(_vk[1]),_vk[2]];},1));});};return new F(function(){return _eW(_k5,_kw,_v4,function(_vl,_vm,_vn){return new F(function(){return A(_v5,[[0,_uY,new T(function(){return B(_7X(_uU,_vl));})],_vm,new T(function(){var _vo=E(E(_vm)[2]),_vp=E(_vn),_vq=E(_vp[1]),_vr=B(_cW(_vq[1],_vq[2],_vq[3],_vp[2],_vo[1],_vo[2],_vo[3],_9));return [0,E(_vr[1]),_vr[2]];})]);});},_vf,_v7,_vf);});};return new F(function(){return _ew(_iS,_uZ,function(_vs,_vt,_vu){return new F(function(){return _v3(_vt,_v0,function(_vv,_vw,_vx){return new F(function(){return A(_v0,[_vv,_vw,new T(function(){return B(_dL(_vu,_vx));})]);});});});},_v1,function(_vy,_vz,_vA){return new F(function(){return _v3(_vz,_v0,function(_vB,_vC,_vD){return new F(function(){return A(_v2,[_vB,_vC,new T(function(){return B(_dL(_vA,_vD));})]);});});});});});},_vE=new T(function(){return B(unCStr("letter or digit"));}),_vF=[1,_vE,_9],_vG=function(_vH){var _vI=u_iswalnum(E(_vH)[1]),_vJ=_vI;return E(_vJ)==0?false:true;},_vK=function(_vL,_vM,_vN,_vO,_vP){var _vQ=E(_vL),_vR=E(_vQ[2]);return new F(function(){return _i6(_g7,_jM,_vG,_vQ[1],_vR[1],_vR[2],_vR[3],_vQ[3],_vM,_vP);});},_vS=function(_vT,_vU,_vV,_vW,_vX){return new F(function(){return _jt(_vK,_vF,_vT,_vU,_vV,_vW,_vX);});},_vY=function(_vZ,_w0,_w1,_w2,_w3){return new F(function(){return _dT(_vS,_vZ,function(_w4,_w5,_w6){return new F(function(){return _uX(_w4,_w5,_w0,_w1,function(_w7,_w8,_w9){return new F(function(){return A(_w0,[_w7,_w8,new T(function(){return B(_dL(_w6,_w9));})]);});});});},_w3,function(_wa,_wb,_wc){return new F(function(){return _uX(_wa,_wb,_w0,_w1,function(_wd,_we,_wf){return new F(function(){return A(_w2,[_wd,_we,new T(function(){return B(_dL(_wc,_wf));})]);});});});},_w3);});},_wg=new T(function(){return B(unCStr("SHOW"));}),_wh=[0,_wg,_9],_wi=function(_wj,_wk,_wl,_wm){var _wn=function(_wo){return new F(function(){return A(_wm,[[0,_wj,_wh],_wk,new T(function(){var _wp=E(E(_wk)[2]),_wq=_wp[1],_wr=_wp[2],_ws=_wp[3],_wt=E(_wo),_wu=E(_wt[1]),_wv=B(_cW(_wu[1],_wu[2],_wu[3],_wt[2],_wq,_wr,_ws,_9)),_ww=E(_wv[1]),_wx=B(_cW(_ww[1],_ww[2],_ww[3],_wv[2],_wq,_wr,_ws,_9));return [0,E(_wx[1]),_wx[2]];})]);});};return new F(function(){return _vY(_wk,function(_wy,_wz,_wA){return new F(function(){return A(_wl,[[0,_wj,_wy],_wz,new T(function(){var _wB=E(E(_wz)[2]),_wC=E(_wA),_wD=E(_wC[1]),_wE=B(_cW(_wD[1],_wD[2],_wD[3],_wC[2],_wB[1],_wB[2],_wB[3],_9));return [0,E(_wE[1]),_wE[2]];})]);});},_wn,function(_wF,_wG,_wH){return new F(function(){return A(_wm,[[0,_wj,_wF],_wG,new T(function(){var _wI=E(E(_wG)[2]),_wJ=E(_wH),_wK=E(_wJ[1]),_wL=B(_cW(_wK[1],_wK[2],_wK[3],_wJ[2],_wI[1],_wI[2],_wI[3],_9));return [0,E(_wL[1]),_wL[2]];})]);});},_wn);});},_wM=new T(function(){return B(unCStr("sS"));}),_wN=new T(function(){return B(_kb(_iJ));}),_wO=[0,58],_wP=new T(function(){return B(_ke(_wN,_wO));}),_wQ=[1,_vE,_9],_wR=function(_wS,_wT,_wU,_wV,_wW,_wX,_wY,_wZ,_x0){var _x1=function(_x2,_x3){var _x4=new T(function(){var _x5=B(_j8(_x2,_x3,_wQ));return [0,E(_x5[1]),_x5[2]];});return new F(function(){return A(_wP,[[0,_wS,E([0,_wT,_wU,_wV]),E(_wW)],_wX,_wY,function(_x6,_x7,_x8){return new F(function(){return A(_wZ,[_x6,_x7,new T(function(){return B(_dL(_x4,_x8));})]);});},function(_x9){return new F(function(){return A(_x0,[new T(function(){return B(_dL(_x4,_x9));})]);});}]);});},_xa=E(_wS);if(!_xa[0]){return new F(function(){return _x1([0,_wT,_wU,_wV],_gd);});}else{var _xb=_xa[2],_xc=E(_xa[1]),_xd=_xc[1],_xe=u_iswalnum(_xd),_xf=_xe;if(!E(_xf)){return new F(function(){return _x1([0,_wT,_wU,_wV],[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_xc,_9],_gb));})])],_9]);});}else{switch(E(_xd)){case 9:var _xg=[0,_wT,_wU,(_wV+8|0)-B(_ge(_wV-1|0,8))|0];break;case 10:var _xg=[0,_wT,_wU+1|0,1];break;default:var _xg=[0,_wT,_wU,_wV+1|0];}var _xh=_xg,_xi=[0,E(_xh),_9],_xj=[0,_xb,E(_xh),E(_wW)];return new F(function(){return A(_wX,[_xc,_xj,_xi]);});}}},_xk=function(_xl,_xm,_xn,_xo,_xp){var _xq=E(_xl),_xr=E(_xq[2]);return new F(function(){return _wR(_xq[1],_xr[1],_xr[2],_xr[3],_xq[3],_xm,_xn,_xo,_xp);});},_xs=[0,10],_xt=new T(function(){return B(unCStr("lf new-line"));}),_xu=[1,_xt,_9],_xv=function(_xw){return function(_xx,_xy,_xz,_xA,_xB){return new F(function(){return _jt(new T(function(){return B(_ke(_xw,_xs));}),_xu,_xx,_xy,_xz,_xA,_xB);});};},_xC=new T(function(){return B(_xv(_wN));}),_xD=function(_xE,_xF,_xG,_xH,_xI,_xJ,_xK){var _xL=function(_xM,_xN,_xO,_xP,_xQ,_xR){return new F(function(){return _xS(_xN,function(_xT,_xU,_xV){return new F(function(){return A(_xO,[[1,_xM,_xT],_xU,new T(function(){var _xW=E(E(_xU)[2]),_xX=E(_xV),_xY=E(_xX[1]),_xZ=B(_cW(_xY[1],_xY[2],_xY[3],_xX[2],_xW[1],_xW[2],_xW[3],_9));return [0,E(_xZ[1]),_xZ[2]];})]);});},_xP,function(_y0,_y1,_y2){return new F(function(){return A(_xQ,[[1,_xM,_y0],_y1,new T(function(){var _y3=E(E(_y1)[2]),_y4=E(_y2),_y5=E(_y4[1]),_y6=B(_cW(_y5[1],_y5[2],_y5[3],_y4[2],_y3[1],_y3[2],_y3[3],_9));return [0,E(_y6[1]),_y6[2]];})]);});},_xR);});},_xS=function(_y7,_y8,_y9,_ya,_yb){return new F(function(){return A(_xF,[_y7,function(_yc,_yd,_ye){return new F(function(){return A(_y8,[_9,_yd,new T(function(){var _yf=E(E(_yd)[2]),_yg=E(_ye),_yh=E(_yg[1]),_yi=B(_cW(_yh[1],_yh[2],_yh[3],_yg[2],_yf[1],_yf[2],_yf[3],_9));return [0,E(_yi[1]),_yi[2]];})]);});},_y9,function(_yj,_yk,_yl){return new F(function(){return A(_ya,[_9,_yk,new T(function(){var _ym=E(E(_yk)[2]),_yn=E(_yl),_yo=E(_yn[1]),_yp=B(_cW(_yo[1],_yo[2],_yo[3],_yn[2],_ym[1],_ym[2],_ym[3],_9));return [0,E(_yp[1]),_yp[2]];})]);});},function(_yq){return new F(function(){return A(_xE,[_y7,function(_yr,_ys,_yt){return new F(function(){return _xL(_yr,_ys,_y8,_y9,function(_yu,_yv,_yw){return new F(function(){return A(_y8,[_yu,_yv,new T(function(){return B(_dL(_yt,_yw));})]);});},function(_yx){return new F(function(){return A(_y9,[new T(function(){return B(_dL(_yt,_yx));})]);});});});},_y9,function(_yy,_yz,_yA){return new F(function(){return _xL(_yy,_yz,_y8,_y9,function(_yB,_yC,_yD){return new F(function(){return A(_ya,[_yB,_yC,new T(function(){var _yE=E(_yq),_yF=E(_yE[1]),_yG=E(_yA),_yH=E(_yG[1]),_yI=E(_yD),_yJ=E(_yI[1]),_yK=B(_cW(_yH[1],_yH[2],_yH[3],_yG[2],_yJ[1],_yJ[2],_yJ[3],_yI[2])),_yL=E(_yK[1]),_yM=B(_cW(_yF[1],_yF[2],_yF[3],_yE[2],_yL[1],_yL[2],_yL[3],_yK[2]));return [0,E(_yM[1]),_yM[2]];})]);});},function(_yN){return new F(function(){return A(_yb,[new T(function(){var _yO=E(_yq),_yP=E(_yO[1]),_yQ=E(_yA),_yR=E(_yQ[1]),_yS=E(_yN),_yT=E(_yS[1]),_yU=B(_cW(_yR[1],_yR[2],_yR[3],_yQ[2],_yT[1],_yT[2],_yT[3],_yS[2])),_yV=E(_yU[1]),_yW=B(_cW(_yP[1],_yP[2],_yP[3],_yO[2],_yV[1],_yV[2],_yV[3],_yU[2]));return [0,E(_yW[1]),_yW[2]];})]);});});});},function(_yX){return new F(function(){return A(_yb,[new T(function(){return B(_dL(_yq,_yX));})]);});}]);});}]);});};return new F(function(){return _xS(_xG,_xH,_xI,_xJ,_xK);});},_yY=new T(function(){return B(unCStr("tab"));}),_yZ=[1,_yY,_9],_z0=[0,9],_z1=function(_z2){return function(_z3,_z4,_z5,_z6,_z7){return new F(function(){return _jt(new T(function(){return B(_ke(_z2,_z0));}),_yZ,_z3,_z4,_z5,_z6,_z7);});};},_z8=new T(function(){return B(_z1(_wN));}),_z9=[0,39],_za=[1,_z9,_9],_zb=new T(function(){return B(unCStr("\'\\\'\'"));}),_zc=function(_zd){var _ze=E(E(_zd)[1]);return _ze==39?E(_zb):[1,_z9,new T(function(){return B(_hJ(_ze,_za));})];},_zf=function(_zg,_zh){return [1,_ga,new T(function(){return B(_i0(_zg,[1,_ga,_zh]));})];},_zi=function(_zj){return new F(function(){return _e(_zb,_zj);});},_zk=function(_zl,_zm){var _zn=E(E(_zm)[1]);return _zn==39?E(_zi):function(_zo){return [1,_z9,new T(function(){return B(_hJ(_zn,[1,_z9,_zo]));})];};},_zp=[0,_zk,_zc,_zf],_zq=function(_zr,_zs,_zt,_zu,_zv){var _zw=new T(function(){return B(_bm(_zr));}),_zx=function(_zy){return new F(function(){return A(_zu,[_5c,_zt,new T(function(){var _zz=E(E(_zt)[2]),_zA=E(_zy),_zB=E(_zA[1]),_zC=B(_cW(_zB[1],_zB[2],_zB[3],_zA[2],_zz[1],_zz[2],_zz[3],_9));return [0,E(_zC[1]),_zC[2]];})]);});};return new F(function(){return A(_zs,[_zt,function(_zD,_zE,_zF){return new F(function(){return A(_zv,[new T(function(){var _zG=E(E(_zE)[2]),_zH=E(_zF),_zI=E(_zH[1]),_zJ=B(_cW(_zI[1],_zI[2],_zI[3],_zH[2],_zG[1],_zG[2],_zG[3],[1,new T(function(){return [1,E(B(A(_zw,[_zD])))];}),_9]));return [0,E(_zJ[1]),_zJ[2]];})]);});},_zx,function(_zK,_zL,_zM){return new F(function(){return A(_zu,[_5c,_zt,new T(function(){var _zN=E(E(_zt)[2]),_zO=E(E(_zL)[2]),_zP=E(_zM),_zQ=E(_zP[1]),_zR=B(_cW(_zQ[1],_zQ[2],_zQ[3],_zP[2],_zO[1],_zO[2],_zO[3],[1,new T(function(){return [1,E(B(A(_zw,[_zK])))];}),_9])),_zS=E(_zR[1]),_zT=B(_cW(_zS[1],_zS[2],_zS[3],_zR[2],_zN[1],_zN[2],_zN[3],_9));return [0,E(_zT[1]),_zT[2]];})]);});},_zx]);});},_zU=function(_zV,_zW,_zX){return new F(function(){return _zq(_zp,_z8,_zV,function(_zY,_zZ,_A0){return new F(function(){return A(_zW,[_5c,_zZ,new T(function(){var _A1=E(E(_zZ)[2]),_A2=E(_A0),_A3=E(_A2[1]),_A4=B(_cW(_A3[1],_A3[2],_A3[3],_A2[2],_A1[1],_A1[2],_A1[3],_9));return [0,E(_A4[1]),_A4[2]];})]);});},_zX);});},_A5=function(_A6,_A7,_A8,_A9,_Aa){return new F(function(){return A(_xC,[_A6,function(_Ab,_Ac,_Ad){return new F(function(){return _zU(_Ac,function(_Ae,_Af,_Ag){return new F(function(){return A(_A7,[_Ae,_Af,new T(function(){return B(_dL(_Ad,_Ag));})]);});},function(_Ah){return new F(function(){return A(_A8,[new T(function(){return B(_dL(_Ad,_Ah));})]);});});});},_A8,function(_Ai,_Aj,_Ak){return new F(function(){return _zU(_Aj,function(_Al,_Am,_An){return new F(function(){return A(_A9,[_Al,_Am,new T(function(){return B(_dL(_Ak,_An));})]);});},function(_Ao){return new F(function(){return A(_Aa,[new T(function(){return B(_dL(_Ak,_Ao));})]);});});});},_Aa]);});},_Ap=[0,E(_9)],_Aq=[1,_Ap,_9],_Ar=function(_As,_At,_Au,_Av,_Aw,_Ax,_Ay){return new F(function(){return A(_As,[new T(function(){return B(A(_At,[_Au]));}),function(_Az){var _AA=E(_Az);if(!_AA[0]){return E(new T(function(){return B(A(_Ay,[[0,E(_Av),_Aq]]));}));}else{var _AB=E(_AA[1]);return new F(function(){return A(_Ax,[_AB[1],[0,_AB[2],E(_Av),E(_Aw)],[0,E(_Av),_9]]);});}}]);});},_AC=new T(function(){return B(unCStr("end of input"));}),_AD=[1,_AC,_9],_AE=function(_AF,_AG,_AH,_AI,_AJ,_AK,_AL,_AM){return new F(function(){return _jt(function(_AN,_AO,_AP,_AQ,_AR){return new F(function(){return _zq(_AH,function(_AS,_AT,_AU,_AV,_AW){var _AX=E(_AS);return new F(function(){return _Ar(_AF,_AG,_AX[1],_AX[2],_AX[3],_AT,_AW);});},_AN,_AQ,_AR);});},_AD,_AI,_AJ,_AK,_AL,_AM);});},_AY=function(_AZ,_B0,_B1,_B2,_B3){return new F(function(){return _dj(_xC,_AZ,function(_B4,_B5,_B6){return new F(function(){return _AE(_g7,_iQ,_zp,_B5,_B0,_B1,function(_B7,_B8,_B9){return new F(function(){return A(_B0,[_B7,_B8,new T(function(){return B(_dL(_B6,_B9));})]);});},function(_Ba){return new F(function(){return A(_B1,[new T(function(){return B(_dL(_B6,_Ba));})]);});});});},_B1,function(_Bb,_Bc,_Bd){return new F(function(){return _AE(_g7,_iQ,_zp,_Bc,_B0,_B1,function(_Be,_Bf,_Bg){return new F(function(){return A(_B2,[_Be,_Bf,new T(function(){return B(_dL(_Bd,_Bg));})]);});},function(_Bh){return new F(function(){return A(_B3,[new T(function(){return B(_dL(_Bd,_Bh));})]);});});});});});},_Bi=function(_Bj,_Bk,_Bl,_Bm){var _Bn=function(_Bo){var _Bp=function(_Bq){return new F(function(){return A(_Bm,[new T(function(){return B(_dL(_Bo,_Bq));})]);});};return new F(function(){return _A5(_Bj,_Bk,_Bp,function(_Br,_Bs,_Bt){return new F(function(){return A(_Bl,[_Br,_Bs,new T(function(){return B(_dL(_Bo,_Bt));})]);});},_Bp);});};return new F(function(){return _AY(_Bj,_Bk,_Bn,_Bl,_Bn);});},_Bu=function(_Bv,_Bw,_Bx,_By,_Bz){return new F(function(){return _Bi(_Bv,_Bw,_By,_Bz);});},_BA=function(_BB){return true;},_BC=function(_BD,_BE,_BF,_BG,_BH){var _BI=E(_BD),_BJ=E(_BI[2]);return new F(function(){return _i6(_g7,_iQ,_BA,_BI[1],_BJ[1],_BJ[2],_BJ[3],_BI[3],_BE,_BH);});},_BK=function(_BL,_BM,_BN,_BO,_BP){return new F(function(){return A(_z8,[_BL,function(_BQ,_BR,_BS){return new F(function(){return _xD(_BC,_Bu,_BR,_BM,_BN,function(_BT,_BU,_BV){return new F(function(){return A(_BM,[_BT,_BU,new T(function(){return B(_dL(_BS,_BV));})]);});},function(_BW){return new F(function(){return A(_BN,[new T(function(){return B(_dL(_BS,_BW));})]);});});});},_BN,function(_BX,_BY,_BZ){return new F(function(){return _xD(_BC,_Bu,_BY,_BM,_BN,function(_C0,_C1,_C2){return new F(function(){return A(_BO,[_C0,_C1,new T(function(){return B(_dL(_BZ,_C2));})]);});},function(_C3){return new F(function(){return A(_BP,[new T(function(){return B(_dL(_BZ,_C3));})]);});});});},_BP]);});},_C4=[0,_wg,_9],_C5=[0,_9,1,1],_C6=function(_C7){return E(_C7);},_C8=function(_C9){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_C9));}))));});},_Ca=new T(function(){return B(_C8("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_Cb=new T(function(){return B(_C8("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_Cc=[0,_g7,_Cb,_C6,_Ca],_Cd=function(_Ce){return new F(function(){return unAppCStr("string error",new T(function(){return B(_9W(_Ce));}));});},_Cf=function(_Cg,_Ch,_Ci,_Cj,_Ck){return new F(function(){return A(_z8,[_Ch,function(_Cl,_Cm,_Cn){return new F(function(){return A(_Ci,[_Cg,_Cm,new T(function(){var _Co=E(E(_Cm)[2]),_Cp=E(_Cn),_Cq=E(_Cp[1]),_Cr=B(_cW(_Cq[1],_Cq[2],_Cq[3],_Cp[2],_Co[1],_Co[2],_Co[3],_9));return [0,E(_Cr[1]),_Cr[2]];})]);});},_Ck,function(_Cs,_Ct,_Cu){return new F(function(){return A(_Cj,[_Cg,_Ct,new T(function(){var _Cv=E(E(_Ct)[2]),_Cw=E(_Cu),_Cx=E(_Cw[1]),_Cy=B(_cW(_Cx[1],_Cx[2],_Cx[3],_Cw[2],_Cv[1],_Cv[2],_Cv[3],_9));return [0,E(_Cy[1]),_Cy[2]];})]);});},_Ck]);});},_Cz=function(_CA,_CB,_CC,_CD,_CE){return new F(function(){return A(_xC,[_CA,function(_CF,_CG,_CH){return new F(function(){return _Cf(_CF,_CG,_CB,function(_CI,_CJ,_CK){return new F(function(){return A(_CB,[_CI,_CJ,new T(function(){return B(_dL(_CH,_CK));})]);});},function(_CL){return new F(function(){return A(_CC,[new T(function(){return B(_dL(_CH,_CL));})]);});});});},_CC,function(_CM,_CN,_CO){return new F(function(){return _Cf(_CM,_CN,_CB,function(_CP,_CQ,_CR){return new F(function(){return A(_CD,[_CP,_CQ,new T(function(){return B(_dL(_CO,_CR));})]);});},function(_CS){return new F(function(){return A(_CE,[new T(function(){return B(_dL(_CO,_CS));})]);});});});},_CE]);});},_CT=function(_CU,_CV,_CW,_CX,_CY){return new F(function(){return _Cz(_CU,_CV,_CW,_CX,function(_CZ){var _D0=E(_CU),_D1=E(_D0[2]),_D2=E(_D0[1]);return _D2[0]==0?B(A(_CY,[new T(function(){var _D3=E(_CZ),_D4=E(_D3[1]),_D5=B(_cW(_D4[1],_D4[2],_D4[3],_D3[2],_D1[1],_D1[2],_D1[3],_Aq));return [0,E(_D5[1]),_D5[2]];})])):B(A(_CV,[_D2[1],[0,_D2[2],E(_D1),E(_D0[3])],[0,E(_D1),_9]]));});});},_D6=function(_D7,_D8,_D9,_Da,_Db){return new F(function(){return _dj(_CT,_D7,_D8,_D9,_Da);});},_Dc=function(_Dd,_De,_Df){return [0,_Dd,E(E(_De)),_Df];},_Dg=function(_Dh,_Di,_Dj){var _Dk=new T(function(){return B(_iK(_Dh));}),_Dl=new T(function(){return B(_iK(_Dh));});return new F(function(){return A(_Di,[_Dj,function(_Dm,_Dn,_Do){return new F(function(){return A(_Dk,[[0,new T(function(){return B(A(_Dl,[new T(function(){return B(_Dc(_Dm,_Dn,_Do));})]));})]]);});},function(_Dp){return new F(function(){return A(_Dk,[[0,new T(function(){return B(A(_Dl,[[1,_Dp]]));})]]);});},function(_Dq,_Dr,_Ds){return new F(function(){return A(_Dk,[new T(function(){return [1,E(B(A(_Dl,[new T(function(){return B(_Dc(_Dq,_Dr,_Ds));})])))];})]);});},function(_Dt){return new F(function(){return A(_Dk,[new T(function(){return [1,E(B(A(_Dl,[[1,_Dt]])))];})]);});}]);});},_Du=function(_Dv){return function(_Dw,_Dx,_Dy,_Dz,_DA){return new F(function(){return A(_Dz,[new T(function(){var _DB=B(_Dg(_Cc,_DC,[0,new T(function(){var _DD=B(_Dg(_Cc,_D6,[0,_Dv,E(_C5),E(_5c)]));if(!_DD[0]){var _DE=E(_DD[1]),_DF=_DE[0]==0?E(_DE[1]):B(_Cd(_DE[1]));}else{var _DG=E(_DD[1]),_DF=_DG[0]==0?E(_DG[1]):B(_Cd(_DG[1]));}return _DF;}),E(_C5),E(_5c)]));if(!_DB[0]){var _DH=E(_DB[1]),_DI=_DH[0]==0?E(_DH[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_DH[1]));})));})],_9],_9],_C4];}else{var _DJ=E(_DB[1]),_DI=_DJ[0]==0?E(_DJ[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_DJ[1]));})));})],_9],_9],_C4];}return _DI;}),_Dw,new T(function(){return [0,E(E(_Dw)[2]),_9];})]);});};},_DK=function(_DL,_DM,_DN,_DO,_DP){return new F(function(){return _BK(_DL,function(_DQ,_DR,_DS){return new F(function(){return A(_Du,[_DQ,_DR,_DM,_DN,function(_DT,_DU,_DV){return new F(function(){return A(_DM,[_DT,_DU,new T(function(){return B(_dL(_DS,_DV));})]);});},function(_DW){return new F(function(){return A(_DN,[new T(function(){return B(_dL(_DS,_DW));})]);});}]);});},_DN,function(_DX,_DY,_DZ){return new F(function(){return A(_Du,[_DX,_DY,_DM,_DN,function(_E0,_E1,_E2){return new F(function(){return A(_DO,[_E0,_E1,new T(function(){return B(_dL(_DZ,_E2));})]);});},function(_E3){return new F(function(){return A(_DP,[new T(function(){return B(_dL(_DZ,_E3));})]);});}]);});},_DP);});},_E4=function(_E5,_E6,_E7,_E8,_E9,_Ea){var _Eb=function(_Ec,_Ed,_Ee,_Ef,_Eg){var _Eh=function(_Ei,_Ej,_Ek,_El,_Em){return new F(function(){return A(_Ef,[[0,[1,[0,_E5,_Ej,_Ek]],_Ei],_El,new T(function(){var _En=E(_Em),_Eo=E(_En[1]),_Ep=E(E(_El)[2]),_Eq=B(_cW(_Eo[1],_Eo[2],_Eo[3],_En[2],_Ep[1],_Ep[2],_Ep[3],_9));return [0,E(_Eq[1]),_Eq[2]];})]);});},_Er=function(_Es){return new F(function(){return _Eh(_9,_wg,_9,_Ec,new T(function(){var _Et=E(E(_Ec)[2]),_Eu=E(_Es),_Ev=E(_Eu[1]),_Ew=B(_cW(_Ev[1],_Ev[2],_Ev[3],_Eu[2],_Et[1],_Et[2],_Et[3],_9));return [0,E(_Ew[1]),_Ew[2]];}));});};return new F(function(){return _DK(_Ec,function(_Ex,_Ey,_Ez){var _EA=E(_Ex),_EB=E(_EA[2]);return new F(function(){return A(_Ed,[[0,[1,[0,_E5,_EB[1],_EB[2]]],_EA[1]],_Ey,new T(function(){var _EC=E(_Ez),_ED=E(_EC[1]),_EE=E(E(_Ey)[2]),_EF=B(_cW(_ED[1],_ED[2],_ED[3],_EC[2],_EE[1],_EE[2],_EE[3],_9));return [0,E(_EF[1]),_EF[2]];})]);});},_Er,function(_EG,_EH,_EI){var _EJ=E(_EG),_EK=E(_EJ[2]);return new F(function(){return _Eh(_EJ[1],_EK[1],_EK[2],_EH,_EI);});},_Er);});};return new F(function(){return A(_xC,[_E6,function(_EL,_EM,_EN){return new F(function(){return _Eb(_EM,_E7,_E8,function(_EO,_EP,_EQ){return new F(function(){return A(_E7,[_EO,_EP,new T(function(){return B(_dL(_EN,_EQ));})]);});},function(_ER){return new F(function(){return A(_E8,[new T(function(){return B(_dL(_EN,_ER));})]);});});});},_E8,function(_ES,_ET,_EU){return new F(function(){return _Eb(_ET,_E7,_E8,function(_EV,_EW,_EX){return new F(function(){return A(_E9,[_EV,_EW,new T(function(){return B(_dL(_EU,_EX));})]);});},function(_EY){return new F(function(){return A(_Ea,[new T(function(){return B(_dL(_EU,_EY));})]);});});});},_Ea]);});},_EZ=new T(function(){return B(unCStr(" associative operator"));}),_F0=function(_F1,_F2){var _F3=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_F1,_EZ));}))))];}),_9];return function(_F4,_F5,_F6,_F7,_F8){return new F(function(){return A(_F2,[_F4,function(_F9,_Fa,_Fb){return new F(function(){return A(_F8,[new T(function(){var _Fc=E(E(_Fa)[2]),_Fd=E(_Fb),_Fe=E(_Fd[1]),_Ff=B(_cW(_Fe[1],_Fe[2],_Fe[3],_Fd[2],_Fc[1],_Fc[2],_Fc[3],_F3));return [0,E(_Ff[1]),_Ff[2]];})]);});},_F8,function(_Fg,_Fh,_Fi){return new F(function(){return A(_F8,[new T(function(){var _Fj=E(E(_Fh)[2]),_Fk=E(_Fi),_Fl=E(_Fk[1]),_Fm=B(_cW(_Fl[1],_Fl[2],_Fl[3],_Fk[2],_Fj[1],_Fj[2],_Fj[3],_F3));return [0,E(_Fm[1]),_Fm[2]];})]);});},_F8]);});};},_Fn=function(_Fo,_Fp,_Fq,_Fr,_Fs,_Ft){var _Fu=E(_Fo);if(!_Fu[0]){return new F(function(){return A(_Ft,[new T(function(){return [0,E(E(_Fp)[2]),_9];})]);});}else{return new F(function(){return A(_Fu[1],[_Fp,_Fq,_Fr,_Fs,function(_Fv){return new F(function(){return _Fn(_Fu[2],_Fp,_Fq,_Fr,function(_Fw,_Fx,_Fy){return new F(function(){return A(_Fs,[_Fw,_Fx,new T(function(){return B(_dL(_Fv,_Fy));})]);});},function(_Fz){return new F(function(){return A(_Ft,[new T(function(){return B(_dL(_Fv,_Fz));})]);});});});}]);});}},_FA=new T(function(){return B(unCStr("right"));}),_FB=new T(function(){return B(unCStr("left"));}),_FC=new T(function(){return B(unCStr("non"));}),_FD=new T(function(){return B(unCStr("operator"));}),_FE=[1,_FD,_9],_FF=[1,_9,_9],_FG=function(_FH){var _FI=E(_FH);if(!_FI[0]){return [0,_9,_9,_9,_9,_9];}else{var _FJ=_FI[2],_FK=E(_FI[1]);switch(_FK[0]){case 0:var _FL=_FK[1],_FM=B(_FG(_FJ)),_FN=_FM[1],_FO=_FM[2],_FP=_FM[3],_FQ=_FM[4],_FR=_FM[5];switch(E(_FK[2])){case 0:return [0,_FN,_FO,[1,_FL,_FP],_FQ,_FR];case 1:return [0,_FN,[1,_FL,_FO],_FP,_FQ,_FR];default:return [0,[1,_FL,_FN],_FO,_FP,_FQ,_FR];}break;case 1:var _FS=B(_FG(_FJ));return [0,_FS[1],_FS[2],_FS[3],[1,_FK[1],_FS[4]],_FS[5]];default:var _FT=B(_FG(_FJ));return [0,_FT[1],_FT[2],_FT[3],_FT[4],[1,_FK[1],_FT[5]]];}}},_FU=function(_FV,_FW){while(1){var _FX=(function(_FY,_FZ){var _G0=E(_FZ);if(!_G0[0]){return E(_FY);}else{var _G1=new T(function(){var _G2=B(_FG(_G0[1]));return [0,_G2[1],_G2[2],_G2[3],_G2[4],_G2[5]];}),_G3=new T(function(){return E(E(_G1)[2]);}),_G4=new T(function(){return B(_F0(_FB,function(_G5,_G6,_G7,_G8,_G9){return new F(function(){return _Fn(_G3,_G5,_G6,_G7,_G8,_G9);});}));}),_Ga=new T(function(){return E(E(_G1)[1]);}),_Gb=new T(function(){return E(E(_G1)[3]);}),_Gc=new T(function(){return B(_F0(_FC,function(_Gd,_Ge,_Gf,_Gg,_Gh){return new F(function(){return _Fn(_Gb,_Gd,_Ge,_Gf,_Gg,_Gh);});}));}),_Gi=function(_Gj,_Gk,_Gl,_Gm,_Gn,_Go){var _Gp=function(_Gq,_Gr,_Gs,_Gt,_Gu){var _Gv=new T(function(){return B(A(_Gj,[_Gq]));});return new F(function(){return _Fn(new T(function(){return E(E(_G1)[5]);}),_Gr,function(_Gw,_Gx,_Gy){return new F(function(){return A(_Gs,[new T(function(){return B(A(_Gw,[_Gv]));}),_Gx,new T(function(){var _Gz=E(E(_Gx)[2]),_GA=E(_Gy),_GB=E(_GA[1]),_GC=B(_cW(_GB[1],_GB[2],_GB[3],_GA[2],_Gz[1],_Gz[2],_Gz[3],_9));return [0,E(_GC[1]),_GC[2]];})]);});},_Gt,function(_GD,_GE,_GF){return new F(function(){return A(_Gu,[new T(function(){return B(A(_GD,[_Gv]));}),_GE,new T(function(){var _GG=E(E(_GE)[2]),_GH=_GG[1],_GI=_GG[2],_GJ=_GG[3],_GK=E(_GF),_GL=E(_GK[1]),_GM=_GL[2],_GN=_GL[3],_GO=E(_GK[2]);if(!_GO[0]){switch(B(_cO(_GL[1],_GH))){case 0:var _GP=[0,E(_GG),_9];break;case 1:if(_GM>=_GI){if(_GM!=_GI){var _GQ=[0,E(_GL),_9];}else{if(_GN>=_GJ){var _GR=_GN!=_GJ?[0,E(_GL),_9]:[0,E(_GL),_cV];}else{var _GR=[0,E(_GG),_9];}var _GS=_GR,_GQ=_GS;}var _GT=_GQ,_GU=_GT;}else{var _GU=[0,E(_GG),_9];}var _GV=_GU,_GP=_GV;break;default:var _GP=[0,E(_GL),_9];}var _GW=_GP;}else{var _GX=B(_j8(_GL,_GO,_FF)),_GY=E(_GX[1]),_GZ=B(_cW(_GY[1],_GY[2],_GY[3],_GX[2],_GH,_GI,_GJ,_9)),_GW=[0,E(_GZ[1]),_GZ[2]];}var _H0=_GW,_H1=_H0,_H2=_H1,_H3=_H2;return _H3;})]);});},function(_H4){return new F(function(){return A(_Gu,[_Gv,_Gr,new T(function(){var _H5=E(E(_Gr)[2]),_H6=_H5[1],_H7=_H5[2],_H8=_H5[3],_H9=E(_H4),_Ha=B(_j8(_H9[1],_H9[2],_FF)),_Hb=E(_Ha[1]),_Hc=B(_cW(_Hb[1],_Hb[2],_Hb[3],_Ha[2],_H6,_H7,_H8,_9)),_Hd=E(_Hc[1]),_He=B(_cW(_Hd[1],_Hd[2],_Hd[3],_Hc[2],_H6,_H7,_H8,_9));return [0,E(_He[1]),_He[2]];})]);});});});};return new F(function(){return A(_FY,[_Gk,function(_Hf,_Hg,_Hh){return new F(function(){return _Gp(_Hf,_Hg,_Gl,_Gm,function(_Hi,_Hj,_Hk){return new F(function(){return A(_Gl,[_Hi,_Hj,new T(function(){return B(_dL(_Hh,_Hk));})]);});});});},_Gm,function(_Hl,_Hm,_Hn){return new F(function(){return _Gp(_Hl,_Hm,_Gl,_Gm,function(_Ho,_Hp,_Hq){return new F(function(){return A(_Gn,[_Ho,_Hp,new T(function(){return B(_dL(_Hn,_Hq));})]);});});});},_Go]);});},_Hr=function(_Hs,_Ht,_Hu,_Hv,_Hw){var _Hx=function(_Hy,_Hz,_HA){return new F(function(){return _Gi(_Hy,_Hz,_Ht,_Hu,function(_HB,_HC,_HD){return new F(function(){return A(_Hv,[_HB,_HC,new T(function(){return B(_dL(_HA,_HD));})]);});},function(_HE){return new F(function(){return A(_Hw,[new T(function(){return B(_dL(_HA,_HE));})]);});});});};return new F(function(){return _Fn(new T(function(){return E(E(_G1)[4]);}),_Hs,function(_HF,_HG,_HH){return new F(function(){return _Gi(_HF,_HG,_Ht,_Hu,function(_HI,_HJ,_HK){return new F(function(){return A(_Ht,[_HI,_HJ,new T(function(){return B(_dL(_HH,_HK));})]);});},function(_HL){return new F(function(){return A(_Hu,[new T(function(){return B(_dL(_HH,_HL));})]);});});});},_Hu,function(_HM,_HN,_HO){return new F(function(){return _Hx(_HM,_HN,new T(function(){var _HP=E(_HO),_HQ=E(_HP[2]);if(!_HQ[0]){var _HR=E(_HP);}else{var _HS=B(_j8(_HP[1],_HQ,_FF)),_HR=[0,E(_HS[1]),_HS[2]];}var _HT=_HR;return _HT;}));});},function(_HU){return new F(function(){return _Hx(_5q,_Hs,new T(function(){var _HV=E(E(_Hs)[2]),_HW=E(_HU),_HX=B(_j8(_HW[1],_HW[2],_FF)),_HY=E(_HX[1]),_HZ=B(_cW(_HY[1],_HY[2],_HY[3],_HX[2],_HV[1],_HV[2],_HV[3],_9));return [0,E(_HZ[1]),_HZ[2]];}));});});});},_I0=function(_I1,_I2,_I3,_I4,_I5,_I6){var _I7=function(_I8){return new F(function(){return A(_G4,[_I2,_I3,_I4,function(_I9,_Ia,_Ib){return new F(function(){return A(_I5,[_I9,_Ia,new T(function(){return B(_dL(_I8,_Ib));})]);});},function(_Ic){return new F(function(){return A(_Gc,[_I2,_I3,_I4,function(_Id,_Ie,_If){return new F(function(){return A(_I5,[_Id,_Ie,new T(function(){var _Ig=E(_I8),_Ih=E(_Ig[1]),_Ii=E(_Ic),_Ij=E(_Ii[1]),_Ik=E(_If),_Il=E(_Ik[1]),_Im=B(_cW(_Ij[1],_Ij[2],_Ij[3],_Ii[2],_Il[1],_Il[2],_Il[3],_Ik[2])),_In=E(_Im[1]),_Io=B(_cW(_Ih[1],_Ih[2],_Ih[3],_Ig[2],_In[1],_In[2],_In[3],_Im[2]));return [0,E(_Io[1]),_Io[2]];})]);});},function(_Ip){return new F(function(){return A(_I6,[new T(function(){var _Iq=E(_I8),_Ir=E(_Iq[1]),_Is=E(_Ic),_It=E(_Is[1]),_Iu=E(_Ip),_Iv=E(_Iu[1]),_Iw=B(_cW(_It[1],_It[2],_It[3],_Is[2],_Iv[1],_Iv[2],_Iv[3],_Iu[2])),_Ix=E(_Iw[1]),_Iy=B(_cW(_Ir[1],_Ir[2],_Ir[3],_Iq[2],_Ix[1],_Ix[2],_Ix[3],_Iw[2]));return [0,E(_Iy[1]),_Iy[2]];})]);});}]);});}]);});},_Iz=function(_IA,_IB,_IC,_ID,_IE,_IF){var _IG=function(_IH,_II,_IJ){return new F(function(){return A(_IC,[new T(function(){return B(A(_IA,[_I1,_IH]));}),_II,new T(function(){var _IK=E(E(_II)[2]),_IL=E(_IJ),_IM=E(_IL[1]),_IN=B(_cW(_IM[1],_IM[2],_IM[3],_IL[2],_IK[1],_IK[2],_IK[3],_9));return [0,E(_IN[1]),_IN[2]];})]);});};return new F(function(){return _Hr(_IB,function(_IO,_IP,_IQ){return new F(function(){return _I0(_IO,_IP,_IG,_ID,function(_IR,_IS,_IT){return new F(function(){return _IG(_IR,_IS,new T(function(){var _IU=E(_IQ),_IV=E(_IU[1]),_IW=E(_IT),_IX=E(_IW[1]),_IY=B(_cW(_IV[1],_IV[2],_IV[3],_IU[2],_IX[1],_IX[2],_IX[3],_IW[2]));return [0,E(_IY[1]),_IY[2]];},1));});},function(_IZ){return new F(function(){return _IG(_IO,_IP,new T(function(){var _J0=E(E(_IP)[2]),_J1=E(_IQ),_J2=E(_J1[1]),_J3=E(_IZ),_J4=E(_J3[1]),_J5=B(_cW(_J4[1],_J4[2],_J4[3],_J3[2],_J0[1],_J0[2],_J0[3],_9)),_J6=E(_J5[1]),_J7=B(_cW(_J2[1],_J2[2],_J2[3],_J1[2],_J6[1],_J6[2],_J6[3],_J5[2]));return [0,E(_J7[1]),_J7[2]];},1));});});});},_ID,function(_J8,_J9,_Ja){var _Jb=function(_Jc,_Jd,_Je){return new F(function(){return A(_IE,[new T(function(){return B(A(_IA,[_I1,_Jc]));}),_Jd,new T(function(){var _Jf=E(E(_Jd)[2]),_Jg=E(_Ja),_Jh=E(_Jg[1]),_Ji=E(_Je),_Jj=E(_Ji[1]),_Jk=B(_cW(_Jh[1],_Jh[2],_Jh[3],_Jg[2],_Jj[1],_Jj[2],_Jj[3],_Ji[2])),_Jl=E(_Jk[1]),_Jm=B(_cW(_Jl[1],_Jl[2],_Jl[3],_Jk[2],_Jf[1],_Jf[2],_Jf[3],_9));return [0,E(_Jm[1]),_Jm[2]];})]);});};return new F(function(){return _I0(_J8,_J9,_IG,_ID,_Jb,function(_Jn){return new F(function(){return _Jb(_J8,_J9,new T(function(){var _Jo=E(E(_J9)[2]),_Jp=E(_Jn),_Jq=E(_Jp[1]),_Jr=B(_cW(_Jq[1],_Jq[2],_Jq[3],_Jp[2],_Jo[1],_Jo[2],_Jo[3],_9));return [0,E(_Jr[1]),_Jr[2]];},1));});});});},_IF);});};return new F(function(){return _Fn(_Ga,_I2,function(_Js,_Jt,_Ju){return new F(function(){return _Iz(_Js,_Jt,_I3,_I4,function(_Jv,_Jw,_Jx){return new F(function(){return A(_I3,[_Jv,_Jw,new T(function(){return B(_dL(_Ju,_Jx));})]);});},function(_Jy){return new F(function(){return A(_I4,[new T(function(){return B(_dL(_Ju,_Jy));})]);});});});},_I4,function(_Jz,_JA,_JB){return new F(function(){return _Iz(_Jz,_JA,_I3,_I4,function(_JC,_JD,_JE){return new F(function(){return A(_I5,[_JC,_JD,new T(function(){return B(_dL(_JB,_JE));})]);});},function(_JF){return new F(function(){return _I7(new T(function(){return B(_dL(_JB,_JF));}));});});});},_I7);});},_JG=new T(function(){return B(_F0(_FA,function(_JH,_JI,_JJ,_JK,_JL){return new F(function(){return _Fn(_Ga,_JH,_JI,_JJ,_JK,_JL);});}));}),_JM=function(_JN,_JO,_JP,_JQ,_JR,_JS){var _JT=function(_JU){return new F(function(){return A(_JG,[_JO,_JP,_JQ,function(_JV,_JW,_JX){return new F(function(){return A(_JR,[_JV,_JW,new T(function(){return B(_dL(_JU,_JX));})]);});},function(_JY){return new F(function(){return A(_Gc,[_JO,_JP,_JQ,function(_JZ,_K0,_K1){return new F(function(){return A(_JR,[_JZ,_K0,new T(function(){var _K2=E(_JU),_K3=E(_K2[1]),_K4=E(_JY),_K5=E(_K4[1]),_K6=E(_K1),_K7=E(_K6[1]),_K8=B(_cW(_K5[1],_K5[2],_K5[3],_K4[2],_K7[1],_K7[2],_K7[3],_K6[2])),_K9=E(_K8[1]),_Ka=B(_cW(_K3[1],_K3[2],_K3[3],_K2[2],_K9[1],_K9[2],_K9[3],_K8[2]));return [0,E(_Ka[1]),_Ka[2]];})]);});},function(_Kb){return new F(function(){return A(_JS,[new T(function(){var _Kc=E(_JU),_Kd=E(_Kc[1]),_Ke=E(_JY),_Kf=E(_Ke[1]),_Kg=E(_Kb),_Kh=E(_Kg[1]),_Ki=B(_cW(_Kf[1],_Kf[2],_Kf[3],_Ke[2],_Kh[1],_Kh[2],_Kh[3],_Kg[2])),_Kj=E(_Ki[1]),_Kk=B(_cW(_Kd[1],_Kd[2],_Kd[3],_Kc[2],_Kj[1],_Kj[2],_Kj[3],_Ki[2]));return [0,E(_Kk[1]),_Kk[2]];})]);});}]);});}]);});},_Kl=function(_Km,_Kn,_Ko,_Kp,_Kq,_Kr){var _Ks=function(_Kt){var _Ku=new T(function(){return B(A(_Km,[_JN,_Kt]));});return function(_Kv,_Kw,_Kx,_Ky,_Kz){return new F(function(){return _JM(_Ku,_Kv,_Kw,_Kx,_Ky,function(_KA){return new F(function(){return A(_Ky,[_Ku,_Kv,new T(function(){var _KB=E(E(_Kv)[2]),_KC=E(_KA),_KD=E(_KC[1]),_KE=B(_cW(_KD[1],_KD[2],_KD[3],_KC[2],_KB[1],_KB[2],_KB[3],_9));return [0,E(_KE[1]),_KE[2]];})]);});});});};};return new F(function(){return _Hr(_Kn,function(_KF,_KG,_KH){return new F(function(){return A(_Ks,[_KF,_KG,_Ko,_Kp,function(_KI,_KJ,_KK){return new F(function(){return A(_Ko,[_KI,_KJ,new T(function(){return B(_dL(_KH,_KK));})]);});},function(_KL){return new F(function(){return A(_Kp,[new T(function(){return B(_dL(_KH,_KL));})]);});}]);});},_Kp,function(_KM,_KN,_KO){return new F(function(){return A(_Ks,[_KM,_KN,_Ko,_Kp,function(_KP,_KQ,_KR){return new F(function(){return A(_Kq,[_KP,_KQ,new T(function(){return B(_dL(_KO,_KR));})]);});},function(_KS){return new F(function(){return A(_Kr,[new T(function(){return B(_dL(_KO,_KS));})]);});}]);});},_Kr);});};return new F(function(){return _Fn(_G3,_JO,function(_KT,_KU,_KV){return new F(function(){return _Kl(_KT,_KU,_JP,_JQ,function(_KW,_KX,_KY){return new F(function(){return A(_JP,[_KW,_KX,new T(function(){return B(_dL(_KV,_KY));})]);});},function(_KZ){return new F(function(){return A(_JQ,[new T(function(){return B(_dL(_KV,_KZ));})]);});});});},_JQ,function(_L0,_L1,_L2){return new F(function(){return _Kl(_L0,_L1,_JP,_JQ,function(_L3,_L4,_L5){return new F(function(){return A(_JR,[_L3,_L4,new T(function(){return B(_dL(_L2,_L5));})]);});},function(_L6){return new F(function(){return _JT(new T(function(){return B(_dL(_L2,_L6));}));});});});},_JT);});},_L7=function(_L8,_L9,_La,_Lb,_Lc,_Ld){var _Le=function(_Lf,_Lg,_Lh,_Li,_Lj,_Lk){var _Ll=function(_Lm){return function(_Ln,_Lo,_Lp,_Lq,_Lr){return new F(function(){return A(_JG,[_Ln,_Lo,_Lp,_Lq,function(_Ls){return new F(function(){return A(_G4,[_Ln,_Lo,_Lp,function(_Lt,_Lu,_Lv){return new F(function(){return A(_Lq,[_Lt,_Lu,new T(function(){return B(_dL(_Ls,_Lv));})]);});},function(_Lw){return new F(function(){return A(_Gc,[_Ln,_Lo,_Lp,function(_Lx,_Ly,_Lz){return new F(function(){return A(_Lq,[_Lx,_Ly,new T(function(){var _LA=E(_Ls),_LB=E(_LA[1]),_LC=E(_Lw),_LD=E(_LC[1]),_LE=E(_Lz),_LF=E(_LE[1]),_LG=B(_cW(_LD[1],_LD[2],_LD[3],_LC[2],_LF[1],_LF[2],_LF[3],_LE[2])),_LH=E(_LG[1]),_LI=B(_cW(_LB[1],_LB[2],_LB[3],_LA[2],_LH[1],_LH[2],_LH[3],_LG[2]));return [0,E(_LI[1]),_LI[2]];})]);});},function(_LJ){return new F(function(){return A(_Lq,[new T(function(){return B(A(_Lf,[_L8,_Lm]));}),_Ln,new T(function(){var _LK=E(E(_Ln)[2]),_LL=E(_Ls),_LM=E(_LL[1]),_LN=E(_Lw),_LO=E(_LN[1]),_LP=E(_LJ),_LQ=E(_LP[1]),_LR=B(_cW(_LQ[1],_LQ[2],_LQ[3],_LP[2],_LK[1],_LK[2],_LK[3],_9)),_LS=E(_LR[1]),_LT=B(_cW(_LO[1],_LO[2],_LO[3],_LN[2],_LS[1],_LS[2],_LS[3],_LR[2])),_LU=E(_LT[1]),_LV=B(_cW(_LM[1],_LM[2],_LM[3],_LL[2],_LU[1],_LU[2],_LU[3],_LT[2]));return [0,E(_LV[1]),_LV[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _Hr(_Lg,function(_LW,_LX,_LY){return new F(function(){return A(_Ll,[_LW,_LX,_Lh,_Li,function(_LZ,_M0,_M1){return new F(function(){return A(_Lh,[_LZ,_M0,new T(function(){return B(_dL(_LY,_M1));})]);});},function(_M2){return new F(function(){return A(_Li,[new T(function(){return B(_dL(_LY,_M2));})]);});}]);});},_Li,function(_M3,_M4,_M5){return new F(function(){return A(_Ll,[_M3,_M4,_Lh,_Li,function(_M6,_M7,_M8){return new F(function(){return A(_Lj,[_M6,_M7,new T(function(){return B(_dL(_M5,_M8));})]);});},function(_M9){return new F(function(){return A(_Lk,[new T(function(){return B(_dL(_M5,_M9));})]);});}]);});},_Lk);});};return new F(function(){return _jt(function(_Ma,_Mb,_Mc,_Md,_Me){return new F(function(){return _I0(_L8,_Ma,_Mb,_Mc,_Md,function(_Mf){return new F(function(){return _JM(_L8,_Ma,_Mb,_Mc,function(_Mg,_Mh,_Mi){return new F(function(){return A(_Md,[_Mg,_Mh,new T(function(){return B(_dL(_Mf,_Mi));})]);});},function(_Mj){var _Mk=function(_Ml){return new F(function(){return A(_Md,[_L8,_Ma,new T(function(){var _Mm=E(E(_Ma)[2]),_Mn=E(_Mf),_Mo=E(_Mn[1]),_Mp=E(_Mj),_Mq=E(_Mp[1]),_Mr=E(_Ml),_Ms=E(_Mr[1]),_Mt=B(_cW(_Ms[1],_Ms[2],_Ms[3],_Mr[2],_Mm[1],_Mm[2],_Mm[3],_9)),_Mu=E(_Mt[1]),_Mv=B(_cW(_Mq[1],_Mq[2],_Mq[3],_Mp[2],_Mu[1],_Mu[2],_Mu[3],_Mt[2])),_Mw=E(_Mv[1]),_Mx=B(_cW(_Mo[1],_Mo[2],_Mo[3],_Mn[2],_Mw[1],_Mw[2],_Mw[3],_Mv[2]));return [0,E(_Mx[1]),_Mx[2]];})]);});};return new F(function(){return _Fn(_Gb,_Ma,function(_My,_Mz,_MA){return new F(function(){return _Le(_My,_Mz,_Mb,_Mc,function(_MB,_MC,_MD){return new F(function(){return A(_Mb,[_MB,_MC,new T(function(){return B(_dL(_MA,_MD));})]);});},function(_ME){return new F(function(){return A(_Mc,[new T(function(){return B(_dL(_MA,_ME));})]);});});});},_Mc,function(_MF,_MG,_MH){return new F(function(){return _Le(_MF,_MG,_Mb,_Mc,function(_MI,_MJ,_MK){return new F(function(){return A(_Md,[_MI,_MJ,new T(function(){var _ML=E(_Mf),_MM=E(_ML[1]),_MN=E(_Mj),_MO=E(_MN[1]),_MP=E(_MH),_MQ=E(_MP[1]),_MR=E(_MK),_MS=E(_MR[1]),_MT=B(_cW(_MQ[1],_MQ[2],_MQ[3],_MP[2],_MS[1],_MS[2],_MS[3],_MR[2])),_MU=E(_MT[1]),_MV=B(_cW(_MO[1],_MO[2],_MO[3],_MN[2],_MU[1],_MU[2],_MU[3],_MT[2])),_MW=E(_MV[1]),_MX=B(_cW(_MM[1],_MM[2],_MM[3],_ML[2],_MW[1],_MW[2],_MW[3],_MV[2]));return [0,E(_MX[1]),_MX[2]];})]);});},function(_MY){return new F(function(){return _Mk(new T(function(){var _MZ=E(_MH),_N0=E(_MZ[1]),_N1=E(_MY),_N2=E(_N1[1]),_N3=B(_cW(_N0[1],_N0[2],_N0[3],_MZ[2],_N2[1],_N2[2],_N2[3],_N1[2]));return [0,E(_N3[1]),_N3[2]];},1));});});});},_Mk);});});});});});},_FE,_L9,_La,_Lb,_Lc,_Ld);});};_FV=function(_N4,_N5,_N6,_N7,_N8){return new F(function(){return _Hr(_N4,function(_N9,_Na,_Nb){return new F(function(){return _L7(_N9,_Na,_N5,_N6,function(_Nc,_Nd,_Ne){return new F(function(){return A(_N5,[_Nc,_Nd,new T(function(){return B(_dL(_Nb,_Ne));})]);});},function(_Nf){return new F(function(){return A(_N6,[new T(function(){return B(_dL(_Nb,_Nf));})]);});});});},_N6,function(_Ng,_Nh,_Ni){return new F(function(){return _L7(_Ng,_Nh,_N5,_N6,function(_Nj,_Nk,_Nl){return new F(function(){return A(_N7,[_Nj,_Nk,new T(function(){return B(_dL(_Ni,_Nl));})]);});},function(_Nm){return new F(function(){return A(_N8,[new T(function(){return B(_dL(_Ni,_Nm));})]);});});});},_N8);});};_FW=_G0[2];return null;}})(_FV,_FW);if(_FX!=null){return _FX;}}},_Nn=0,_No=[3,_],_Np=function(_Nq,_Nr){return [5,_No,_Nq,_Nr];},_Ns=new T(function(){return B(unCStr("=>"));}),_Nt=function(_Nu){return E(E(_Nu)[1]);},_Nv=function(_Nw,_Nx,_Ny,_Nz){while(1){var _NA=E(_Nz);if(!_NA[0]){return [0,_Nw,_Nx,_Ny];}else{var _NB=_NA[2];switch(E(E(_NA[1])[1])){case 9:var _NC=(_Ny+8|0)-B(_ge(_Ny-1|0,8))|0;_Nz=_NB;_Ny=_NC;continue;case 10:var _ND=_Nx+1|0;_Ny=1;_Nz=_NB;_Nx=_ND;continue;default:var _NC=_Ny+1|0;_Nz=_NB;_Ny=_NC;continue;}}}},_NE=function(_NF){return E(E(_NF)[1]);},_NG=function(_NH){return E(E(_NH)[2]);},_NI=function(_NJ){return [0,E(E(_NJ)[2]),_9];},_NK=function(_NL,_NM,_NN,_NO,_NP,_NQ,_NR){var _NS=E(_NM);if(!_NS[0]){return new F(function(){return A(_NQ,[_9,_NN,new T(function(){return B(_NI(_NN));})]);});}else{var _NT=E(_NN),_NU=E(_NT[2]),_NV=new T(function(){return B(_Nt(_NL));}),_NW=[0,E(_NU),[1,[2,E([1,_ga,new T(function(){return B(_i0(_NS,_gb));})])],_gd]],_NX=[2,E([1,_ga,new T(function(){return B(_i0(_NS,_gb));})])],_NY=new T(function(){var _NZ=B(_Nv(_NU[1],_NU[2],_NU[3],_NS));return [0,_NZ[1],_NZ[2],_NZ[3]];}),_O0=function(_O1,_O2){var _O3=E(_O1);if(!_O3[0]){return new F(function(){return A(_NO,[_NS,new T(function(){return [0,_O2,E(E(_NY)),E(_NT[3])];}),new T(function(){return [0,E(E(_NY)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_NE(_NV));}),[new T(function(){return B(A(new T(function(){return B(_NG(_NL));}),[_O2]));}),function(_O4){var _O5=E(_O4);if(!_O5[0]){return E(new T(function(){return B(A(_NP,[_NW]));}));}else{var _O6=E(_O5[1]),_O7=E(_O6[1]);return E(_O3[1])[1]!=_O7[1]?B(A(_NP,[[0,E(_NU),[1,_NX,[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_O7,_9],_gb));})])],_9]]]])):B(_O0(_O3[2],_O6[2]));}}]);});}};return new F(function(){return A(_NE,[_NV,new T(function(){return B(A(_NG,[_NL,_NT[1]]));}),function(_O8){var _O9=E(_O8);if(!_O9[0]){return E(new T(function(){return B(A(_NR,[_NW]));}));}else{var _Oa=E(_O9[1]),_Ob=E(_Oa[1]);return E(_NS[1])[1]!=_Ob[1]?B(A(_NR,[[0,E(_NU),[1,_NX,[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_Ob,_9],_gb));})])],_9]]]])):B(_O0(_NS[2],_Oa[2]));}}]);});}},_Oc=function(_Od,_Oe,_Of,_Og,_Oh){return new F(function(){return _NK(_kd,_Ns,_Od,function(_Oi,_Oj,_Ok){return new F(function(){return A(_Oe,[_Np,_Oj,new T(function(){var _Ol=E(E(_Oj)[2]),_Om=E(_Ok),_On=E(_Om[1]),_Oo=B(_cW(_On[1],_On[2],_On[3],_Om[2],_Ol[1],_Ol[2],_Ol[3],_9));return [0,E(_Oo[1]),_Oo[2]];})]);});},_Of,function(_Op,_Oq,_Or){return new F(function(){return A(_Og,[_Np,_Oq,new T(function(){var _Os=E(E(_Oq)[2]),_Ot=E(_Or),_Ou=E(_Ot[1]),_Ov=B(_cW(_Ou[1],_Ou[2],_Ou[3],_Ot[2],_Os[1],_Os[2],_Os[3],_9));return [0,E(_Ov[1]),_Ov[2]];})]);});},_Oh);});},_Ow=[0,_Oc,_Nn],_Ox=[1,_Ow,_9],_Oy=[1,_Ox,_9],_Oz=1,_OA=[2,_],_OB=function(_Nq,_Nr){return [5,_OA,_Nq,_Nr];},_OC=new T(function(){return B(unCStr("\\/"));}),_OD=function(_OE,_OF,_OG,_OH,_OI){return new F(function(){return _NK(_kd,_OC,_OE,function(_OJ,_OK,_OL){return new F(function(){return A(_OF,[_OB,_OK,new T(function(){var _OM=E(E(_OK)[2]),_ON=E(_OL),_OO=E(_ON[1]),_OP=B(_cW(_OO[1],_OO[2],_OO[3],_ON[2],_OM[1],_OM[2],_OM[3],_9));return [0,E(_OP[1]),_OP[2]];})]);});},_OG,function(_OQ,_OR,_OS){return new F(function(){return A(_OH,[_OB,_OR,new T(function(){var _OT=E(E(_OR)[2]),_OU=E(_OS),_OV=E(_OU[1]),_OW=B(_cW(_OV[1],_OV[2],_OV[3],_OU[2],_OT[1],_OT[2],_OT[3],_9));return [0,E(_OW[1]),_OW[2]];})]);});},_OI);});},_OX=[0,_OD,_Oz],_OY=[1,_],_OZ=function(_Nq,_Nr){return [5,_OY,_Nq,_Nr];},_P0=new T(function(){return B(unCStr("/\\"));}),_P1=function(_P2,_P3,_P4,_P5,_P6){return new F(function(){return _NK(_kd,_P0,_P2,function(_P7,_P8,_P9){return new F(function(){return A(_P3,[_OZ,_P8,new T(function(){var _Pa=E(E(_P8)[2]),_Pb=E(_P9),_Pc=E(_Pb[1]),_Pd=B(_cW(_Pc[1],_Pc[2],_Pc[3],_Pb[2],_Pa[1],_Pa[2],_Pa[3],_9));return [0,E(_Pd[1]),_Pd[2]];})]);});},_P4,function(_Pe,_Pf,_Pg){return new F(function(){return A(_P5,[_OZ,_Pf,new T(function(){var _Ph=E(E(_Pf)[2]),_Pi=E(_Pg),_Pj=E(_Pi[1]),_Pk=B(_cW(_Pj[1],_Pj[2],_Pj[3],_Pi[2],_Ph[1],_Ph[2],_Ph[3],_9));return [0,E(_Pk[1]),_Pk[2]];})]);});},_P6);});},_Pl=[0,_P1,_Oz],_Pm=[1,_Pl,_9],_Pn=[1,_OX,_Pm],_Po=[1,_Pn,_Oy],_Pp=[0,_],_Pq=function(_Nr){return [4,_Pp,_Nr];},_Pr=[0,45],_Ps=[1,_Pr,_9],_Pt=function(_Pu,_Pv,_Pw,_Px,_Py){return new F(function(){return _NK(_kd,_Ps,_Pu,function(_Pz,_PA,_PB){return new F(function(){return A(_Pv,[_Pq,_PA,new T(function(){var _PC=E(E(_PA)[2]),_PD=E(_PB),_PE=E(_PD[1]),_PF=B(_cW(_PE[1],_PE[2],_PE[3],_PD[2],_PC[1],_PC[2],_PC[3],_9));return [0,E(_PF[1]),_PF[2]];})]);});},_Pw,function(_PG,_PH,_PI){return new F(function(){return A(_Px,[_Pq,_PH,new T(function(){var _PJ=E(E(_PH)[2]),_PK=E(_PI),_PL=E(_PK[1]),_PM=B(_cW(_PL[1],_PL[2],_PL[3],_PK[2],_PJ[1],_PJ[2],_PJ[3],_9));return [0,E(_PM[1]),_PM[2]];})]);});},_Py);});},_PN=[1,_Pt],_PO=[1,_PN,_9],_PP=[1,_PO,_Po],_PQ=new T(function(){return B(unCStr("number"));}),_PR=[1,_PQ,_9],_PS=new T(function(){return B(err(_kz));}),_PT=new T(function(){return B(err(_kx));}),_PU=new T(function(){return B(_ug(_uC,_u3,_uI));}),_PV=function(_PW){return function(_PX,_PY,_PZ,_Q0,_Q1){return new F(function(){return A(_Q0,[new T(function(){var _Q2=B(_uN(B(_kC(_PU,_PW))));return _Q2[0]==0?E(_PT):E(_Q2[2])[0]==0?E(_Q2[1]):E(_PS);}),_PX,new T(function(){return [0,E(E(_PX)[2]),_9];})]);});};},_Q3=function(_Q4,_Q5,_Q6,_Q7,_Q8){return new F(function(){return _dT(_jZ,_Q4,function(_Q9,_Qa,_Qb){return new F(function(){return A(_PV,[_Q9,_Qa,_Q5,_Q6,function(_Qc,_Qd,_Qe){return new F(function(){return A(_Q5,[_Qc,_Qd,new T(function(){return B(_dL(_Qb,_Qe));})]);});},function(_Qf){return new F(function(){return A(_Q6,[new T(function(){return B(_dL(_Qb,_Qf));})]);});}]);});},_Q6,function(_Qg,_Qh,_Qi){return new F(function(){return A(_PV,[_Qg,_Qh,_Q5,_Q6,function(_Qj,_Qk,_Ql){return new F(function(){return A(_Q7,[_Qj,_Qk,new T(function(){return B(_dL(_Qi,_Ql));})]);});},function(_Qm){return new F(function(){return A(_Q8,[new T(function(){return B(_dL(_Qi,_Qm));})]);});}]);});},_Q8);});},_Qn=function(_Qo,_Qp,_Qq,_Qr,_Qs){return new F(function(){return _Q3(_Qo,function(_Qt,_Qu,_Qv){return new F(function(){return A(_Qp,[[1,[0,_,_Qt]],_Qu,new T(function(){var _Qw=E(E(_Qu)[2]),_Qx=E(_Qv),_Qy=E(_Qx[1]),_Qz=B(_cW(_Qy[1],_Qy[2],_Qy[3],_Qx[2],_Qw[1],_Qw[2],_Qw[3],_9));return [0,E(_Qz[1]),_Qz[2]];})]);});},_Qq,function(_QA,_QB,_QC){return new F(function(){return A(_Qr,[[1,[0,_,_QA]],_QB,new T(function(){var _QD=E(E(_QB)[2]),_QE=_QD[1],_QF=_QD[2],_QG=_QD[3],_QH=E(_QC),_QI=E(_QH[1]),_QJ=_QI[2],_QK=_QI[3],_QL=E(_QH[2]);if(!_QL[0]){switch(B(_cO(_QI[1],_QE))){case 0:var _QM=[0,E(_QD),_9];break;case 1:if(_QJ>=_QF){if(_QJ!=_QF){var _QN=[0,E(_QI),_9];}else{if(_QK>=_QG){var _QO=_QK!=_QG?[0,E(_QI),_9]:[0,E(_QI),_cV];}else{var _QO=[0,E(_QD),_9];}var _QP=_QO,_QN=_QP;}var _QQ=_QN,_QR=_QQ;}else{var _QR=[0,E(_QD),_9];}var _QS=_QR,_QM=_QS;break;default:var _QM=[0,E(_QI),_9];}var _QT=_QM;}else{var _QU=B(_j8(_QI,_QL,_PR)),_QV=E(_QU[1]),_QW=B(_cW(_QV[1],_QV[2],_QV[3],_QU[2],_QE,_QF,_QG,_9)),_QT=[0,E(_QW[1]),_QW[2]];}var _QX=_QT,_QY=_QX,_QZ=_QY,_R0=_QZ;return _R0;})]);});},function(_R1){return new F(function(){return A(_Qs,[new T(function(){var _R2=E(_R1),_R3=B(_j8(_R2[1],_R2[2],_PR));return [0,E(_R3[1]),_R3[2]];})]);});});});},_R4=new T(function(){return B(unCStr("P_"));}),_R5=function(_R6,_R7,_R8,_R9,_Ra){return new F(function(){return _NK(_kd,_R4,_R6,function(_Rb,_Rc,_Rd){return new F(function(){return _Qn(_Rc,_R7,_R8,function(_Re,_Rf,_Rg){return new F(function(){return A(_R7,[_Re,_Rf,new T(function(){return B(_dL(_Rd,_Rg));})]);});},function(_Rh){return new F(function(){return A(_R8,[new T(function(){return B(_dL(_Rd,_Rh));})]);});});});},_R8,function(_Ri,_Rj,_Rk){return new F(function(){return _Qn(_Rj,_R7,_R8,function(_Rl,_Rm,_Rn){return new F(function(){return A(_R9,[_Rl,_Rm,new T(function(){return B(_dL(_Rk,_Rn));})]);});},function(_Ro){return new F(function(){return A(_Ra,[new T(function(){return B(_dL(_Rk,_Ro));})]);});});});},_Ra);});},_Rp=[0,41],_Rq=new T(function(){return B(_ke(_kd,_Rp));}),_Rr=function(_Rs,_Rt,_Ru,_Rv,_Rw,_Rx){return new F(function(){return A(_Rq,[_Rt,function(_Ry,_Rz,_RA){return new F(function(){return A(_Ru,[_Rs,_Rz,new T(function(){var _RB=E(E(_Rz)[2]),_RC=E(_RA),_RD=E(_RC[1]),_RE=B(_cW(_RD[1],_RD[2],_RD[3],_RC[2],_RB[1],_RB[2],_RB[3],_9));return [0,E(_RE[1]),_RE[2]];})]);});},_Rv,function(_RF,_RG,_RH){return new F(function(){return A(_Rw,[_Rs,_RG,new T(function(){var _RI=E(E(_RG)[2]),_RJ=E(_RH),_RK=E(_RJ[1]),_RL=B(_cW(_RK[1],_RK[2],_RK[3],_RJ[2],_RI[1],_RI[2],_RI[3],_9));return [0,E(_RL[1]),_RL[2]];})]);});},_Rx]);});},_RM=function(_RN,_RO,_RP,_RQ,_RR){return new F(function(){return A(_RS,[_RN,function(_RT,_RU,_RV){return new F(function(){return _Rr(_RT,_RU,_RO,_RP,function(_RW,_RX,_RY){return new F(function(){return A(_RO,[_RW,_RX,new T(function(){return B(_dL(_RV,_RY));})]);});},function(_RZ){return new F(function(){return A(_RP,[new T(function(){return B(_dL(_RV,_RZ));})]);});});});},_RP,function(_S0,_S1,_S2){return new F(function(){return _Rr(_S0,_S1,_RO,_RP,function(_S3,_S4,_S5){return new F(function(){return A(_RQ,[_S3,_S4,new T(function(){return B(_dL(_S2,_S5));})]);});},function(_S6){return new F(function(){return A(_RR,[new T(function(){return B(_dL(_S2,_S6));})]);});});});},_RR]);});},_S7=[0,40],_S8=new T(function(){return B(_ke(_kd,_S7));}),_S9=function(_Sa,_Sb,_Sc,_Sd,_Se){var _Sf=function(_Sg){return new F(function(){return _R5(_Sa,_Sb,_Sc,function(_Sh,_Si,_Sj){return new F(function(){return A(_Sd,[_Sh,_Si,new T(function(){return B(_dL(_Sg,_Sj));})]);});},function(_Sk){return new F(function(){return A(_Se,[new T(function(){return B(_dL(_Sg,_Sk));})]);});});});};return new F(function(){return A(_S8,[_Sa,function(_Sl,_Sm,_Sn){return new F(function(){return _RM(_Sm,_Sb,_Sc,function(_So,_Sp,_Sq){return new F(function(){return A(_Sb,[_So,_Sp,new T(function(){return B(_dL(_Sn,_Sq));})]);});},function(_Sr){return new F(function(){return A(_Sc,[new T(function(){return B(_dL(_Sn,_Sr));})]);});});});},_Sc,function(_Ss,_St,_Su){return new F(function(){return _RM(_St,_Sb,_Sc,function(_Sv,_Sw,_Sx){return new F(function(){return A(_Sd,[_Sv,_Sw,new T(function(){return B(_dL(_Su,_Sx));})]);});},function(_Sy){return new F(function(){return _Sf(new T(function(){return B(_dL(_Su,_Sy));}));});});});},_Sf]);});},_RS=new T(function(){return B(_FU(_S9,_PP));}),_Sz=function(_SA,_SB,_SC,_SD,_SE){return new F(function(){return A(_RS,[_SA,function(_SF,_SG,_SH){return new F(function(){return _E4(_SF,_SG,_SB,_SC,function(_SI,_SJ,_SK){return new F(function(){return A(_SB,[_SI,_SJ,new T(function(){return B(_dL(_SH,_SK));})]);});},function(_SL){return new F(function(){return A(_SC,[new T(function(){return B(_dL(_SH,_SL));})]);});});});},_SC,function(_SM,_SN,_SO){return new F(function(){return _E4(_SM,_SN,_SB,_SC,function(_SP,_SQ,_SR){return new F(function(){return A(_SD,[_SP,_SQ,new T(function(){return B(_dL(_SO,_SR));})]);});},function(_SS){return new F(function(){return A(_SE,[new T(function(){return B(_dL(_SO,_SS));})]);});});});},_SE]);});},_ST=function(_SU,_SV,_SW,_SX,_SY){return new F(function(){return _ew(_iS,_SU,function(_SZ,_T0,_T1){return new F(function(){return _Sz(_T0,_SV,_SW,function(_T2,_T3,_T4){return new F(function(){return A(_SV,[_T2,_T3,new T(function(){return B(_dL(_T1,_T4));})]);});},function(_T5){return new F(function(){return A(_SW,[new T(function(){return B(_dL(_T1,_T5));})]);});});});},_SW,function(_T6,_T7,_T8){return new F(function(){return _Sz(_T7,_SV,_SW,function(_T9,_Ta,_Tb){return new F(function(){return A(_SX,[_T9,_Ta,new T(function(){return B(_dL(_T8,_Tb));})]);});},function(_Tc){return new F(function(){return A(_SY,[new T(function(){return B(_dL(_T8,_Tc));})]);});});});});});},_Td=function(_Te,_Tf,_Tg,_Th,_Ti,_Tj,_Tk,_Tl){var _Tm=E(_Te);if(!_Tm[0]){return new F(function(){return A(_Tl,[[0,E([0,_Tf,_Tg,_Th]),_gd]]);});}else{var _Tn=_Tm[1];if(!B(_86(_iy,_Tn,_wM))){return new F(function(){return A(_Tl,[[0,E([0,_Tf,_Tg,_Th]),[1,[0,E([1,_ga,new T(function(){return B(_i0([1,_Tn,_9],_gb));})])],_9]]]);});}else{var _To=function(_Tp,_Tq,_Tr,_Ts){var _Tt=[0,E([0,_Tp,_Tq,_Tr]),_9],_Tu=[0,E([0,_Tp,_Tq,_Tr]),_cV];return new F(function(){return _ew(_xk,[0,_Tm[2],E(_Ts),E(_Ti)],function(_Tv,_Tw,_Tx){return new F(function(){return _ST(_Tw,_Tj,_Tk,function(_Ty,_Tz,_TA){return new F(function(){return A(_Tj,[_Ty,_Tz,new T(function(){return B(_dL(_Tx,_TA));})]);});},function(_TB){return new F(function(){return A(_Tk,[new T(function(){return B(_dL(_Tx,_TB));})]);});});});},_Tk,function(_TC,_TD,_TE){return new F(function(){return _ST(_TD,_Tj,_Tk,function(_TF,_TG,_TH){return new F(function(){return A(_Tj,[_TF,_TG,new T(function(){var _TI=E(_TE),_TJ=E(_TI[1]),_TK=E(_TH),_TL=E(_TK[1]),_TM=B(_cW(_TJ[1],_TJ[2],_TJ[3],_TI[2],_TL[1],_TL[2],_TL[3],_TK[2])),_TN=E(_TM[1]),_TO=_TN[2],_TP=_TN[3],_TQ=E(_TM[2]);if(!_TQ[0]){switch(B(_cO(_Tp,_TN[1]))){case 0:var _TR=[0,E(_TN),_9];break;case 1:if(_Tq>=_TO){if(_Tq!=_TO){var _TS=E(_Tt);}else{if(_Tr>=_TP){var _TT=_Tr!=_TP?E(_Tt):E(_Tu);}else{var _TT=[0,E(_TN),_9];}var _TU=_TT,_TS=_TU;}var _TV=_TS,_TW=_TV;}else{var _TW=[0,E(_TN),_9];}var _TX=_TW,_TR=_TX;break;default:var _TR=E(_Tt);}var _TY=_TR;}else{var _TY=[0,E(_TN),_TQ];}var _TZ=_TY,_U0=_TZ,_U1=_U0,_U2=_U1,_U3=_U2,_U4=_U3;return _U4;})]);});},function(_U5){return new F(function(){return A(_Tk,[new T(function(){var _U6=E(_TE),_U7=E(_U6[1]),_U8=E(_U5),_U9=E(_U8[1]),_Ua=B(_cW(_U7[1],_U7[2],_U7[3],_U6[2],_U9[1],_U9[2],_U9[3],_U8[2])),_Ub=E(_Ua[1]),_Uc=_Ub[2],_Ud=_Ub[3],_Ue=E(_Ua[2]);if(!_Ue[0]){switch(B(_cO(_Tp,_Ub[1]))){case 0:var _Uf=[0,E(_Ub),_9];break;case 1:if(_Tq>=_Uc){if(_Tq!=_Uc){var _Ug=E(_Tt);}else{if(_Tr>=_Ud){var _Uh=_Tr!=_Ud?E(_Tt):E(_Tu);}else{var _Uh=[0,E(_Ub),_9];}var _Ui=_Uh,_Ug=_Ui;}var _Uj=_Ug,_Uk=_Uj;}else{var _Uk=[0,E(_Ub),_9];}var _Ul=_Uk,_Uf=_Ul;break;default:var _Uf=E(_Tt);}var _Um=_Uf;}else{var _Um=[0,E(_Ub),_Ue];}var _Un=_Um,_Uo=_Un,_Up=_Uo,_Uq=_Up,_Ur=_Uq,_Us=_Ur;return _Us;})]);});});});});});};switch(E(E(_Tn)[1])){case 9:var _Ut=(_Th+8|0)-B(_ge(_Th-1|0,8))|0;return new F(function(){return _To(_Tf,_Tg,_Ut,[0,_Tf,_Tg,_Ut]);});break;case 10:var _Uu=_Tg+1|0;return new F(function(){return _To(_Tf,_Uu,1,[0,_Tf,_Uu,1]);});break;default:var _Uv=_Th+1|0;return new F(function(){return _To(_Tf,_Tg,_Uv,[0,_Tf,_Tg,_Uv]);});}}}},_Uw=function(_Ux,_Uy){return E(_1);},_Uz=function(_UA,_UB,_UC,_UD){var _UE=E(_UC);switch(_UE[0]){case 0:var _UF=E(_UD);return _UF[0]==0?E(_1):E(_UF[1]);case 1:return new F(function(){return A(_UA,[_UE[1],_9]);});break;case 2:return new F(function(){return A(_UB,[_UE[1],[1,new T(function(){return B(_Uz(_UA,_UB,_UE[2],_UD));}),_9]]);});break;default:return new F(function(){return A(_UB,[_UE[1],[1,new T(function(){return B(_Uz(_UA,_UB,_UE[2],_UD));}),[1,new T(function(){return B(_Uz(_UA,_UB,_UE[3],_UD));}),_9]]]);});}},_UG=function(_UH,_UI,_UJ,_UK,_UL,_UM,_UN,_UO){var _UP=E(_UN);switch(_UP[0]){case 0:return [0];case 1:return new F(function(){return A(_UK,[_UP[1],_9]);});break;case 2:return new F(function(){return A(_UH,[_UP[1],[1,new T(function(){return B(_Uz(_UK,_UL,_UP[2],_UO));}),_9]]);});break;case 3:return new F(function(){return A(_UH,[_UP[1],[1,new T(function(){return B(_Uz(_UK,_UL,_UP[2],_UO));}),[1,new T(function(){return B(_Uz(_UK,_UL,_UP[3],_UO));}),_9]]]);});break;case 4:return new F(function(){return A(_UI,[_UP[1],[1,new T(function(){return B(_UG(_UH,_UI,_UJ,_UK,_UL,_UM,_UP[2],_UO));}),_9]]);});break;case 5:return new F(function(){return A(_UI,[_UP[1],[1,new T(function(){return B(_UG(_UH,_UI,_UJ,_UK,_UL,_UM,_UP[2],_UO));}),[1,new T(function(){return B(_UG(_UH,_UI,_UJ,_UK,_UL,_UM,_UP[3],_UO));}),_9]]]);});break;default:var _UQ=_UP[1],_UR=_UP[2];return new F(function(){return A(_UJ,[_UQ,[1,new T(function(){return B(A(_UM,[new T(function(){return B(A(_UR,[_ae]));}),_UQ]));}),[1,new T(function(){return B(_UG(_UH,_UI,_UJ,_UK,_UL,_UM,B(A(_UR,[_ae])),[1,new T(function(){return B(A(_UM,[new T(function(){return B(A(_UR,[_ae]));}),_UQ]));}),_9]));}),_9]]]);});}},_US=[0,95],_UT=[1,_US,_9],_UU=[1,_UT,_9],_UV=function(_UW){var _UX=function(_UY){var _UZ=E(new T(function(){var _V0=B(_Dg(_Cc,_RS,[0,_UW,E(_C5),E(_5c)]));if(!_V0[0]){var _V1=E(_V0[1]),_V2=_V1[0]==0?[1,_V1[1]]:[0,_V1[1]];}else{var _V3=E(_V0[1]),_V2=_V3[0]==0?[1,_V3[1]]:[0,_V3[1]];}return _V2;}));return _UZ[0]==0?function(_V4,_V5,_V6,_V7,_V8){return new F(function(){return A(_V7,[[0,[0,new T(function(){var _V9=E(_UZ[1]),_Va=E(_V9[1]);return B(_9R(_Va[1],_Va[2],_Va[3],_V9[2]));})],_9],_V4,new T(function(){return [0,E(E(_V4)[2]),_9];})]);});}:function(_Vb,_Vc,_Vd,_Ve,_Vf){return new F(function(){return A(_Ve,[[0,[0,new T(function(){return B(_UG(_Q,_u,_Q,_N,_Q,_Uw,_UZ[1],_UU));})],_9],_Vb,new T(function(){return [0,E(E(_Vb)[2]),_9];})]);});};};return function(_Vg,_Vh,_Vi,_Vj,_Vk){return new F(function(){return A(_xC,[_Vg,function(_Vl,_Vm,_Vn){return new F(function(){return A(_UX,[_,_Vm,_Vh,_Vi,function(_Vo,_Vp,_Vq){return new F(function(){return A(_Vh,[_Vo,_Vp,new T(function(){return B(_dL(_Vn,_Vq));})]);});},function(_Vr){return new F(function(){return A(_Vi,[new T(function(){return B(_dL(_Vn,_Vr));})]);});}]);});},_Vi,function(_Vs,_Vt,_Vu){return new F(function(){return A(_UX,[_,_Vt,_Vh,_Vi,function(_Vv,_Vw,_Vx){return new F(function(){return A(_Vj,[_Vv,_Vw,new T(function(){return B(_dL(_Vu,_Vx));})]);});},function(_Vy){return new F(function(){return A(_Vk,[new T(function(){return B(_dL(_Vu,_Vy));})]);});}]);});},_Vk]);});};},_Vz=function(_VA,_VB,_VC,_VD,_VE,_VF,_VG,_VH,_VI,_VJ){return new F(function(){return _i6(_VA,_VB,function(_VK){return !B(_86(_iy,_VK,_VC))?true:false;},_VD,_VE,_VF,_VG,_VH,_VI,_VJ);});},_VL=[0,9],_VM=[1,_VL,_9],_VN=[0,10],_VO=[1,_VN,_VM],_VP=function(_VQ,_VR,_VS,_VT,_VU){var _VV=E(_VQ),_VW=E(_VV[2]);return new F(function(){return _Vz(_g7,_iQ,_VO,_VV[1],_VW[1],_VW[2],_VW[3],_VV[3],_VR,_VU);});},_VX=function(_VY,_VZ,_W0,_W1,_W2){return new F(function(){return _dT(_VP,_VY,function(_W3,_W4,_W5){return new F(function(){return A(_UV,[_W3,_W4,_VZ,_W0,function(_W6,_W7,_W8){return new F(function(){return A(_VZ,[_W6,_W7,new T(function(){return B(_dL(_W5,_W8));})]);});},function(_W9){return new F(function(){return A(_W0,[new T(function(){return B(_dL(_W5,_W9));})]);});}]);});},_W0,function(_Wa,_Wb,_Wc){return new F(function(){return A(_UV,[_Wa,_Wb,_VZ,_W0,function(_Wd,_We,_Wf){return new F(function(){return A(_W1,[_Wd,_We,new T(function(){return B(_dL(_Wc,_Wf));})]);});},function(_Wg){return new F(function(){return A(_W2,[new T(function(){return B(_dL(_Wc,_Wg));})]);});}]);});},_W2);});},_Wh=function(_Wi,_Wj,_Wk,_Wl,_Wm,_Wn){var _Wo=function(_Wp,_Wq,_Wr,_Ws,_Wt,_Wu){var _Wv=function(_Ww){var _Wx=[0,[1,[0,_Wi,_Wp,new T(function(){return B(_7X(_uU,_Ww));})]],_9];return function(_Wy,_Wz,_WA,_WB,_WC){return new F(function(){return A(_xC,[_Wy,function(_WD,_WE,_WF){return new F(function(){return A(_Wz,[_Wx,_WE,new T(function(){var _WG=E(E(_WE)[2]),_WH=E(_WF),_WI=E(_WH[1]),_WJ=B(_cW(_WI[1],_WI[2],_WI[3],_WH[2],_WG[1],_WG[2],_WG[3],_9));return [0,E(_WJ[1]),_WJ[2]];})]);});},_WA,function(_WK,_WL,_WM){return new F(function(){return A(_WB,[_Wx,_WL,new T(function(){var _WN=E(E(_WL)[2]),_WO=E(_WM),_WP=E(_WO[1]),_WQ=B(_cW(_WP[1],_WP[2],_WP[3],_WO[2],_WN[1],_WN[2],_WN[3],_9));return [0,E(_WQ[1]),_WQ[2]];})]);});},_WC]);});};},_WR=function(_WS,_WT,_WU,_WV,_WW){var _WX=function(_WY,_WZ,_X0){return new F(function(){return A(_Wv,[_WY,_WZ,_WT,_WU,function(_X1,_X2,_X3){return new F(function(){return A(_WV,[_X1,_X2,new T(function(){return B(_dL(_X0,_X3));})]);});},function(_X4){return new F(function(){return A(_WW,[new T(function(){return B(_dL(_X0,_X4));})]);});}]);});},_X5=function(_X6){return new F(function(){return _WX(_9,_WS,new T(function(){var _X7=E(E(_WS)[2]),_X8=E(_X6),_X9=E(_X8[1]),_Xa=B(_cW(_X9[1],_X9[2],_X9[3],_X8[2],_X7[1],_X7[2],_X7[3],_9));return [0,E(_Xa[1]),_Xa[2]];}));});};return new F(function(){return _eW(_k5,_kw,_WS,function(_Xb,_Xc,_Xd){return new F(function(){return A(_Wv,[_Xb,_Xc,_WT,_WU,function(_Xe,_Xf,_Xg){return new F(function(){return A(_WT,[_Xe,_Xf,new T(function(){return B(_dL(_Xd,_Xg));})]);});},function(_Xh){return new F(function(){return A(_WU,[new T(function(){return B(_dL(_Xd,_Xh));})]);});}]);});},_X5,_WX,_X5);});};return new F(function(){return _ew(_iS,_Wq,function(_Xi,_Xj,_Xk){return new F(function(){return _WR(_Xj,_Wr,_Ws,function(_Xl,_Xm,_Xn){return new F(function(){return A(_Wr,[_Xl,_Xm,new T(function(){return B(_dL(_Xk,_Xn));})]);});},function(_Xo){return new F(function(){return A(_Ws,[new T(function(){return B(_dL(_Xk,_Xo));})]);});});});},_Ws,function(_Xp,_Xq,_Xr){return new F(function(){return _WR(_Xq,_Wr,_Ws,function(_Xs,_Xt,_Xu){return new F(function(){return A(_Wt,[_Xs,_Xt,new T(function(){return B(_dL(_Xr,_Xu));})]);});},function(_Xv){return new F(function(){return A(_Wu,[new T(function(){return B(_dL(_Xr,_Xv));})]);});});});});});},_Xw=function(_Xx,_Xy,_Xz,_XA,_XB){return new F(function(){return _dT(_vS,_Xx,function(_XC,_XD,_XE){return new F(function(){return _Wo(_XC,_XD,_Xy,_Xz,function(_XF,_XG,_XH){return new F(function(){return A(_Xy,[_XF,_XG,new T(function(){return B(_dL(_XE,_XH));})]);});},function(_XI){return new F(function(){return A(_Xz,[new T(function(){return B(_dL(_XE,_XI));})]);});});});},_XB,function(_XJ,_XK,_XL){return new F(function(){return _Wo(_XJ,_XK,_Xy,_Xz,function(_XM,_XN,_XO){return new F(function(){return A(_XA,[_XM,_XN,new T(function(){return B(_dL(_XL,_XO));})]);});},function(_XP){return new F(function(){return A(_XB,[new T(function(){return B(_dL(_XL,_XP));})]);});});});},_XB);});};return new F(function(){return _ew(_iS,_Wj,function(_XQ,_XR,_XS){return new F(function(){return _Xw(_XR,_Wk,_Wl,function(_XT,_XU,_XV){return new F(function(){return A(_Wk,[_XT,_XU,new T(function(){return B(_dL(_XS,_XV));})]);});},function(_XW){return new F(function(){return A(_Wl,[new T(function(){return B(_dL(_XS,_XW));})]);});});});},_Wl,function(_XX,_XY,_XZ){return new F(function(){return _Xw(_XY,_Wk,_Wl,function(_Y0,_Y1,_Y2){return new F(function(){return A(_Wm,[_Y0,_Y1,new T(function(){return B(_dL(_XZ,_Y2));})]);});},function(_Y3){return new F(function(){return A(_Wn,[new T(function(){return B(_dL(_XZ,_Y3));})]);});});});});});},_Y4=function(_Y5,_Y6,_Y7,_Y8,_Y9){return new F(function(){return A(_RS,[_Y5,function(_Ya,_Yb,_Yc){return new F(function(){return _Wh(_Ya,_Yb,_Y6,_Y7,function(_Yd,_Ye,_Yf){return new F(function(){return A(_Y6,[_Yd,_Ye,new T(function(){return B(_dL(_Yc,_Yf));})]);});},function(_Yg){return new F(function(){return A(_Y7,[new T(function(){return B(_dL(_Yc,_Yg));})]);});});});},_Y7,function(_Yh,_Yi,_Yj){return new F(function(){return _Wh(_Yh,_Yi,_Y6,_Y7,function(_Yk,_Yl,_Ym){return new F(function(){return A(_Y8,[_Yk,_Yl,new T(function(){return B(_dL(_Yj,_Ym));})]);});},function(_Yn){return new F(function(){return A(_Y9,[new T(function(){return B(_dL(_Yj,_Yn));})]);});});});},_Y9]);});},_Yo=function(_Yp,_Yq,_Yr,_Ys){var _Yt=function(_Yu){var _Yv=E(_Yp),_Yw=E(_Yv[2]),_Yx=function(_Yy){var _Yz=function(_YA){return new F(function(){return A(_Ys,[new T(function(){var _YB=E(_Yu),_YC=E(_YB[1]),_YD=E(_Yy),_YE=E(_YD[1]),_YF=E(_YA),_YG=E(_YF[1]),_YH=B(_cW(_YE[1],_YE[2],_YE[3],_YD[2],_YG[1],_YG[2],_YG[3],_YF[2])),_YI=E(_YH[1]),_YJ=B(_cW(_YC[1],_YC[2],_YC[3],_YB[2],_YI[1],_YI[2],_YI[3],_YH[2]));return [0,E(_YJ[1]),_YJ[2]];})]);});};return new F(function(){return _VX(_Yv,_Yq,_Yz,function(_YK,_YL,_YM){return new F(function(){return A(_Yr,[_YK,_YL,new T(function(){var _YN=E(_Yu),_YO=E(_YN[1]),_YP=E(_Yy),_YQ=E(_YP[1]),_YR=E(_YM),_YS=E(_YR[1]),_YT=B(_cW(_YQ[1],_YQ[2],_YQ[3],_YP[2],_YS[1],_YS[2],_YS[3],_YR[2])),_YU=E(_YT[1]),_YV=B(_cW(_YO[1],_YO[2],_YO[3],_YN[2],_YU[1],_YU[2],_YU[3],_YT[2]));return [0,E(_YV[1]),_YV[2]];})]);});},_Yz);});};return new F(function(){return _Td(_Yv[1],_Yw[1],_Yw[2],_Yw[3],_Yv[3],_Yq,_Yx,_Yx);});};return new F(function(){return _Y4(_Yp,_Yq,_Yt,_Yr,_Yt);});},_YW=function(_YX,_YY,_YZ,_Z0,_Z1){return new F(function(){return _Yo(_YX,_YY,_Z0,_Z1);});},_DC=function(_Z2,_Z3,_Z4,_Z5,_Z6){return new F(function(){return _dT(_YW,_Z2,function(_Z7,_Z8,_Z9){return new F(function(){return _wi(_Z7,_Z8,_Z3,function(_Za,_Zb,_Zc){return new F(function(){return A(_Z3,[_Za,_Zb,new T(function(){return B(_dL(_Z9,_Zc));})]);});});});},_Z4,function(_Zd,_Ze,_Zf){return new F(function(){return _wi(_Zd,_Ze,_Z3,function(_Zg,_Zh,_Zi){return new F(function(){return A(_Z5,[_Zg,_Zh,new T(function(){return B(_dL(_Zf,_Zi));})]);});});});},_Z6);});},_Zj=function(_Zk,_Zl,_Zm){while(1){var _Zn=E(_Zl);if(!_Zn[0]){return E(_Zm)[0]==0?true:false;}else{var _Zo=E(_Zm);if(!_Zo[0]){return false;}else{if(!B(A(_84,[_Zk,_Zn[1],_Zo[1]]))){return false;}else{_Zl=_Zn[2];_Zm=_Zo[2];continue;}}}}},_Zp=function(_Zq,_Zr,_Zs){var _Zt=E(_Zr),_Zu=E(_Zs);return !B(_Zj(_Zq,_Zt[1],_Zu[1]))?true:!B(A(_84,[_Zq,_Zt[2],_Zu[2]]))?true:false;},_Zv=function(_Zw,_Zx,_Zy,_Zz,_ZA){return !B(_Zj(_Zw,_Zx,_Zz))?false:B(A(_84,[_Zw,_Zy,_ZA]));},_ZB=function(_ZC,_ZD,_ZE){var _ZF=E(_ZD),_ZG=E(_ZE);return new F(function(){return _Zv(_ZC,_ZF[1],_ZF[2],_ZG[1],_ZG[2]);});},_ZH=function(_ZI){return [0,function(_ZJ,_ZK){return new F(function(){return _ZB(_ZI,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _Zp(_ZI,_ZJ,_ZK);});}];},_ZL=function(_ZM,_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT,_ZU){return new F(function(){return _lj(B(_aA(_ZM,_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT)),B(_aA(_ZM,_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZU)));});},_ZV=function(_ZW,_ZX,_ZY,_ZZ,_100,_101,_102,_103,_104){return !B(_ZL(_ZW,_ZX,_ZY,_ZZ,_100,_101,_102,_103,_104))?true:false;},_105=function(_106,_107,_108,_109,_10a,_10b,_10c){return [0,function(_bi,_bj){return new F(function(){return _ZL(_106,_107,_108,_109,_10a,_10b,_10c,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _ZV(_106,_107,_108,_109,_10a,_10b,_10c,_bi,_bj);});}];},_10d=function(_10e,_10f,_10g){var _10h=E(_10f),_10i=E(_10g);return !B(_Zj(_10e,_10h[1],_10i[1]))?true:!B(A(_84,[_10e,_10h[2],_10i[2]]))?true:false;},_10j=function(_10k,_10l,_10m){var _10n=E(_10l),_10o=E(_10m);return new F(function(){return _Zv(_10k,_10n[1],_10n[2],_10o[1],_10o[2]);});},_10p=function(_10q){return [0,function(_ZJ,_ZK){return new F(function(){return _10j(_10q,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _10d(_10q,_ZJ,_ZK);});}];},_10r=function(_10s,_10t,_10u){var _10v=E(_10s);switch(_10v[0]){case 0:var _10w=E(_10t);return _10w[0]==0?!B(_lj(_10v[3],_10w[3]))?[0]:[1,_10u]:[0];case 1:var _10x=E(_10t);return _10x[0]==1?!B(_lj(_10v[3],_10x[3]))?[0]:[1,_10u]:[0];case 2:var _10y=E(_10t);return _10y[0]==2?!B(_lj(_10v[3],_10y[3]))?[0]:[1,_10u]:[0];case 3:var _10z=E(_10t);return _10z[0]==3?!B(_lj(_10v[3],_10z[3]))?[0]:[1,_10u]:[0];case 4:var _10A=E(_10t);return _10A[0]==4?!B(_lj(_10v[3],_10A[3]))?[0]:[1,_10u]:[0];case 5:var _10B=E(_10t);return _10B[0]==5?!B(_lj(_10v[3],_10B[3]))?[0]:[1,_10u]:[0];case 6:var _10C=E(_10t);return _10C[0]==6?!B(_lj(_10v[3],_10C[3]))?[0]:[1,_10u]:[0];case 7:var _10D=E(_10t);return _10D[0]==7?!B(_lj(_10v[3],_10D[3]))?[0]:[1,_10u]:[0];case 8:var _10E=E(_10t);return _10E[0]==8?!B(_lj(_10v[3],_10E[3]))?[0]:[1,_10u]:[0];default:var _10F=E(_10t);return _10F[0]==9?!B(_lj(_10v[3],_10F[3]))?[0]:[1,_10u]:[0];}},_10G=new T(function(){return B(_3B("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_10H=function(_10I,_10J){return [3,_,_10I,_10J];},_10K=function(_10L,_10M,_10N){while(1){var _10O=E(_10N);if(!_10O[0]){return [0];}else{var _10P=E(_10O[1]),_10Q=B(A(_10L,[_10M,_10P[2],_10P[3]]));if(!_10Q[0]){_10N=_10O[2];continue;}else{return E(_10Q);}}}},_10R=function(_10S,_10T){while(1){var _10U=(function(_10V,_10W){var _10X=E(_10W);switch(_10X[0]){case 2:var _10Y=B(_10K(_10r,_10X[2],_10V));if(!_10Y[0]){return E(_10X);}else{var _10Z=_10V;_10T=_10Y[1];_10S=_10Z;return null;}break;case 4:var _110=_10X[3],_111=B(_10K(_10r,_10X[2],_10V));if(!_111[0]){return E(_10X);}else{var _112=E(_111[1]);switch(_112[0]){case 3:return E(_112[3])[0]==0?B(_10H(_112[2],_110)):E(_10X);case 4:if(!E(_112[3])[0]){var _10Z=_10V;_10T=[4,_,_112[2],_110];_10S=_10Z;return null;}else{return E(_10X);}break;default:return E(_10X);}}break;case 6:var _113=_10X[3],_114=_10X[4],_115=B(_10K(_10r,_10X[2],_10V));if(!_115[0]){return E(_10X);}else{var _116=E(_115[1]);switch(_116[0]){case 5:if(!E(_116[3])[0]){if(!E(_116[4])[0]){var _10Z=_10V;_10T=[5,_,_116[2],_113,_114];_10S=_10Z;return null;}else{return E(_10X);}}else{return E(_10X);}break;case 6:if(!E(_116[3])[0]){if(!E(_116[4])[0]){var _10Z=_10V;_10T=[6,_,_116[2],_113,_114];_10S=_10Z;return null;}else{return E(_10X);}}else{return E(_10X);}break;default:return E(_10X);}}break;case 7:return [7,_,_10X[2],new T(function(){return B(_10R(_10V,_10X[3]));})];case 8:var _117=_10X[2],_118=_10X[3],_119=B(_10K(_10r,_117,_10V));if(!_119[0]){return [8,_,_117,new T(function(){return B(_10R(_10V,_118));})];}else{var _11a=E(_119[1]);switch(_11a[0]){case 7:return E(_11a[3])[0]==0?[7,_,_11a[2],new T(function(){return B(_10R(_10V,_118));})]:[8,_,_117,new T(function(){return B(_10R(_10V,_118));})];case 8:if(!E(_11a[3])[0]){var _10Z=_10V;_10T=[8,_,_11a[2],_118];_10S=_10Z;return null;}else{return [8,_,_117,new T(function(){return B(_10R(_10V,_118));})];}break;default:return [8,_,_117,new T(function(){return B(_10R(_10V,_118));})];}}break;case 9:return [9,_,_10X[2],new T(function(){return B(_10R(_10V,_10X[3]));}),new T(function(){return B(_10R(_10V,_10X[4]));})];case 10:var _11b=_10X[2],_11c=_10X[3],_11d=_10X[4],_11e=B(_10K(_10r,_11b,_10V));if(!_11e[0]){return [10,_,_11b,new T(function(){return B(_10R(_10V,_11c));}),new T(function(){return B(_10R(_10V,_11d));})];}else{var _11f=E(_11e[1]);switch(_11f[0]){case 9:return E(_11f[3])[0]==0?E(_11f[4])[0]==0?[9,_,_11f[2],new T(function(){return B(_10R(_10V,B(_10R(_10V,_11c))));}),new T(function(){return B(_10R(_10V,B(_10R(_10V,_11d))));})]:[10,_,_11b,new T(function(){return B(_10R(_10V,_11c));}),new T(function(){return B(_10R(_10V,_11d));})]:[10,_,_11b,new T(function(){return B(_10R(_10V,_11c));}),new T(function(){return B(_10R(_10V,_11d));})];case 10:if(!E(_11f[3])[0]){if(!E(_11f[4])[0]){var _10Z=_10V;_10T=[10,_,_11f[2],_11c,_11d];_10S=_10Z;return null;}else{return [10,_,_11b,new T(function(){return B(_10R(_10V,_11c));}),new T(function(){return B(_10R(_10V,_11d));})];}}else{return [10,_,_11b,new T(function(){return B(_10R(_10V,_11c));}),new T(function(){return B(_10R(_10V,_11d));})];}break;default:return [10,_,_11b,new T(function(){return B(_10R(_10V,_11c));}),new T(function(){return B(_10R(_10V,_11d));})];}}break;case 11:return [11,_,_10X[2],function(_11g){return new F(function(){return _10R(_10V,B(A(_10X[3],[_11g])));});}];case 12:var _11h=_10X[2],_11i=_10X[3],_11j=B(_10K(_10r,_11h,_10V));if(!_11j[0]){return [12,_,_11h,function(_11k){return new F(function(){return _10R(_10V,B(A(_11i,[_11k])));});}];}else{var _11l=E(_11j[1]);switch(_11l[0]){case 11:return [11,_,_11l[2],function(_11m){return new F(function(){return _10R(_10V,B(A(_11i,[_11m])));});}];case 12:var _10Z=_10V;_10T=[12,_,_11l[2],_11i];_10S=_10Z;return null;default:return [12,_,_11h,function(_11n){return new F(function(){return _10R(_10V,B(A(_11i,[_11n])));});}];}}break;default:return E(_10X);}})(_10S,_10T);if(_10U!=null){return _10U;}}},_11o=function(_11p,_11q){var _11r=E(_11q);if(!_11r[0]){var _11s=B(_10K(_10r,_11r[1],_11p));if(!_11s[0]){return E(_11r);}else{var _11t=E(_11s[1]);return _11t[0]==0?E(_10G):[1,new T(function(){return B(_7X(function(_11u){return new F(function(){return _10R(_11p,_11u);});},_11t[1]));})];}}else{return [1,new T(function(){return B(_7X(function(_11v){return new F(function(){return _10R(_11p,_11v);});},_11r[1]));})];}},_11w=function(_11x,_11y,_11z,_11A,_11B,_11C,_11D,_11E,_11F){var _11G=E(_11F);return [0,new T(function(){return B(_7X(function(_11H){return new F(function(){return _11o(_11E,_11H);});},_11G[1]));}),new T(function(){return B(_11o(_11E,_11G[2]));})];},_11I=function(_11J,_11K,_11L,_11M,_11N,_11O,_11P,_11Q,_11R){var _11S=E(_11R);return [0,new T(function(){return B(_7X(function(_11T){return new F(function(){return _11w(_11J,_11K,_11L,_11M,_11N,_11O,_11P,_11Q,_11T);});},_11S[1]));}),new T(function(){return B(_11w(_11J,_11K,_11L,_11M,_11N,_11O,_11P,_11Q,_11S[2]));})];},_11U=function(_11V){return E(E(_11V)[1]);},_11W=function(_11X,_11Y){var _11Z=E(_11Y);return new F(function(){return A(_11U,[_11Z[1],E(_11X)[2],_11Z[2]]);});},_120=function(_121,_122,_123){var _124=E(_123);if(!_124[0]){return [0];}else{var _125=_124[1],_126=_124[2];return !B(A(_121,[_122,_125]))?[1,_125,new T(function(){return B(_120(_121,_122,_126));})]:E(_126);}},_127=function(_128,_129,_12a){while(1){var _12b=E(_12a);if(!_12b[0]){return false;}else{if(!B(A(_128,[_129,_12b[1]]))){_12a=_12b[2];continue;}else{return true;}}}},_12c=function(_12d,_12e){var _12f=function(_12g,_12h){while(1){var _12i=(function(_12j,_12k){var _12l=E(_12j);if(!_12l[0]){return [0];}else{var _12m=_12l[1],_12n=_12l[2];if(!B(_127(_12d,_12m,_12k))){return [1,_12m,new T(function(){return B(_12f(_12n,[1,_12m,_12k]));})];}else{_12g=_12n;var _12o=_12k;_12h=_12o;return null;}}})(_12g,_12h);if(_12i!=null){return _12i;}}};return new F(function(){return _12f(_12e,_9);});},_12p=function(_12q,_12r,_12s){return new F(function(){return _e(_12r,new T(function(){return B((function(_12t,_12u){while(1){var _12v=E(_12u);if(!_12v[0]){return E(_12t);}else{var _12w=B(_120(_12q,_12v[1],_12t));_12u=_12v[2];_12t=_12w;continue;}}})(B(_12c(_12q,_12s)),_12r));},1));});},_12x=function(_12y,_12z){while(1){var _12A=(function(_12B,_12C){var _12D=E(_12C);switch(_12D[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12B,_12D[2]],_9];case 3:var _12E=_12B;_12z=_12D[3];_12y=_12E;return null;case 4:return new F(function(){return _12p(_11W,[1,[0,_12B,_12D[2]],_9],new T(function(){return B(_12x(_12B,_12D[3]));},1));});break;case 5:return new F(function(){return _12p(_11W,B(_12x(_12B,_12D[3])),new T(function(){return B(_12x(_12B,_12D[4]));},1));});break;default:return new F(function(){return _12p(_11W,B(_12p(_11W,[1,[0,_12B,_12D[2]],_9],new T(function(){return B(_12x(_12B,_12D[3]));},1))),new T(function(){return B(_12x(_12B,_12D[4]));},1));});}})(_12y,_12z);if(_12A!=null){return _12A;}}},_12F=function(_12G,_12H,_12I,_12J){while(1){var _12K=(function(_12L,_12M,_12N,_12O){var _12P=E(_12O);switch(_12P[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12L,_12P[2]],_9];case 3:return new F(function(){return _12x(_12L,_12P[3]);});break;case 4:return new F(function(){return _12p(_11W,[1,[0,_12L,_12P[2]],_9],new T(function(){return B(_12x(_12L,_12P[3]));},1));});break;case 5:return new F(function(){return _12p(_11W,B(_12x(_12L,_12P[3])),new T(function(){return B(_12x(_12L,_12P[4]));},1));});break;case 6:return new F(function(){return _12p(_11W,B(_12p(_11W,[1,[0,_12L,_12P[2]],_9],new T(function(){return B(_12x(_12L,_12P[3]));},1))),new T(function(){return B(_12x(_12L,_12P[4]));},1));});break;case 7:var _12Q=_12L,_12R=_12M,_12S=_12N;_12J=_12P[3];_12G=_12Q;_12H=_12R;_12I=_12S;return null;case 8:return new F(function(){return _12p(_11W,[1,[0,_12L,_12P[2]],_9],new T(function(){return B(_12F(_12L,_12M,_12N,_12P[3]));},1));});break;case 9:return new F(function(){return _12p(_11W,B(_12F(_12L,_12M,_12N,_12P[3])),new T(function(){return B(_12F(_12L,_12M,_12N,_12P[4]));},1));});break;case 10:return new F(function(){return _12p(_11W,B(_12p(_11W,[1,[0,_12L,_12P[2]],_9],new T(function(){return B(_12F(_12L,_12M,_12N,_12P[3]));},1))),new T(function(){return B(_12F(_12L,_12M,_12N,_12P[4]));},1));});break;case 11:var _12Q=_12L,_12R=_12M,_12S=_12N;_12J=B(A(_12P[3],[_ae]));_12G=_12Q;_12H=_12R;_12I=_12S;return null;default:return new F(function(){return _12p(_11W,[1,[0,_12L,_12P[2]],_9],new T(function(){return B(_12F(_12L,_12M,_12N,B(A(_12P[3],[_ae]))));},1));});}})(_12G,_12H,_12I,_12J);if(_12K!=null){return _12K;}}},_12T=function(_12U,_12V,_12W,_12X,_12Y){var _12Z=function(_130){return new F(function(){return _12F(_12U,_12V,_12W,_130);});};return new F(function(){return _e(B(_7r(B(_7X(function(_131){var _132=E(_131);if(!_132[0]){return [1,[0,_12U,_132[1]],_9];}else{return new F(function(){return _7r(B(_7X(_12Z,_132[1])));});}},_12X)))),new T(function(){var _133=E(_12Y);if(!_133[0]){var _134=[1,[0,_12U,_133[1]],_9];}else{var _134=B(_7r(B(_7X(_12Z,_133[1]))));}return _134;},1));});},_135=function(_136,_137,_138,_139,_13a,_13b,_13c,_13d,_13e){var _13f=E(_13e);return new F(function(){return _e(B(_7r(B(_7X(function(_13g){var _13h=E(_13g);return new F(function(){return _12T(_136,_13a,_13b,_13h[1],_13h[2]);});},_13f[1])))),new T(function(){var _13i=E(_13f[2]);return B(_12T(_136,_13a,_13b,_13i[1],_13i[2]));},1));});},_13j=function(_13k,_13l,_13m,_13n,_13o,_13p,_13q,_13r,_13s,_13t,_13u){return [0,_13k,_13l,_13m,_13n,function(_11T){return new F(function(){return _135(_13k,_13o,_13p,_13q,_13r,_13s,_13t,_13u,_11T);});},function(_13v,_11T){return new F(function(){return _11I(_13o,_13p,_13q,_13r,_13s,_13t,_13u,_13v,_11T);});}];},_13w=function(_13x){return E(E(_13x)[2]);},_13y=function(_13z){return E(E(_13z)[1]);},_13A=[0,_13y,_13w],_13B=[0,125],_13C=new T(function(){return B(unCStr("given = "));}),_13D=new T(function(){return B(unCStr(", "));}),_13E=new T(function(){return B(unCStr("needed = "));}),_13F=new T(function(){return B(unCStr("AbsRule {"));}),_13G=[0,0],_13H=function(_13I){return E(E(_13I)[3]);},_13J=function(_13K){return E(E(_13K)[1]);},_13L=function(_13M,_13N,_13O,_13P){var _13Q=function(_13R){return new F(function(){return _e(_13F,new T(function(){return B(_e(_13E,new T(function(){return B(A(new T(function(){return B(A(_13H,[_13M,_13O]));}),[new T(function(){return B(_e(_13D,new T(function(){return B(_e(_13C,new T(function(){return B(A(new T(function(){return B(A(_13J,[_13M,_13G,_13P]));}),[[1,_13B,_13R]]));},1)));},1)));})]));},1)));},1));});};return _13N<11?E(_13Q):function(_13S){return [1,_E,new T(function(){return B(_13Q([1,_D,_13S]));})];};},_13T=function(_13U,_13V){var _13W=E(_13V);return new F(function(){return A(_13L,[_13U,0,_13W[1],_13W[2],_9]);});},_13X=function(_13Y,_13Z,_140){return new F(function(){return _2T(function(_141){var _142=E(_141);return new F(function(){return _13L(_13Y,0,_142[1],_142[2]);});},_13Z,_140);});},_143=function(_144,_145,_146){var _147=E(_146);return new F(function(){return _13L(_144,E(_145)[1],_147[1],_147[2]);});},_148=function(_149){return [0,function(_ZJ,_ZK){return new F(function(){return _143(_149,_ZJ,_ZK);});},function(_ZK){return new F(function(){return _13T(_149,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _13X(_149,_ZJ,_ZK);});}];},_14a=new T(function(){return B(unCStr("Sequent "));}),_14b=[0,11],_14c=[0,32],_14d=function(_14e,_14f,_14g,_14h){var _14i=new T(function(){return B(A(_13J,[_14e,_14b,_14h]));}),_14j=new T(function(){return B(A(_13H,[_14e,_14g]));});return _14f<11?function(_14k){return new F(function(){return _e(_14a,new T(function(){return B(A(_14j,[[1,_14c,new T(function(){return B(A(_14i,[_14k]));})]]));},1));});}:function(_14l){return [1,_E,new T(function(){return B(_e(_14a,new T(function(){return B(A(_14j,[[1,_14c,new T(function(){return B(A(_14i,[[1,_D,_14l]]));})]]));},1)));})];};},_14m=function(_14n,_14o){var _14p=E(_14o);return new F(function(){return A(_14d,[_14n,0,_14p[1],_14p[2],_9]);});},_14q=function(_14r,_14s,_14t){return new F(function(){return _2T(function(_14u){var _14v=E(_14u);return new F(function(){return _14d(_14r,0,_14v[1],_14v[2]);});},_14s,_14t);});},_14w=function(_14x,_14y,_14z){var _14A=E(_14z);return new F(function(){return _14d(_14x,E(_14y)[1],_14A[1],_14A[2]);});},_14B=function(_14C){return [0,function(_ZJ,_ZK){return new F(function(){return _14w(_14C,_ZJ,_ZK);});},function(_ZK){return new F(function(){return _14m(_14C,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _14q(_14C,_ZJ,_ZK);});}];},_14D=function(_14E,_14F){return new F(function(){return _e(B(_a1(_14E)),_14F);});},_14G=function(_14H,_14I){return new F(function(){return _2T(_14D,_14H,_14I);});},_14J=function(_14K,_14L,_14M){return new F(function(){return _e(B(_a1(_14L)),_14M);});},_14N=[0,_14J,_a1,_14G],_14O=function(_14P,_14Q,_14R,_14S,_14T,_14U,_14V,_14W,_14X,_14Y,_14Z,_150){var _151=E(_150);return new F(function(){return _12T(_14P,_14W,_14X,_151[1],_151[2]);});},_152=function(_153,_154,_155,_156,_157,_158,_159,_15a,_15b,_15c,_15d){return [0,_153,_154,_155,_156,function(_11T){return new F(function(){return _14O(_153,_154,_155,_156,_157,_158,_159,_15a,_15b,_15c,_15d,_11T);});},function(_13v,_11T){return new F(function(){return _11w(_157,_158,_159,_15a,_15b,_15c,_15d,_13v,_11T);});}];},_15e=function(_15f,_15g){return [0];},_15h=function(_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_15q,_15r,_15s,_15t,_15u,_15v){return [0,_15i,_15j,_15e,_1];},_15w=function(_15x,_15y,_15z,_15A,_15B,_15C,_15D,_15E,_15F,_15G,_15H,_15I){var _15J=E(_15I);if(!_15J[0]){return [1,[0,_15x,_15J[1]],_9];}else{return new F(function(){return _7r(B(_7X(function(_15K){return new F(function(){return _12F(_15x,_15E,_15F,_15K);});},_15J[1])));});}},_15L=function(_15M,_15N,_15O,_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W){return [0,_15M,_15N,_15O,_15P,function(_11T){return new F(function(){return _15w(_15M,_15N,_15O,_15P,_15Q,_15R,_15S,_15T,_15U,_15V,_15W,_11T);});},_11o];},_15X=new T(function(){return B(_C8("w_syIh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv aymk} [tv] quant{tv aymi} [tv]"));}),_15Y=new T(function(){return B(_C8("w_syIg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv aymi} [tv]"));}),_15Z=new T(function(){return B(_C8("w_syIf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv aymh} [tv]"));}),_160=new T(function(){return B(_C8("w_syIe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv aymk} [tv]"));}),_161=new T(function(){return B(_C8("w_syId{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv aymg} [tv]"));}),_162=new T(function(){return B(_C8("w_syIc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv aymj} [tv]"));}),_163=new T(function(){return B(_C8("w_syIi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv aymk} [tv]"));}),_164=new T(function(){return B(_C8("w_syIb{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aymi} [tv]"));}),_165=new T(function(){return B(_C8("w_syIa{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv aymh} [tv]"));}),_166=new T(function(){return B(_C8("w_syI9{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv aymk} [tv]"));}),_167=new T(function(){return B(_C8("w_syI8{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv aymg} [tv]"));}),_168=new T(function(){return B(_C8("w_syI7{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aymj} [tv]"));}),_169=function(_16a,_16b){return function(_16c,_16d){var _16e=E(_16c);return _16e[0]==0?[1,[0,new T(function(){return B(_16f(_16a,_16b,_168,_167,_166,_165,_164,_162,_161,_160,_15Z,_15Y,_15X,_163));}),_16e[1],_16d]]:[0];};},_16g=function(_16h){return [0,E(_16h)];},_16f=function(_16i,_16j,_16k,_16l,_16m,_16n,_16o,_16p,_16q,_16r,_16s,_16t,_16u,_16v){return [0,_16i,_16j,new T(function(){return B(_169(_16i,_16j));}),_16g];},_16w=[1,_9],_16x=function(_16y,_16z){while(1){var _16A=E(_16y);if(!_16A[0]){return E(_16z);}else{_16y=_16A[2];var _16B=_16z+1|0;_16z=_16B;continue;}}},_16C=[0,95],_16D=[1,_16C,_9],_16E=[1,_16D,_9],_16F=function(_16G,_16H,_16I){return !B(_lj(B(A(_16G,[_16H,_16E])),B(A(_16G,[_16I,_16E]))))?true:false;},_16J=function(_16K){return [0,function(_16L,_16M){return new F(function(){return _lj(B(A(_16K,[_16L,_16E])),B(A(_16K,[_16M,_16E])));});},function(_bi,_bj){return new F(function(){return _16F(_16K,_bi,_bj);});}];},_16N=function(_16O,_16P){return new F(function(){return _10R(_16O,_16P);});},_16Q=function(_16R,_16S,_16T,_16U,_16V,_16W,_16X,_16Y,_16Z,_170,_171){return [0,_16R,_16S,_16T,_16U,function(_172){return new F(function(){return _12F(_16R,_16Y,_16Z,_172);});},_16N];},_173=new T(function(){return B(_C8("w_snA5{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv akx5} [tv] quant{tv akx3} [tv]"));}),_174=new T(function(){return B(_C8("w_snA4{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv akx3} [tv]"));}),_175=new T(function(){return B(_C8("w_snA3{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv akx2} [tv]"));}),_176=new T(function(){return B(_C8("w_snA2{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv akx5} [tv]"));}),_177=new T(function(){return B(_C8("w_snA1{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv akx1} [tv]"));}),_178=new T(function(){return B(_C8("w_snA0{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv akx4} [tv]"));}),_179=new T(function(){return B(_C8("w_snA6{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv akx5} [tv]"));}),_17a=new T(function(){return B(_C8("w_snzZ{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv akx3} [tv]"));}),_17b=new T(function(){return B(_C8("w_snzY{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv akx2} [tv]"));}),_17c=new T(function(){return B(_C8("w_snzX{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv akx5} [tv]"));}),_17d=new T(function(){return B(_C8("w_snzW{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv akx1} [tv]"));}),_17e=new T(function(){return B(_C8("w_snzV{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv akx4} [tv]"));}),_17f=function(_17g,_17h,_17i,_17j){var _17k=E(_17i);switch(_17k[0]){case 2:return [1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17k[2],_17j]];case 4:var _17m=_17k[2];if(!E(_17k[3])[0]){var _17n=E(_17j);switch(_17n[0]){case 3:return E(_17n[3])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17m,_17n]]:[0];case 4:return E(_17n[3])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17m,_17n]]:[0];default:return [0];}}else{return [0];}break;case 6:var _17o=_17k[2];if(!E(_17k[3])[0]){if(!E(_17k[4])[0]){var _17p=E(_17j);switch(_17p[0]){case 5:return E(_17p[3])[0]==0?E(_17p[4])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17o,_17p]]:[0]:[0];case 6:return E(_17p[3])[0]==0?E(_17p[4])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17o,_17p]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _17q=_17k[2];if(!E(_17k[3])[0]){var _17r=E(_17j);switch(_17r[0]){case 7:return E(_17r[3])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17q,_17r]]:[0];case 8:return E(_17r[3])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17q,_17r]]:[0];default:return [0];}}else{return [0];}break;case 10:var _17s=_17k[2];if(!E(_17k[3])[0]){if(!E(_17k[4])[0]){var _17t=E(_17j);switch(_17t[0]){case 9:return E(_17t[3])[0]==0?E(_17t[4])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17s,_17t]]:[0]:[0];case 10:return E(_17t[3])[0]==0?E(_17t[4])[0]==0?[1,[0,new T(function(){return B(_17l(_17g,_17h,_17e,_17d,_17c,_17b,_17a,_178,_177,_176,_175,_174,_173,_179));}),_17s,_17t]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_17u=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_17v=function(_17w){var _17x=E(_17w);switch(_17x[0]){case 3:return [2,_,_17x];case 4:return [4,_,_17x,_V];case 5:return [6,_,_17x,_V,_V];case 6:return [8,_,_17x,_S];case 7:return [10,_,_17x,_S,_S];default:return E(_17u);}},_17l=function(_17y,_17z,_17A,_17B,_17C,_17D,_17E,_17F,_17G,_17H,_17I,_17J,_17K,_17L){return [0,_17y,_17z,function(_17M,_17N){return new F(function(){return _17f(_17y,_17z,_17M,_17N);});},_17v];},_17O=function(_17P,_17Q,_17R){return new F(function(){return _2T(function(_17S,_17T){return new F(function(){return _e(B(A(_17P,[_17S,_16E])),_17T);});},_17Q,_17R);});},_17U=function(_17V){return [0,function(_17W,_17X,_17Y){return new F(function(){return _e(B(A(_17V,[_17X,_16E])),_17Y);});},function(_17Z){return new F(function(){return A(_17V,[_17Z,_16E]);});},function(_bi,_bj){return new F(function(){return _17O(_17V,_bi,_bj);});}];},_180=[1,_9],_181=function(_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18c,_18d){var _18e=E(_18c);if(_18e[0]==2){return E(_180);}else{var _18f=E(_18d);if(_18f[0]==2){return E(_180);}else{var _18g=function(_18h){var _18i=function(_18j){var _18k=function(_18l){var _18m=function(_18n){var _18o=function(_18p){var _18q=function(_18r){var _18s=function(_18t){var _18u=function(_18v){var _18w=function(_18x){var _18y=function(_18z){var _18A=function(_18B){var _18C=function(_18D){var _18E=E(_18e);switch(_18E[0]){case 1:var _18F=E(_18f);return _18F[0]==1?!B(A(_183,[_18E[2],_18F[2]]))?[0]:E(_180):[0];case 3:var _18G=E(_18f);return _18G[0]==3?!B(A(_182,[_18E[2],_18G[2]]))?[0]:E(_180):[0];case 4:var _18H=_18E[2],_18I=E(_18f);switch(_18I[0]){case 3:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[4,_,_18H,_V],[3,_,_18I[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[4,_,_18H,_V],[4,_,_18I[2],_V]]));}),_9]];default:return [0];}break;case 5:var _18K=E(_18f);return _18K[0]==5?!B(A(_182,[_18E[2],_18K[2]]))?[0]:E(_180):[0];case 6:var _18L=_18E[2],_18M=E(_18f);switch(_18M[0]){case 5:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[6,_,_18L,_V,_V],[5,_,_18M[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[6,_,_18L,_V,_V],[6,_,_18M[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _18N=E(_18f);return _18N[0]==7?!B(A(_184,[_18E[2],_18N[2]]))?[0]:[1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18E[3],_18N[3]]));}),_9]]:[0];case 8:var _18O=_18E[2],_18P=_18E[3],_18Q=E(_18f);switch(_18Q[0]){case 7:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[8,_,_18O,_S],[7,_,_18Q[2],_S]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18P,_18Q[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[8,_,_18O,_S],[8,_,_18Q[2],_S]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18P,_18Q[3]]));}),_9]]];default:return [0];}break;case 9:var _18R=E(_18f);return _18R[0]==9?!B(A(_184,[_18E[2],_18R[2]]))?[0]:[1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18E[3],_18R[3]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18E[4],_18R[4]]));}),_9]]]:[0];case 10:var _18S=_18E[2],_18T=_18E[3],_18U=_18E[4],_18V=function(_18W){var _18X=E(_18f);switch(_18X[0]){case 9:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[10,_,_18S,_S,_S],[9,_,_18X[2],_S,_S]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18T,_18X[3]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18U,_18X[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,[10,_,_18S,_S,_S],[10,_,_18X[2],_S,_S]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18T,_18X[3]]));}),[1,new T(function(){return B(A(_18J,[_182,_183,_184,_185,_186,_187,_188,_189,_18a,_18b,_18U,_18X[4]]));}),_9]]]];default:return [0];}};return E(_18T)[0]==0?E(_18U)[0]==0?E(_180):B(_18V(_)):B(_18V(_));default:return [0];}},_18Y=E(_18f);return _18Y[0]==10?E(_18Y[3])[0]==0?E(_18Y[4])[0]==0?E(_180):B(_18C(_)):B(_18C(_)):B(_18C(_));},_18Z=E(_18e);return _18Z[0]==8?E(_18Z[3])[0]==0?E(_180):B(_18A(_)):B(_18A(_));},_190=E(_18f);switch(_190[0]){case 6:return E(_190[3])[0]==0?E(_190[4])[0]==0?E(_180):B(_18y(_)):B(_18y(_));case 8:return E(_190[3])[0]==0?E(_180):B(_18y(_));default:return new F(function(){return _18y(_);});}},_191=E(_18e);return _191[0]==6?E(_191[3])[0]==0?E(_191[4])[0]==0?E(_180):B(_18w(_)):B(_18w(_)):B(_18w(_));},_192=E(_18f);return _192[0]==4?E(_192[3])[0]==0?E(_180):B(_18u(_)):B(_18u(_));},_193=E(_18e);switch(_193[0]){case 4:return E(_193[3])[0]==0?E(_180):B(_18s(_));case 9:return E(_193[3])[0]==0?E(_193[4])[0]==0?E(_180):B(_18s(_)):B(_18s(_));default:return new F(function(){return _18s(_);});}},_194=E(_18f);return _194[0]==9?E(_194[3])[0]==0?E(_194[4])[0]==0?E(_180):B(_18q(_)):B(_18q(_)):B(_18q(_));},_195=E(_18e);return _195[0]==7?E(_195[3])[0]==0?E(_180):B(_18o(_)):B(_18o(_));},_196=E(_18f);switch(_196[0]){case 5:return E(_196[3])[0]==0?E(_196[4])[0]==0?E(_180):B(_18m(_)):B(_18m(_));case 7:return E(_196[3])[0]==0?E(_180):B(_18m(_));default:return new F(function(){return _18m(_);});}},_197=E(_18e);return _197[0]==5?E(_197[3])[0]==0?E(_197[4])[0]==0?E(_180):B(_18k(_)):B(_18k(_)):B(_18k(_));},_198=E(_18f);return _198[0]==3?E(_198[3])[0]==0?E(_180):B(_18i(_)):B(_18i(_));},_199=E(_18e);return _199[0]==3?E(_199[3])[0]==0?E(_180):B(_18g(_)):B(_18g(_));}}},_19a=function(_19b,_19c,_19d){return [0,_19b,_19c,_19d];},_19e=new T(function(){return B(_C8("w_snAe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv akwq} [tv]"));}),_19f=new T(function(){return B(_C8("w_snAa{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv akwr} [tv]"));}),_19g=function(_19h){return [0,function(_19i,_19j){return B(A(_19h,[_19i,_19j,_1]))[0]==0?false:true;},function(_19k,_19l){return B(A(_19h,[_19k,_19l,_1]))[0]==0?true:false;}];},_19m=new T(function(){return B(_19g(_10r));}),_18J=function(_19n,_19o,_19p,_19q,_19r,_19s,_19t,_19u,_19v,_19w){var _19x=function(_19y,_19z){return new F(function(){return _af(_19r,_19t,_19u,_19s,_19q,_19v,_19w,_19y);});};return function(_m0,_19A){return new F(function(){return _19a(new T(function(){return B(_17l(function(_19B,_19C){return new F(function(){return _181(_19n,_19o,_19p,_19q,_19r,_19s,_19t,_19u,_19v,_19w,_19B,_19C);});},new T(function(){return B(_16Q(_19m,_14N,new T(function(){return B(_16J(_19x));}),new T(function(){return B(_17U(_19x));}),_19r,_19t,_19u,_19q,_19s,_19v,_19w));}),_19f,_19n,_19o,_19p,_19e,_19q,_19r,_19s,_19t,_19u,_19v,_19w));}),_m0,_19A);});};},_19D=function(_19E,_19F,_19G){var _19H=E(_19F);if(!_19H[0]){return [0];}else{var _19I=E(_19G);return _19I[0]==0?[0]:[1,new T(function(){return B(A(_19E,[_19H[1],_19I[1]]));}),new T(function(){return B(_19D(_19E,_19H[2],_19I[2]));})];}},_19J=function(_19K,_19L,_19M,_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U,_19V){var _19W=E(_19U);if(!_19W[0]){return E(_16w);}else{var _19X=_19W[1],_19Y=E(_19V);if(!_19Y[0]){return E(_16w);}else{var _19Z=_19Y[1];return B(_16x(_19X,0))!=B(_16x(_19Z,0))?[0]:[1,new T(function(){return B(_19D(new T(function(){return B(_18J(_19K,_19L,_19M,_19N,_19O,_19P,_19Q,_19R,_19S,_19T));}),_19X,_19Z));})];}}},_1a0=new T(function(){return B(_C8("w_syJ2{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aym0} [tv]"));}),_1a1=new T(function(){return B(_C8("w_syJ6{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aylZ} [tv]"));}),_1a2=new T(function(){return B(_19g(_10r));}),_1a3=function(_1a4,_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad){var _1ae=new T(function(){return B(_16f(function(_1af,_1ag){return new F(function(){return _19J(_1a4,_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1af,_1ag);});},new T(function(){return B(_15L(_1a2,_14N,new T(function(){return B(_105(_1a8,_1aa,_1ab,_1a7,_1a9,_1ac,_1ad));}),new T(function(){return B(_b9(_1a8,_1aa,_1ab,_1a7,_1a9,_1ac,_1ad));}),_1a8,_1aa,_1ab,_1a7,_1a9,_1ac,_1ad));}),_1a0,_1a4,_1a5,_1a6,_1a1,_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad));});return function(_1ah,_1ai){var _1aj=E(_1ah),_1ak=_1aj[1],_1al=E(_1ai),_1am=_1al[1];return B(_16x(_1ak,0))!=B(_16x(_1am,0))?[0]:[1,[1,[0,_1ae,_1aj[2],_1al[2]],new T(function(){return B(_19D(function(_13v,_11T){return [0,_1ae,_13v,_11T];},_1ak,_1am));})]];};},_1an=new T(function(){return B(_C8("w_syLE{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aylx} [tv]"));}),_1ao=new T(function(){return B(_C8("w_syLI{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aylw} [tv]"));}),_1ap=function(_1aq,_1ar,_1as,_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az){var _1aA=new T(function(){return B(_15h(new T(function(){return B(_1a3(_1aq,_1ar,_1as,_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az));}),new T(function(){return B(_152(_1a2,_14N,new T(function(){return B(_10p(new T(function(){return B(_105(_1au,_1aw,_1ax,_1at,_1av,_1ay,_1az));})));}),new T(function(){return B(_14B(new T(function(){return B(_b9(_1au,_1aw,_1ax,_1at,_1av,_1ay,_1az));})));}),_1au,_1aw,_1ax,_1at,_1av,_1ay,_1az));}),_1an,_1aq,_1ar,_1as,_1ao,_1at,_1au,_1av,_1aw,_1ax,_1ay,_1az));});return function(_1aB,_1aC){var _1aD=E(_1aB),_1aE=_1aD[1],_1aF=E(_1aC),_1aG=_1aF[1];return B(_16x(_1aE,0))!=B(_16x(_1aG,0))?[0]:[1,[1,[0,_1aA,_1aD[2],_1aF[2]],new T(function(){return B(_19D(function(_13v,_11T){return [0,_1aA,_13v,_11T];},_1aE,_1aG));})]];};},_1aH=function(_1aI,_1aJ){while(1){var _1aK=E(_1aJ);if(!_1aK[0]){return false;}else{var _1aL=E(_1aK[1]);if(!B(A(_11U,[_1aL[1],_1aI,_1aL[2]]))){_1aJ=_1aK[2];continue;}else{return true;}}}},_1aM=[0,_9],_1aN=function(_1aO,_1aP,_1aQ,_1aR,_1aS,_1aT,_1aU,_1aV,_1aW,_1aX,_1aY){var _1aZ=E(_1aR);return !B(A(_1aZ[1],[new T(function(){return B(A(_1aW,[_1aX]));}),_1aY]))?!B(_1aH(_1aX,B(A(_1aT,[_1aY]))))?[0,[1,[0,[0,_1aO,[0,_1aP,_1aQ,_1aZ,_1aS,_1aT,_1aU],_1aV,_1aW],_1aX,_1aY],_9]]:[1,[1,_,[0,_1aO,[0,_1aP,_1aQ,_1aZ,_1aS,_1aT,_1aU],_1aV,_1aW],[3,_1aQ,_1aS,_1aX,_1aY]]]:E(_1aM);},_1b0=function(_1b1){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(54,15)-(56,42)|case");});},_1b2=new T(function(){return B(_1b0(_));}),_1b3=new T(function(){return B(unCStr(": empty list"));}),_1b4=new T(function(){return B(unCStr("Prelude."));}),_1b5=function(_1b6){return new F(function(){return err(B(_e(_1b4,new T(function(){return B(_e(_1b6,_1b3));},1))));});},_1b7=new T(function(){return B(unCStr("head"));}),_1b8=new T(function(){return B(_1b5(_1b7));}),_1b9=function(_1ba){return E(E(_1ba)[2]);},_1bb=function(_1bc,_1bd){while(1){var _1be=E(_1bc);if(!_1be){return E(_1bd);}else{var _1bf=E(_1bd);if(!_1bf[0]){return [0];}else{_1bc=_1be-1|0;_1bd=_1bf[2];continue;}}}},_1bg=function(_1bh,_1bi){var _1bj=E(_1bh)[1];return _1bj>=0?B(_1bb(_1bj,_1bi)):E(_1bi);},_1bk=function(_1bl){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:96:31-64|function conc");});},_1bm=new T(function(){return B(_1bk(_));}),_1bn=function(_1bo){var _1bp=E(_1bo);switch(_1bp[0]){case 3:return [2,_,_1bp];case 4:return [4,_,_1bp,_V];case 5:return [6,_,_1bp,_V,_V];case 6:return [8,_,_1bp,_S];case 7:return [10,_,_1bp,_S,_S];default:return E(_17u);}},_1bq=function(_1br){var _1bs=E(_1br);if(!_1bs[0]){return [0];}else{var _1bt=E(_1bs[1]);if(!_1bt[0]){return [0];}else{return new F(function(){return _e(_1bt[1],new T(function(){return B(_1bq(_1bs[2]));},1));});}}},_1bu=function(_1bv){var _1bw=E(_1bv);return [0,[1,[1,new T(function(){return B(_1bq(_1bw[1]));})],_9],_1bw[2]];},_1bx=function(_1by,_1bz,_1bA){return !B(_86(_1by,_1bz,_1bA))?E(_1bA):[1,_1bz,new T(function(){return B(_7u(function(_1bB){return !B(A(_84,[_1by,_1bB,_1bz]))?true:false;},_1bA));})];},_1bC=function(_1bD,_1bE,_1bF,_1bG,_1bH,_1bI,_1bJ){return function(_1bK,_1bL){var _1bM=E(_1bK);if(!_1bM[0]){return new F(function(){return _1bu(_1bL);});}else{var _1bN=E(_1bL);return [0,[1,[1,new T(function(){return B(_1bx(new T(function(){return B(_16J(function(_1bO,_1bP){return new F(function(){return _af(_1bJ,_1bI,_1bH,_1bF,_1bG,_1bD,_1bE,_1bO);});}));}),_1bM[1],B(_1bq(_1bN[1]))));})],_9],_1bN[2]];}};},_1bQ=new T(function(){return B(_19g(_10r));}),_1bR=function(_1bS){return E(E(_1bS)[1]);},_1bT=function(_1bU,_1bV){var _1bW=E(_1bU);if(!_1bW){return [0];}else{var _1bX=E(_1bV);return _1bX[0]==0?[0]:[1,_1bX[1],new T(function(){return B(_1bT(_1bW-1|0,_1bX[2]));})];}},_1bY=function(_1bZ,_1c0){return _1bZ<0?[0]:B(_1bT(_1bZ,_1c0));},_1c1=function(_1c2,_1c3){var _1c4=E(_1c2)[1];return _1c4>0?B(_1bY(_1c4,_1c3)):[0];},_1c5=function(_1c6,_1c7){return [1,_,_1c6,_1c7];},_1c8=function(_1c9){return E(E(_1c9)[2]);},_1ca=function(_1cb){return E(E(_1cb)[4]);},_1cc=function(_1cd,_1ce,_1cf){var _1cg=E(_1cd),_1ch=E(_1cg[2]);return new F(function(){return _1aN(_1cg[1],_1ch[1],_1ch[2],_1ch[3],_1ch[4],_1ch[5],_1ch[6],_1cg[3],_1cg[4],_1ce,_1cf);});},_1ci=function(_1cj,_1ck,_1cl,_1cm,_1cn,_1co){var _1cp=B(A(_1cl,[_1cn,_1co]));if(!_1cp[0]){var _1cq=B(A(_1cl,[_1co,_1cn]));if(!_1cq[0]){var _1cr=B(A(_1cj,[_1cn,_1co]));if(!_1cr[0]){return [1,[0,new T(function(){return B(_1ca(_1ck));}),_1cn,_1co]];}else{var _1cs=B(_1ct([0,_1cj,_1ck,_1cl,_1cm],_1cr[1]));return _1cs[0]==0?E(_1cs):[1,[2,new T(function(){return B(_1ca(_1ck));}),_1cs[1],_1cn,_1co]];}}else{var _1cu=E(_1cq[1]);return new F(function(){return _1cc(_1cu[1],_1cu[2],_1cu[3]);});}}else{var _1cv=E(_1cp[1]);return new F(function(){return _1cc(_1cv[1],_1cv[2],_1cv[3]);});}},_1cw=function(_1cx){return E(E(_1cx)[6]);},_1ct=function(_1cy,_1cz){var _1cA=E(_1cz);if(!_1cA[0]){return E(_1aM);}else{var _1cB=E(_1cA[1]),_1cC=E(_1cB[1]),_1cD=B(_1ci(_1cC[1],_1cC[2],_1cC[3],_1cC[4],_1cB[2],_1cB[3]));if(!_1cD[0]){var _1cE=_1cD[1],_1cF=B(_1ct(_1cy,B(_7X(function(_1cG){var _1cH=E(_1cG),_1cI=_1cH[1];return [0,_1cI,new T(function(){return B(A(_1cw,[B(_1c8(_1cI)),_1cE,_1cH[2]]));}),new T(function(){return B(A(_1cw,[B(_1c8(_1cI)),_1cE,_1cH[3]]));})];},_1cA[2]))));if(!_1cF[0]){var _1cJ=_1cF[1];return [0,new T(function(){var _1cK=function(_1cL){var _1cM=E(_1cL);return _1cM[0]==0?E(_1cJ):[1,new T(function(){var _1cN=E(_1cM[1]),_1cO=_1cN[1];return [0,_1cO,_1cN[2],new T(function(){return B(A(_1cw,[B(_1c8(_1cO)),_1cJ,_1cN[3]]));})];}),new T(function(){return B(_1cK(_1cM[2]));})];};return B(_1cK(_1cE));})];}else{return [1,new T(function(){return B(_1c5(_1cy,_1cF[1]));})];}}else{return [1,[1,_,_1cC,_1cD[1]]];}}},_1cP=function(_1cQ,_1cR,_1cS,_1cT,_1cU,_1cV,_1cW,_1cX,_1cY,_1cZ,_1d0,_1d1){var _1d2=new T(function(){return B(_1b9(_1d1));}),_1d3=function(_1d4,_1d5){return new F(function(){return _af(_1cW,_1cV,_1cU,_1cS,_1cT,_1cQ,_1cR,_1d4);});},_1d6=new T(function(){return B(_16Q(_1bQ,_14N,new T(function(){return B(_16J(_1d3));}),new T(function(){return B(_17U(_1d3));}),_1cW,_1cV,_1cU,_1cT,_1cS,_1cQ,_1cR));}),_1d7=function(_1d8,_1d9){return new F(function(){return _181(_1d0,_1cY,_1cZ,_1cT,_1cW,_1cS,_1cV,_1cU,_1cQ,_1cR,_1d8,_1d9);});};return function(_1da,_1db,_1dc){var _1dd=new T(function(){return B(A(_1cX,[_1dc]));});return [0,new T(function(){return B(_19D(function(_1de,_1df){var _1dg=B(A(new T(function(){return B(_1bC(_1cQ,_1cR,_1cS,_1cT,_1cU,_1cV,_1cW));}),[new T(function(){var _1dh=E(E(_1df)[1]);if(!_1dh[0]){var _1di=[0];}else{var _1dj=E(_1dh[1]),_1di=_1dj[0]==0?[0]:[1,new T(function(){var _1dk=E(_1dj[1]);return _1dk[0]==0?E(_1b8):B(_10R(new T(function(){var _1dl=E(B(A(_1d2,[_1da]))[2]);if(!_1dl[0]){var _1dm=E(_1bm);}else{var _1dn=E(_1dl[1]);if(!_1dn[0]){var _1do=E(_1bm);}else{var _1dp=_1dn[1];if(!E(_1dn[2])[0]){var _1dq=B(_17f(_1d7,_1d6,_1dp,_1dd));if(!_1dq[0]){var _1dr=B(_17f(_1d7,_1d6,_1dd,_1dp));if(!_1dr[0]){var _1ds=B(_1d7(_1dp,_1dd));if(!_1ds[0]){var _1dt=[0];}else{var _1du=B(_1ct([0,_1d7,_1d6,function(_1dv,_1dw){return new F(function(){return _17f(_1d7,_1d6,_1dv,_1dw);});},_1bn],_1ds[1])),_1dt=_1du[0]==0?E(_1du[1]):[0];}var _1dx=_1dt;}else{var _1dy=E(_1dr[1]),_1dz=E(_1dy[1]),_1dA=E(_1dz[2]),_1dB=B(_1aN(_1dz[1],_1dA[1],_1dA[2],_1dA[3],_1dA[4],_1dA[5],_1dA[6],_1dz[3],_1dz[4],_1dy[2],_1dy[3])),_1dx=_1dB[0]==0?E(_1dB[1]):[0];}var _1dC=_1dx;}else{var _1dD=E(_1dq[1]),_1dE=E(_1dD[1]),_1dF=E(_1dE[2]),_1dG=B(_1aN(_1dE[1],_1dF[1],_1dF[2],_1dF[3],_1dF[4],_1dF[5],_1dF[6],_1dE[3],_1dE[4],_1dD[2],_1dD[3])),_1dC=_1dG[0]==0?E(_1dG[1]):[0];}var _1dH=_1dC;}else{var _1dH=E(_1bm);}var _1do=_1dH;}var _1dm=_1do;}var _1dI=_1dm;return _1dI;}),_1dk[1]));})];}var _1dJ=_1di;return _1dJ;}),_1de])),_1dK=_1dg[2],_1dL=E(E(_1df)[1]);if(!_1dL[0]){return E(_1b2);}else{var _1dM=E(_1dL[1]);if(!_1dM[0]){return E(_1dL[2])[0]==0?E(_1dg):E(_1b2);}else{var _1dN=E(_1dg[1]);if(!_1dN[0]){return [0,_9,_1dK];}else{var _1dO=E(_1dN[1]);if(!_1dO[0]){return E(_1dg);}else{var _1dP=_1dO[1],_1dQ=new T(function(){return [0,B(_16x(_1dM[1],0))];});return [0,[1,[1,new T(function(){return B(_1c1(_1dQ,_1dP));})],[1,[1,new T(function(){return B(_1bg(_1dQ,_1dP));})],_1dN[2]]],_1dK];}}}}},_1db,new T(function(){return B(A(new T(function(){return B(_1bR(_1d1));}),[_1da]));},1)));}),[0,new T(function(){return E(B(A(_1d2,[_1da]))[1]);}),[1,[1,_1dd,_9]]]];};},_1dR=function(_1dS,_1dT){return [0];},_1dU=function(_1dV,_1dW,_1dX,_1dY,_1dZ,_1e0,_1e1,_1e2,_1e3,_1e4,_1e5){var _1e6=new T(function(){return B(_1cP(_1dV,_1dW,_1dX,_1dY,_1dZ,_1e0,_1e1,_1e2,_1e3,_1e4,_1e5,_13A));}),_1e7=new T(function(){return B(_1ap(_1e5,_1e3,_1e4,_1dY,_1e1,_1dX,_1e0,_1dZ,_1dV,_1dW));}),_1e8=[0,_1e7,new T(function(){return B(_13j(_1bQ,_14N,new T(function(){return B(_ZH(new T(function(){return B(_10p(new T(function(){return B(_105(_1e1,_1e0,_1dZ,_1dY,_1dX,_1dV,_1dW));})));})));}),new T(function(){return B(_148(new T(function(){return B(_14B(new T(function(){return B(_b9(_1e1,_1e0,_1dZ,_1dY,_1dX,_1dV,_1dW));})));})));}),_1e1,_1e0,_1dZ,_1dY,_1dX,_1dV,_1dW));}),_1dR,_1];return function(_1e9,_1ea,_1eb){var _1ec=B(_7u(function(_1ed){var _1ee=B(A(_1e7,[new T(function(){return B(A(_1e6,[_1ed,_1ea,_1eb]));}),_1ed]));return _1ee[0]==0?false:B(_1ct(_1e8,_1ee[1]))[0]==0?true:false;},E(_1e9)[1]));if(!_1ec[0]){return [0];}else{var _1ef=_1ec[1],_1eg=new T(function(){return B(A(_1e6,[_1ef,_1ea,_1eb]));}),_1eh=B(A(_1e7,[_1ef,_1eg]));if(!_1eh[0]){return [0];}else{var _1ei=B(_1ct(_1e8,_1eh[1]));if(!_1ei[0]){var _1ej=_1ei[1];return [1,new T(function(){var _1ek=E(E(_1eg)[2]);return [0,new T(function(){return B(_7X(function(_1el){return new F(function(){return _11o(_1ej,_1el);});},_1ek[1]));}),new T(function(){return B(_11o(_1ej,_1ek[2]));})];})];}else{return [0];}}}};},_1em=[1],_1en=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1eo=function(_1ep){return new F(function(){return err(_1en);});},_1eq=new T(function(){return B(_1eo(_));}),_1er=function(_1es,_1et,_1eu){var _1ev=E(_1eu);if(!_1ev[0]){var _1ew=_1ev[1],_1ex=E(_1et);if(!_1ex[0]){var _1ey=_1ex[1],_1ez=_1ex[2];if(_1ey<=(imul(3,_1ew)|0)){return [0,(1+_1ey|0)+_1ew|0,E(E(_1es)),E(_1ex),E(_1ev)];}else{var _1eA=E(_1ex[3]);if(!_1eA[0]){var _1eB=_1eA[1],_1eC=E(_1ex[4]);if(!_1eC[0]){var _1eD=_1eC[1],_1eE=_1eC[2],_1eF=_1eC[3];if(_1eD>=(imul(2,_1eB)|0)){var _1eG=function(_1eH){var _1eI=E(_1eC[4]);return _1eI[0]==0?[0,(1+_1ey|0)+_1ew|0,E(_1eE),E([0,(1+_1eB|0)+_1eH|0,E(_1ez),E(_1eA),E(_1eF)]),E([0,(1+_1ew|0)+_1eI[1]|0,E(E(_1es)),E(_1eI),E(_1ev)])]:[0,(1+_1ey|0)+_1ew|0,E(_1eE),E([0,(1+_1eB|0)+_1eH|0,E(_1ez),E(_1eA),E(_1eF)]),E([0,1+_1ew|0,E(E(_1es)),E(_1em),E(_1ev)])];},_1eJ=E(_1eF);return _1eJ[0]==0?B(_1eG(_1eJ[1])):B(_1eG(0));}else{return [0,(1+_1ey|0)+_1ew|0,E(_1ez),E(_1eA),E([0,(1+_1ew|0)+_1eD|0,E(E(_1es)),E(_1eC),E(_1ev)])];}}else{return E(_1eq);}}else{return E(_1eq);}}}else{return [0,1+_1ew|0,E(E(_1es)),E(_1em),E(_1ev)];}}else{var _1eK=E(_1et);if(!_1eK[0]){var _1eL=_1eK[1],_1eM=_1eK[2],_1eN=_1eK[4],_1eO=E(_1eK[3]);if(!_1eO[0]){var _1eP=_1eO[1],_1eQ=E(_1eN);if(!_1eQ[0]){var _1eR=_1eQ[1],_1eS=_1eQ[2],_1eT=_1eQ[3];if(_1eR>=(imul(2,_1eP)|0)){var _1eU=function(_1eV){var _1eW=E(_1eQ[4]);return _1eW[0]==0?[0,1+_1eL|0,E(_1eS),E([0,(1+_1eP|0)+_1eV|0,E(_1eM),E(_1eO),E(_1eT)]),E([0,1+_1eW[1]|0,E(E(_1es)),E(_1eW),E(_1em)])]:[0,1+_1eL|0,E(_1eS),E([0,(1+_1eP|0)+_1eV|0,E(_1eM),E(_1eO),E(_1eT)]),E([0,1,E(E(_1es)),E(_1em),E(_1em)])];},_1eX=E(_1eT);return _1eX[0]==0?B(_1eU(_1eX[1])):B(_1eU(0));}else{return [0,1+_1eL|0,E(_1eM),E(_1eO),E([0,1+_1eR|0,E(E(_1es)),E(_1eQ),E(_1em)])];}}else{return [0,3,E(_1eM),E(_1eO),E([0,1,E(E(_1es)),E(_1em),E(_1em)])];}}else{var _1eY=E(_1eN);return _1eY[0]==0?[0,3,E(_1eY[2]),E([0,1,E(_1eM),E(_1em),E(_1em)]),E([0,1,E(E(_1es)),E(_1em),E(_1em)])]:[0,2,E(E(_1es)),E(_1eK),E(_1em)];}}else{return [0,1,E(E(_1es)),E(_1em),E(_1em)];}}},_1eZ=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_1f0=function(_1f1){return new F(function(){return err(_1eZ);});},_1f2=new T(function(){return B(_1f0(_));}),_1f3=function(_1f4,_1f5,_1f6){var _1f7=E(_1f5);if(!_1f7[0]){var _1f8=_1f7[1],_1f9=E(_1f6);if(!_1f9[0]){var _1fa=_1f9[1],_1fb=_1f9[2];if(_1fa<=(imul(3,_1f8)|0)){return [0,(1+_1f8|0)+_1fa|0,E(E(_1f4)),E(_1f7),E(_1f9)];}else{var _1fc=E(_1f9[3]);if(!_1fc[0]){var _1fd=_1fc[1],_1fe=_1fc[2],_1ff=_1fc[3],_1fg=E(_1f9[4]);if(!_1fg[0]){var _1fh=_1fg[1];if(_1fd>=(imul(2,_1fh)|0)){var _1fi=function(_1fj){var _1fk=E(_1f4),_1fl=E(_1fc[4]);return _1fl[0]==0?[0,(1+_1f8|0)+_1fa|0,E(_1fe),E([0,(1+_1f8|0)+_1fj|0,E(_1fk),E(_1f7),E(_1ff)]),E([0,(1+_1fh|0)+_1fl[1]|0,E(_1fb),E(_1fl),E(_1fg)])]:[0,(1+_1f8|0)+_1fa|0,E(_1fe),E([0,(1+_1f8|0)+_1fj|0,E(_1fk),E(_1f7),E(_1ff)]),E([0,1+_1fh|0,E(_1fb),E(_1em),E(_1fg)])];},_1fm=E(_1ff);return _1fm[0]==0?B(_1fi(_1fm[1])):B(_1fi(0));}else{return [0,(1+_1f8|0)+_1fa|0,E(_1fb),E([0,(1+_1f8|0)+_1fd|0,E(E(_1f4)),E(_1f7),E(_1fc)]),E(_1fg)];}}else{return E(_1f2);}}else{return E(_1f2);}}}else{return [0,1+_1f8|0,E(E(_1f4)),E(_1f7),E(_1em)];}}else{var _1fn=E(_1f6);if(!_1fn[0]){var _1fo=_1fn[1],_1fp=_1fn[2],_1fq=_1fn[4],_1fr=E(_1fn[3]);if(!_1fr[0]){var _1fs=_1fr[1],_1ft=_1fr[2],_1fu=_1fr[3],_1fv=E(_1fq);if(!_1fv[0]){var _1fw=_1fv[1];if(_1fs>=(imul(2,_1fw)|0)){var _1fx=function(_1fy){var _1fz=E(_1f4),_1fA=E(_1fr[4]);return _1fA[0]==0?[0,1+_1fo|0,E(_1ft),E([0,1+_1fy|0,E(_1fz),E(_1em),E(_1fu)]),E([0,(1+_1fw|0)+_1fA[1]|0,E(_1fp),E(_1fA),E(_1fv)])]:[0,1+_1fo|0,E(_1ft),E([0,1+_1fy|0,E(_1fz),E(_1em),E(_1fu)]),E([0,1+_1fw|0,E(_1fp),E(_1em),E(_1fv)])];},_1fB=E(_1fu);return _1fB[0]==0?B(_1fx(_1fB[1])):B(_1fx(0));}else{return [0,1+_1fo|0,E(_1fp),E([0,1+_1fs|0,E(E(_1f4)),E(_1em),E(_1fr)]),E(_1fv)];}}else{return [0,3,E(_1ft),E([0,1,E(E(_1f4)),E(_1em),E(_1em)]),E([0,1,E(_1fp),E(_1em),E(_1em)])];}}else{var _1fC=E(_1fq);return _1fC[0]==0?[0,3,E(_1fp),E([0,1,E(E(_1f4)),E(_1em),E(_1em)]),E(_1fC)]:[0,2,E(E(_1f4)),E(_1em),E(_1fn)];}}else{return [0,1,E(E(_1f4)),E(_1em),E(_1em)];}}},_1fD=function(_1fE){return [0,1,E(E(_1fE)),E(_1em),E(_1em)];},_1fF=function(_1fG,_1fH){var _1fI=E(_1fH);if(!_1fI[0]){return new F(function(){return _1er(_1fI[2],B(_1fF(_1fG,_1fI[3])),_1fI[4]);});}else{return new F(function(){return _1fD(_1fG);});}},_1fJ=function(_1fK,_1fL){var _1fM=E(_1fL);if(!_1fM[0]){return new F(function(){return _1f3(_1fM[2],_1fM[3],B(_1fJ(_1fK,_1fM[4])));});}else{return new F(function(){return _1fD(_1fK);});}},_1fN=function(_1fO,_1fP,_1fQ,_1fR,_1fS){return new F(function(){return _1f3(_1fQ,_1fR,B(_1fJ(_1fO,_1fS)));});},_1fT=function(_1fU,_1fV,_1fW,_1fX,_1fY){return new F(function(){return _1er(_1fW,B(_1fF(_1fU,_1fX)),_1fY);});},_1fZ=function(_1g0,_1g1,_1g2,_1g3,_1g4,_1g5){var _1g6=E(_1g1);if(!_1g6[0]){var _1g7=_1g6[1],_1g8=_1g6[2],_1g9=_1g6[3],_1ga=_1g6[4];if((imul(3,_1g7)|0)>=_1g2){if((imul(3,_1g2)|0)>=_1g7){return [0,(_1g7+_1g2|0)+1|0,E(E(_1g0)),E(_1g6),E([0,_1g2,E(_1g3),E(_1g4),E(_1g5)])];}else{return new F(function(){return _1f3(_1g8,_1g9,B(_1fZ(_1g0,_1ga,_1g2,_1g3,_1g4,_1g5)));});}}else{return new F(function(){return _1er(_1g3,B(_1gb(_1g0,_1g7,_1g8,_1g9,_1ga,_1g4)),_1g5);});}}else{return new F(function(){return _1fT(_1g0,_1g2,_1g3,_1g4,_1g5);});}},_1gb=function(_1gc,_1gd,_1ge,_1gf,_1gg,_1gh){var _1gi=E(_1gh);if(!_1gi[0]){var _1gj=_1gi[1],_1gk=_1gi[2],_1gl=_1gi[3],_1gm=_1gi[4];if((imul(3,_1gd)|0)>=_1gj){if((imul(3,_1gj)|0)>=_1gd){return [0,(_1gd+_1gj|0)+1|0,E(E(_1gc)),E([0,_1gd,E(_1ge),E(_1gf),E(_1gg)]),E(_1gi)];}else{return new F(function(){return _1f3(_1ge,_1gf,B(_1fZ(_1gc,_1gg,_1gj,_1gk,_1gl,_1gm)));});}}else{return new F(function(){return _1er(_1gk,B(_1gb(_1gc,_1gd,_1ge,_1gf,_1gg,_1gl)),_1gm);});}}else{return new F(function(){return _1fN(_1gc,_1gd,_1ge,_1gf,_1gg);});}},_1gn=function(_1go,_1gp,_1gq){var _1gr=E(_1gp);if(!_1gr[0]){var _1gs=_1gr[1],_1gt=_1gr[2],_1gu=_1gr[3],_1gv=_1gr[4],_1gw=E(_1gq);if(!_1gw[0]){var _1gx=_1gw[1],_1gy=_1gw[2],_1gz=_1gw[3],_1gA=_1gw[4];if((imul(3,_1gs)|0)>=_1gx){if((imul(3,_1gx)|0)>=_1gs){return [0,(_1gs+_1gx|0)+1|0,E(E(_1go)),E(_1gr),E(_1gw)];}else{return new F(function(){return _1f3(_1gt,_1gu,B(_1fZ(_1go,_1gv,_1gx,_1gy,_1gz,_1gA)));});}}else{return new F(function(){return _1er(_1gy,B(_1gb(_1go,_1gs,_1gt,_1gu,_1gv,_1gz)),_1gA);});}}else{return new F(function(){return _1fN(_1go,_1gs,_1gt,_1gu,_1gv);});}}else{return new F(function(){return _1fF(_1go,_1gq);});}},_1gB=function(_1gC,_1gD,_1gE,_1gF){var _1gG=E(_1gF);if(!_1gG[0]){var _1gH=new T(function(){var _1gI=B(_1gB(_1gG[1],_1gG[2],_1gG[3],_1gG[4]));return [0,_1gI[1],_1gI[2]];});return [0,new T(function(){return E(E(_1gH)[1]);}),new T(function(){return B(_1er(_1gD,_1gE,E(_1gH)[2]));})];}else{return [0,_1gD,_1gE];}},_1gJ=function(_1gK,_1gL,_1gM,_1gN){var _1gO=E(_1gM);if(!_1gO[0]){var _1gP=new T(function(){var _1gQ=B(_1gJ(_1gO[1],_1gO[2],_1gO[3],_1gO[4]));return [0,_1gQ[1],_1gQ[2]];});return [0,new T(function(){return E(E(_1gP)[1]);}),new T(function(){return B(_1f3(_1gL,E(_1gP)[2],_1gN));})];}else{return [0,_1gL,_1gN];}},_1gR=function(_1gS,_1gT){var _1gU=E(_1gS);if(!_1gU[0]){var _1gV=_1gU[1],_1gW=E(_1gT);if(!_1gW[0]){var _1gX=_1gW[1];if(_1gV<=_1gX){var _1gY=B(_1gJ(_1gX,_1gW[2],_1gW[3],_1gW[4]));return new F(function(){return _1er(_1gY[1],_1gU,_1gY[2]);});}else{var _1gZ=B(_1gB(_1gV,_1gU[2],_1gU[3],_1gU[4]));return new F(function(){return _1f3(_1gZ[1],_1gZ[2],_1gW);});}}else{return E(_1gU);}}else{return E(_1gT);}},_1h0=function(_1h1,_1h2,_1h3,_1h4,_1h5){var _1h6=E(_1h1);if(!_1h6[0]){var _1h7=_1h6[1],_1h8=_1h6[2],_1h9=_1h6[3],_1ha=_1h6[4];if((imul(3,_1h7)|0)>=_1h2){if((imul(3,_1h2)|0)>=_1h7){return new F(function(){return _1gR(_1h6,[0,_1h2,E(_1h3),E(_1h4),E(_1h5)]);});}else{return new F(function(){return _1f3(_1h8,_1h9,B(_1h0(_1ha,_1h2,_1h3,_1h4,_1h5)));});}}else{return new F(function(){return _1er(_1h3,B(_1hb(_1h7,_1h8,_1h9,_1ha,_1h4)),_1h5);});}}else{return [0,_1h2,E(_1h3),E(_1h4),E(_1h5)];}},_1hb=function(_1hc,_1hd,_1he,_1hf,_1hg){var _1hh=E(_1hg);if(!_1hh[0]){var _1hi=_1hh[1],_1hj=_1hh[2],_1hk=_1hh[3],_1hl=_1hh[4];if((imul(3,_1hc)|0)>=_1hi){if((imul(3,_1hi)|0)>=_1hc){return new F(function(){return _1gR([0,_1hc,E(_1hd),E(_1he),E(_1hf)],_1hh);});}else{return new F(function(){return _1f3(_1hd,_1he,B(_1h0(_1hf,_1hi,_1hj,_1hk,_1hl)));});}}else{return new F(function(){return _1er(_1hj,B(_1hb(_1hc,_1hd,_1he,_1hf,_1hk)),_1hl);});}}else{return [0,_1hc,E(_1hd),E(_1he),E(_1hf)];}},_1hm=function(_1hn,_1ho){var _1hp=E(_1hn);if(!_1hp[0]){var _1hq=_1hp[1],_1hr=_1hp[2],_1hs=_1hp[3],_1ht=_1hp[4],_1hu=E(_1ho);if(!_1hu[0]){var _1hv=_1hu[1],_1hw=_1hu[2],_1hx=_1hu[3],_1hy=_1hu[4];if((imul(3,_1hq)|0)>=_1hv){if((imul(3,_1hv)|0)>=_1hq){return new F(function(){return _1gR(_1hp,_1hu);});}else{return new F(function(){return _1f3(_1hr,_1hs,B(_1h0(_1ht,_1hv,_1hw,_1hx,_1hy)));});}}else{return new F(function(){return _1er(_1hw,B(_1hb(_1hq,_1hr,_1hs,_1ht,_1hx)),_1hy);});}}else{return E(_1hp);}}else{return E(_1ho);}},_1hz=function(_1hA,_1hB){var _1hC=E(_1hB);if(!_1hC[0]){var _1hD=_1hC[2],_1hE=_1hC[3],_1hF=_1hC[4];if(!B(A(_1hA,[_1hD]))){return new F(function(){return _1hm(B(_1hz(_1hA,_1hE)),B(_1hz(_1hA,_1hF)));});}else{return new F(function(){return _1gn(_1hD,B(_1hz(_1hA,_1hE)),B(_1hz(_1hA,_1hF)));});}}else{return [1];}},_1hG=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_1hH=new T(function(){return B(err(_1hG));}),_1hI=function(_1hJ,_1hK,_1hL,_1hM){while(1){var _1hN=E(_1hL);if(!_1hN[0]){_1hJ=_1hN[1];_1hK=_1hN[2];_1hL=_1hN[3];_1hM=_1hN[4];continue;}else{return E(_1hK);}}},_1hO=function(_1hP,_1hQ){var _1hR=B(_1hz(function(_1hS){return new F(function(){return _lj(E(_1hS)[2],_1hP);});},_1hQ));if(!_1hR[0]){var _1hT=E(_1hR[3]);return _1hT[0]==0?B(_1hI(_1hT[1],_1hT[2],_1hT[3],_1hT[4])):E(_1hR[2]);}else{return E(_1hH);}},_1hU=[1,_9],_1hV=function(_1hW,_1hX,_1hY,_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9){var _1ia=E(_1i9);if(!_1ia[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_1i3,[_1i8]));}),_9]],_9],[1,[1,new T(function(){return B(A(_1i3,[_1i8]));}),_9]]]];}else{var _1ib=function(_1ic){var _1id=E(_1ic);if(!_1id[0]){return E(_1hU);}else{var _1ie=E(_1id[1]),_1if=B(_1hV(_1hW,_1hX,_1hY,_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1ie[1],_1ie[2]));if(!_1if[0]){return [0];}else{var _1ig=B(_1ib(_1id[2]));return _1ig[0]==0?[0]:[1,[1,_1if[1],_1ig[1]]];}}},_1ih=B(_1ib(_1ia[2]));return _1ih[0]==0?[0]:B(A(_1dU,[_1hW,_1hX,_1hY,_1hZ,_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,new T(function(){return B(_1hO(_1ia[1],_1i7));}),_1ih[1],_1i8]));}},_1ii=function(_1ij,_1ik,_1il,_1im,_1in,_1io,_1ip,_1iq,_1ir,_1is,_1it,_1iu,_1iv,_1iw,_1ix){var _1iy=E(_1ix);return new F(function(){return _1hV(_1ij,_1ik,_1il,_1im,_1in,_1io,_1ip,_1iq,_1ir,_1iu,_1iv,_1iw,_1iy[1],_1iy[2]);});},_1iz=function(_1iA){return new F(function(){return _db(_1iA,_9);});},_1iB=function(_1iC,_1iD){return _1iC<=B(_16x(_1iD,0))?[1,new T(function(){var _1iE=_1iC-1|0;if(_1iE>=0){var _1iF=B(_gp(B(_1iz(_1iD)),_1iE));}else{var _1iF=E(_gm);}var _1iG=_1iF,_1iH=_1iG;return _1iH;})]:[0];},_1iI=function(_1iJ,_1iK,_1iL){var _1iM=function(_1iN){return _1iN<=B(_16x(_1iL,0))?[1,[0,new T(function(){var _1iO=_1iJ-1|0;if(_1iO>=0){var _1iP=B(_gp(B(_1iz(_1iL)),_1iO));}else{var _1iP=E(_gm);}var _1iQ=_1iP,_1iR=_1iQ;return _1iR;}),new T(function(){var _1iS=_1iK-1|0;if(_1iS>=0){var _1iT=B(_gp(B(_1iz(_1iL)),_1iS));}else{var _1iT=E(_gm);}var _1iU=_1iT,_1iV=_1iU;return _1iV;})]]:[0];};return _1iJ>_1iK?B(_1iM(_1iJ)):B(_1iM(_1iK));},_1iW=[0],_1iX=new T(function(){return B(unCStr("depends on unjustified lines"));}),_1iY=new T(function(){return B(unCStr("unavailable lines"));}),_1iZ=new T(function(){return B(unCStr("wrong number of premises"));}),_1j0=new T(function(){return B(unCStr("Impossible Error 1"));}),_1j1=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1j2=new T(function(){return B(unCStr("PR"));}),_1j3=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1j4=function(_1j5,_1j6,_1j7,_1j8,_1j9,_1ja){var _1jb=function(_1jc){var _1jd=B(A(_1j8,[_1j6]));if(!_1jd[0]){return [0,[1,_1j3,_1j9],[1,_28,_1ja]];}else{var _1je=E(_1jd[1]);if(!_1je[0]){switch(E(E(_1je[1])[1])){case 1:var _1jf=E(_1j7);if(!_1jf[0]){return [0,[1,_1iZ,_1j9],[1,_28,_1ja]];}else{if(!E(_1jf[2])[0]){var _1jg=B(_1iB(E(_1jf[1])[1],_1ja));if(!_1jg[0]){return [0,[1,_1iY,_1j9],[1,_28,_1ja]];}else{var _1jh=E(_1jg[1]);return _1jh[0]==0?[0,[1,_1iX,_1j9],[1,_28,_1ja]]:[0,[1,_9,_1j9],[1,[1,[0,_1j5,[1,_1j6,[1,_1jh[1],_9]]]],_1ja]];}}else{return [0,[1,_1iZ,_1j9],[1,_28,_1ja]];}}break;case 2:var _1ji=E(_1j7);if(!_1ji[0]){return [0,[1,_1iZ,_1j9],[1,_28,_1ja]];}else{var _1jj=E(_1ji[2]);if(!_1jj[0]){return [0,[1,_1iZ,_1j9],[1,_28,_1ja]];}else{if(!E(_1jj[2])[0]){var _1jk=B(_1iI(E(_1ji[1])[1],E(_1jj[1])[1],_1ja));if(!_1jk[0]){return [0,[1,_1iY,_1j9],[1,_28,_1ja]];}else{var _1jl=E(_1jk[1]),_1jm=E(_1jl[1]);if(!_1jm[0]){return [0,[1,_1iX,_1j9],[1,_28,_1ja]];}else{var _1jn=E(_1jl[2]);return _1jn[0]==0?[0,[1,_1iX,_1j9],[1,_28,_1ja]]:[0,[1,_9,_1j9],[1,[1,[0,_1j5,[1,_1j6,[1,_1jm[1],[1,_1jn[1],_9]]]]],_1ja]];}}}else{return [0,[1,_1iZ,_1j9],[1,_28,_1ja]];}}}break;default:return [0,[1,_1j0,_1j9],[1,_28,_1ja]];}}else{return [0,[1,_1j1,_1j9],[1,_28,_1ja]];}}};return !B(_lj(_1j6,_1j2))?B(_1jb(_)):E(_1j7)[0]==0?[0,[1,_9,_1j9],[1,[1,[0,_1j5,_1iW]],_1ja]]:B(_1jb(_));},_1jo=new T(function(){return B(unCStr("depends on an unjustified line"));}),_1jp=new T(function(){return B(unCStr("unavailable line"));}),_1jq=function(_1jr,_1js,_1jt,_1ju){return E(B(_1jv(_1jr,_1js,[1,_9,_1jt],[1,_28,_1ju]))[2]);},_1jw=function(_1jx,_1jy,_1jz,_1jA,_1jB,_1jC,_1jD,_1jE){var _1jF=B(_1iI(_1jA,_1jB,B(_1jq(_1jx,_1jy,_1jD,_1jE))));if(!_1jF[0]){return new F(function(){return _1jv(_1jx,_1jy,[1,_1jp,_1jD],[1,_28,_1jE]);});}else{var _1jG=E(_1jF[1]),_1jH=E(_1jG[1]);if(!_1jH[0]){return new F(function(){return _1jv(_1jx,_1jy,[1,_1jo,_1jD],[1,_28,_1jE]);});}else{var _1jI=E(_1jG[2]);return _1jI[0]==0?B(_1jv(_1jx,_1jy,[1,_1jo,_1jD],[1,_28,_1jE])):B(_1jv(_1jx,_1jy,[1,_9,_1jD],[1,[1,[0,_1jz,[1,_1jC,[1,_1jH[1],[1,_1jI[1],_9]]]]],_1jE]));}}},_1jJ=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1jK=function(_1jL,_1jM,_1jN,_1jO,_1jP,_1jQ,_1jR){var _1jS=E(_1jP);if(!_1jS[0]){return new F(function(){return _1jv(_1jL,_1jM,[1,_1jJ,_1jQ],[1,_28,_1jR]);});}else{var _1jT=E(_1jS[2]);if(!_1jT[0]){return new F(function(){return _1jv(_1jL,_1jM,[1,_1jJ,_1jQ],[1,_28,_1jR]);});}else{if(!E(_1jT[2])[0]){return new F(function(){return _1jw(_1jL,_1jM,_1jN,E(_1jS[1])[1],E(_1jT[1])[1],_1jO,_1jQ,_1jR);});}else{return new F(function(){return _1jv(_1jL,_1jM,[1,_1jJ,_1jQ],[1,_28,_1jR]);});}}}},_1jU=function(_1jV,_1jW,_1jX){return [0,[1,_9,_1jW],[1,_28,new T(function(){var _1jY=B(_16x(_1jW,0))-E(_1jV)[1]|0,_1jZ=new T(function(){return _1jY>=0?B(_1bb(_1jY,_1jX)):E(_1jX);});if(_1jY>0){var _1k0=function(_1k1,_1k2){var _1k3=E(_1k1);return _1k3[0]==0?E(_1jZ):_1k2>1?[1,_28,new T(function(){return B(_1k0(_1k3[2],_1k2-1|0));})]:E([1,_28,_1jZ]);},_1k4=B(_1k0(_1jX,_1jY));}else{var _1k4=E(_1jZ);}var _1k5=_1k4,_1k6=_1k5,_1k7=_1k6,_1k8=_1k7;return _1k8;})]];},_1k9=function(_1ka,_1kb,_1kc,_1kd,_1ke,_1kf,_1kg){var _1kh=new T(function(){return E(B(_1jv(_1ka,_1kb,[1,_9,_1kf],[1,_28,_1kg]))[2]);});if(_1kd<=B(_16x(_1kh,0))){var _1ki=_1kd-1|0;if(_1ki>=0){var _1kj=B(_gp(B(_1iz(_1kh)),_1ki));return _1kj[0]==0?B(_1jv(_1ka,_1kb,[1,_1jo,_1kf],[1,_28,_1kg])):B(_1jv(_1ka,_1kb,[1,_9,_1kf],[1,[1,[0,_1kc,[1,_1ke,[1,_1kj[1],_9]]]],_1kg]));}else{return E(_gm);}}else{return new F(function(){return _1jv(_1ka,_1kb,[1,_1jp,_1kf],[1,_28,_1kg]);});}},_1kk=function(_1kl,_1km,_1kn,_1ko,_1kp,_1kq,_1kr){var _1ks=E(_1kp);if(!_1ks[0]){return new F(function(){return _1jv(_1kl,_1km,[1,_1jJ,_1kq],[1,_28,_1kr]);});}else{if(!E(_1ks[2])[0]){return new F(function(){return _1k9(_1kl,_1km,_1kn,E(_1ks[1])[1],_1ko,_1kq,_1kr);});}else{return new F(function(){return _1jv(_1kl,_1km,[1,_1jJ,_1kq],[1,_28,_1kr]);});}}},_1kt=new T(function(){return B(unCStr("Open Subproof"));}),_1ku=new T(function(){return B(unCStr("Impossible Error 2"));}),_1kv=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1kw=new T(function(){return B(unCStr("SHOW"));}),_1kx=function(_1ky,_1kz,_1kA,_1kB,_1kC,_1kD,_1kE){if(!B(_lj(_1kz,_1kw))){var _1kF=B(A(_1kB,[_1kz]));if(!_1kF[0]){return [0,[1,_1j3,_1kD],[1,_28,_1kE]];}else{var _1kG=E(_1kF[1]);if(!_1kG[0]){return [0,[1,_1kv,_1kD],[1,_28,_1kE]];}else{switch(E(E(_1kG[1])[1])){case 1:var _1kH=B(_1kk(_1kC,_1kB,_1ky,_1kz,_1kA,_1kD,_1kE));return new F(function(){return _1jU(new T(function(){return [0,B(_16x(_1kD,0))+1|0];},1),_1kH[1],_1kH[2]);});break;case 2:var _1kI=B(_1jK(_1kC,_1kB,_1ky,_1kz,_1kA,_1kD,_1kE));return new F(function(){return _1jU(new T(function(){return [0,B(_16x(_1kD,0))+1|0];},1),_1kI[1],_1kI[2]);});break;default:return [0,[1,_1ku,_1kD],[1,_28,_1kE]];}}}}else{var _1kJ=B(_1jv(_1kC,_1kB,[1,_1kt,_1kD],[1,_28,_1kE]));return new F(function(){return _1jU(new T(function(){return [0,B(_16x(_1kD,0))+1|0];},1),_1kJ[1],_1kJ[2]);});}},_1kK=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1kL=new T(function(){return B(unCStr("incomplete line"));}),_1kM=function(_1kN,_1kO,_1kP,_1kQ,_1kR){var _1kS=E(_1kN);if(!_1kS[0]){return E(_1kO)[0]==0?[0,[1,_1kL,_1kQ],[1,_28,_1kR]]:[0,[1,_1kK,_1kQ],[1,_28,_1kR]];}else{var _1kT=_1kS[1],_1kU=E(_1kO);if(!_1kU[0]){var _1kV=E(_1kT);return new F(function(){return _1j4(_1kV[1],_1kV[2],_1kV[3],_1kP,_1kQ,_1kR);});}else{var _1kW=E(_1kT);return new F(function(){return _1kx(_1kW[1],_1kW[2],_1kW[3],_1kP,_1kU,_1kQ,_1kR);});}}},_1jv=function(_1kX,_1kY,_1kZ,_1l0){return new F(function(){return (function(_1l1,_1l2,_1l3){while(1){var _1l4=E(_1l3);if(!_1l4[0]){return [0,_1l1,_1l2];}else{var _1l5=E(_1l4[1]),_1l6=B(_1kM(_1l5[1],_1l5[2],_1kY,_1l1,_1l2));_1l1=_1l6[1];_1l2=_1l6[2];_1l3=_1l4[2];continue;}}})(_1kZ,_1l0,_1kX);});},_1l7=function(_1l8,_1l9){while(1){var _1la=E(_1l9);if(!_1la[0]){return true;}else{if(!B(A(_1l8,[_1la[1]]))){return false;}else{_1l9=_1la[2];continue;}}}},_1lb=[0,666],_1lc=[0,_,_1lb],_1ld=[1,_1lc],_1le=[0,_1ld,_1iW],_1lf=function(_1lg){return new F(function(){return _lj(_1lg,_9);});},_1lh=function(_1li,_1lj){var _1lk=B(_1jv(_1li,_1lj,_9,_9)),_1ll=_1lk[1];return !B(_1l7(_1lf,_1ll))?[0,_1ll]:[1,new T(function(){var _1lm=B(_16x(_1li,0))-1|0;if(_1lm>=0){var _1ln=B(_gp(B(_db(_1lk[2],_9)),_1lm)),_1lo=_1ln[0]==0?E(_1le):E(_1ln[1]);}else{var _1lo=E(_gm);}var _1lp=_1lo,_1lq=_1lp,_1lr=_1lq;return _1lr;})];},_1ls=function(_1lt,_){return _1lt;},_1lu=function(_1lv){var _1lw=E(_1lv);return _1lw[0]==0?E(_1ls):function(_1lx,_){var _1ly=B(A(new T(function(){var _1lz=E(_1lw[1]);return B(_1lA(_1lz[1],_1lz[2]));}),[_1lx,_])),_1lB=_1ly,_1lC=B(A(new T(function(){return B(_1lu(_1lw[2]));}),[_1lx,_])),_1lD=_1lC;return _1lx;};},_1lE=function(_1lF,_1lG){return function(_1lH,_){var _1lI=B(A(new T(function(){var _1lJ=E(_1lF);return B(_1lA(_1lJ[1],_1lJ[2]));}),[_1lH,_])),_1lK=_1lI,_1lL=B(A(new T(function(){return B(_1lu(_1lG));}),[_1lH,_])),_1lM=_1lL;return _1lH;};},_1lN=function(_1lO,_1lP){return new F(function(){return _F(0,E(_1lO)[1],_1lP);});},_1lQ=function(_1lR){return function(_m0,_19A){return new F(function(){return _56(new T(function(){return B(_2T(_1lN,_1lR,_9));}),_m0,_19A);});};},_1lS=function(_1lT){return function(_m0,_19A){return new F(function(){return _56(new T(function(){return B(_UG(_Q,_u,_Q,_N,_Q,_Uw,_1lT,_UU));}),_m0,_19A);});};},_1lU=new T(function(){return B(unCStr("open"));}),_1lV=new T(function(){return B(unCStr("termination"));}),_1lW=new T(function(){return B(unCStr("closed"));}),_1lX=function(_1lY){var _1lZ=E(_1lY);return _1lZ[0]==0?E(_1ls):function(_1m0,_){var _1m1=B(A(new T(function(){var _1m2=E(_1lZ[1]);return B(_1lA(_1m2[1],_1m2[2]));}),[_1m0,_])),_1m3=_1m1,_1m4=B(A(new T(function(){return B(_1lX(_1lZ[2]));}),[_1m0,_])),_1m5=_1m4;return _1m0;};},_1m6=function(_1m7,_1m8){return function(_1m9,_){var _1ma=B(A(new T(function(){var _1mb=E(_1m7);return B(_1lA(_1mb[1],_1mb[2]));}),[_1m9,_])),_1mc=_1ma,_1md=B(A(new T(function(){return B(_1lX(_1m8));}),[_1m9,_])),_1me=_1md;return _1m9;};},_1mf=new T(function(){return B(unCStr("SHOW"));}),_1lA=function(_1mg,_1mh){var _1mi=E(_1mg);if(!_1mi[0]){return function(_m0,_19A){return new F(function(){return _bX(_56,_1mi[1],_m0,_19A);});};}else{var _1mj=E(_1mi[1]),_1mk=_1mj[1],_1ml=_1mj[2],_1mm=_1mj[3];if(!B(_lj(_1ml,_1mf))){var _1mn=E(_1mh);return _1mn[0]==0?function(_m0,_19A){return new F(function(){return _bX(_63,function(_1mo,_){var _1mp=B(_5T(_1lS,_1mk,_1mo,_)),_1mq=_1mp,_1mr=B(_5T(_63,function(_1ms,_){var _1mt=B(_5T(_56,_1ml,_1ms,_)),_1mu=_1mt,_1mv=B(_5T(_1lQ,_1mm,_1ms,_)),_1mw=_1mv;return _1ms;},_1mo,_)),_1mx=_1mr;return _1mo;},_m0,_19A);});}:function(_m0,_19A){return new F(function(){return _bX(_63,function(_1my,_){var _1mz=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UG(_Q,_u,_Q,_N,_Q,_Uw,_1mk,_UU));})));}),_1my,_)),_1mA=_1mz,_1mB=B(_bX(_63,function(_1mC,_){var _1mD=B(_5T(_63,new T(function(){return B(_1lE(_1mn[1],_1mn[2]));}),_1mC,_)),_1mE=_1mD,_1mF=B(_bX(_63,function(_1mG,_){var _1mH=B(_5T(_56,_9,_1mG,_)),_1mI=_1mH,_1mJ=B(A(_5d,[_5q,_1mI,_bP,_1lV,_])),_1mK=_1mJ,_1mL=B(_5T(_63,function(_1mM,_){var _1mN=B(_5T(_56,_1ml,_1mM,_)),_1mO=_1mN,_1mP=B(_5T(_1lQ,_1mm,_1mM,_)),_1mQ=_1mP;return _1mM;},_1mG,_)),_1mR=_1mL;return _1mG;},_1mC,_)),_1mS=_1mF;return _1mC;},_1my,_)),_1mT=_1mB,_1mU=B(A(_5d,[_5q,_1mT,_bP,_1lW,_])),_1mV=_1mU;return _1my;},_m0,_19A);});};}else{var _1mW=E(_1mh);return _1mW[0]==0?function(_m0,_19A){return new F(function(){return _bX(_63,function(_bB,_){return new F(function(){return _5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UG(_Q,_u,_Q,_N,_Q,_Uw,_1mk,_UU));})));}),_bB,_);});},_m0,_19A);});}:function(_m0,_19A){return new F(function(){return _bX(_63,function(_1mX,_){var _1mY=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_UG(_Q,_u,_Q,_N,_Q,_Uw,_1mk,_UU));})));}),_1mX,_)),_1mZ=_1mY,_1n0=B(_bX(_63,function(_bB,_){return new F(function(){return _5T(_63,new T(function(){return B(_1m6(_1mW[1],_1mW[2]));}),_bB,_);});},_1mX,_)),_1n1=_1n0,_1n2=B(A(_5d,[_5q,_1n1,_bP,_1lU,_])),_1n3=_1n2;return _1mX;},_m0,_19A);});};}}},_1n4=function(_1n5){var _1n6=E(_1n5);return _1n6[0]==0?E(_1ls):function(_1n7,_){var _1n8=B(A(new T(function(){var _1n9=E(_1n6[1]);return B(_1lA(_1n9[1],_1n9[2]));}),[_1n7,_])),_1na=_1n8,_1nb=B(A(new T(function(){return B(_1n4(_1n6[2]));}),[_1n7,_])),_1nc=_1nb;return _1n7;};},_1nd=[0,10],_1ne=[1,_1nd,_9],_1nf=function(_1ng,_1nh,_){var _1ni=jsCreateElem(toJSStr(E(_1ng))),_1nj=_1ni,_1nk=jsAppendChild(_1nj,E(_1nh)[1]);return [0,_1nj];},_1nl=function(_1nm,_1nn,_1no,_){var _1np=B(_1nf(_1nm,_1no,_)),_1nq=_1np,_1nr=B(A(_1nn,[_1nq,_])),_1ns=_1nr;return _1nq;},_1nt=new T(function(){return B(unCStr("()"));}),_1nu=new T(function(){return B(unCStr("GHC.Tuple"));}),_1nv=new T(function(){return B(unCStr("ghc-prim"));}),_1nw=new T(function(){var _1nx=hs_wordToWord64(2170319554),_1ny=_1nx,_1nz=hs_wordToWord64(26914641),_1nA=_1nz;return [0,_1ny,_1nA,[0,_1ny,_1nA,_1nv,_1nu,_1nt],_9];}),_1nB=function(_1nC){return E(_1nw);},_1nD=new T(function(){return B(unCStr("PerchM"));}),_1nE=new T(function(){return B(unCStr("Haste.Perch"));}),_1nF=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1nG=new T(function(){var _1nH=hs_wordToWord64(3005229400),_1nI=_1nH,_1nJ=hs_wordToWord64(2682402736),_1nK=_1nJ;return [0,_1nI,_1nK,[0,_1nI,_1nK,_1nF,_1nE,_1nD],_9];}),_1nL=function(_1nM){return E(_1nG);},_1nN=function(_1nO){var _1nP=E(_1nO);if(!_1nP[0]){return [0];}else{var _1nQ=E(_1nP[1]);return [1,[0,_1nQ[1],_1nQ[2]],new T(function(){return B(_1nN(_1nP[2]));})];}},_1nR=function(_1nS,_1nT){var _1nU=E(_1nS);if(!_1nU){return [0,_9,_1nT];}else{var _1nV=E(_1nT);if(!_1nV[0]){return [0,_9,_9];}else{var _1nW=new T(function(){var _1nX=B(_1nR(_1nU-1|0,_1nV[2]));return [0,_1nX[1],_1nX[2]];});return [0,[1,_1nV[1],new T(function(){return E(E(_1nW)[1]);})],new T(function(){return E(E(_1nW)[2]);})];}}},_1nY=[0,120],_1nZ=[0,48],_1o0=function(_1o1){var _1o2=new T(function(){var _1o3=B(_1nR(8,new T(function(){var _1o4=md5(toJSStr(E(_1o1))),_1o5=_1o4;return fromJSStr(_1o5);})));return [0,_1o3[1],_1o3[2]];}),_1o6=parseInt([0,toJSStr([1,_1nZ,[1,_1nY,new T(function(){return E(E(_1o2)[1]);})]])]),_1o7=_1o6,_1o8=new T(function(){var _1o9=B(_1nR(8,new T(function(){return E(E(_1o2)[2]);})));return [0,_1o9[1],_1o9[2]];}),_1oa=parseInt([0,toJSStr([1,_1nZ,[1,_1nY,new T(function(){return E(E(_1o8)[1]);})]])]),_1ob=_1oa,_1oc=hs_mkWord64(_1o7,_1ob),_1od=_1oc,_1oe=parseInt([0,toJSStr([1,_1nZ,[1,_1nY,new T(function(){return E(B(_1nR(8,new T(function(){return E(E(_1o8)[2]);})))[1]);})]])]),_1of=_1oe,_1og=hs_mkWord64(_1of,_1of),_1oh=_1og;return [0,_1od,_1oh];},_1oi=function(_1oj,_1ok){var _1ol=jsShowI(_1oj),_1om=_1ol,_1on=md5(_1om),_1oo=_1on;return new F(function(){return _e(fromJSStr(_1oo),new T(function(){var _1op=jsShowI(_1ok),_1oq=_1op,_1or=md5(_1oq),_1os=_1or;return fromJSStr(_1os);},1));});},_1ot=function(_1ou){var _1ov=E(_1ou);return new F(function(){return _1oi(_1ov[1],_1ov[2]);});},_1ow=function(_1ox,_1oy){return function(_1oz){return E(new T(function(){var _1oA=B(A(_1ox,[_])),_1oB=E(_1oA[3]),_1oC=_1oB[1],_1oD=_1oB[2],_1oE=B(_e(_1oA[4],[1,new T(function(){return B(A(_1oy,[_]));}),_9]));if(!_1oE[0]){var _1oF=[0,_1oC,_1oD,_1oB,_9];}else{var _1oG=B(_1o0(new T(function(){return B(_7r(B(_7X(_1ot,[1,[0,_1oC,_1oD],new T(function(){return B(_1nN(_1oE));})]))));},1))),_1oF=[0,_1oG[1],_1oG[2],_1oB,_1oE];}var _1oH=_1oF,_1oI=_1oH;return _1oI;}));};},_1oJ=new T(function(){return B(_1ow(_1nL,_1nB));}),_1oK=function(_1oL,_1oM,_1oN,_){var _1oO=E(_1oM),_1oP=B(A(_1oL,[_1oN,_])),_1oQ=_1oP,_1oR=B(A(_5d,[_5q,_1oQ,_1oO[1],_1oO[2],_])),_1oS=_1oR;return _1oQ;},_1oT=function(_1oU,_1oV){while(1){var _1oW=(function(_1oX,_1oY){var _1oZ=E(_1oY);if(!_1oZ[0]){return E(_1oX);}else{_1oU=function(_1p0,_){return new F(function(){return _1oK(_1oX,_1oZ[1],_1p0,_);});};_1oV=_1oZ[2];return null;}})(_1oU,_1oV);if(_1oW!=null){return _1oW;}}},_1p1=new T(function(){return B(unCStr("value"));}),_1p2=new T(function(){return B(unCStr("id"));}),_1p3=new T(function(){return B(unCStr("onclick"));}),_1p4=new T(function(){return B(unCStr("checked"));}),_1p5=[0,_1p4,_9],_1p6=new T(function(){return B(unCStr("type"));}),_1p7=new T(function(){return B(unCStr("input"));}),_1p8=function(_1p9,_){return new F(function(){return _1nf(_1p7,_1p9,_);});},_1pa=function(_1pb,_1pc,_1pd){return new F(function(){return _1oT(function(_1p0,_){return new F(function(){return _1oK(_1pb,_1pc,_1p0,_);});},_1pd);});},_1pe=function(_1pf,_1pg,_1ph,_1pi,_1pj){var _1pk=new T(function(){var _1pl=new T(function(){return B(_1pa(_1p8,[0,_1p6,_1pg],[1,[0,_1p2,_1pf],[1,[0,_1p1,_1ph],_9]]));});return !E(_1pi)?E(_1pl):B(_1pa(_1pl,_1p5,_9));}),_1pm=E(_1pj);return _1pm[0]==0?E(_1pk):B(_1pa(_1pk,[0,_1p3,_1pm[1]],_9));},_1pn=new T(function(){return B(unCStr("href"));}),_1po=[0,97],_1pp=[1,_1po,_9],_1pq=function(_1pr,_){return new F(function(){return _1nf(_1pp,_1pr,_);});},_1ps=function(_1pt,_1pu){return function(_1pv,_){var _1pw=B(A(new T(function(){return B(_1pa(_1pq,[0,_1pn,_1pt],_9));}),[_1pv,_])),_1px=_1pw,_1py=B(A(_1pu,[_1px,_])),_1pz=_1py;return _1px;};},_1pA=function(_1pB){return new F(function(){return _1ps(_1pB,function(_1p0,_){return new F(function(){return _56(_1pB,_1p0,_);});});});},_1pC=new T(function(){return B(unCStr("option"));}),_1pD=function(_1pE,_){return new F(function(){return _1nf(_1pC,_1pE,_);});},_1pF=new T(function(){return B(unCStr("selected"));}),_1pG=[0,_1pF,_9],_1pH=function(_1pI,_1pJ,_1pK){var _1pL=new T(function(){return B(_1pa(_1pD,[0,_1p1,_1pI],_9));});if(!E(_1pK)){return function(_1pM,_){var _1pN=B(A(_1pL,[_1pM,_])),_1pO=_1pN,_1pP=B(A(_1pJ,[_1pO,_])),_1pQ=_1pP;return _1pO;};}else{return new F(function(){return _1pa(function(_1pR,_){var _1pS=B(A(_1pL,[_1pR,_])),_1pT=_1pS,_1pU=B(A(_1pJ,[_1pT,_])),_1pV=_1pU;return _1pT;},_1pG,_9);});}},_1pW=function(_1pX,_1pY){return new F(function(){return _1pH(_1pX,function(_1p0,_){return new F(function(){return _56(_1pX,_1p0,_);});},_1pY);});},_1pZ=new T(function(){return B(unCStr("method"));}),_1q0=new T(function(){return B(unCStr("action"));}),_1q1=new T(function(){return B(unCStr("UTF-8"));}),_1q2=new T(function(){return B(unCStr("acceptCharset"));}),_1q3=[0,_1q2,_1q1],_1q4=new T(function(){return B(unCStr("form"));}),_1q5=function(_1q6,_){return new F(function(){return _1nf(_1q4,_1q6,_);});},_1q7=function(_1q8,_1q9,_1qa){return function(_1qb,_){var _1qc=B(A(new T(function(){return B(_1pa(_1q5,_1q3,[1,[0,_1q0,_1q8],[1,[0,_1pZ,_1q9],_9]]));}),[_1qb,_])),_1qd=_1qc,_1qe=B(A(_1qa,[_1qd,_])),_1qf=_1qe;return _1qd;};},_1qg=new T(function(){return B(unCStr("select"));}),_1qh=function(_1qi,_){return new F(function(){return _1nf(_1qg,_1qi,_);});},_1qj=function(_1qk,_1ql){return function(_1qm,_){var _1qn=B(A(new T(function(){return B(_1pa(_1qh,[0,_1p2,_1qk],_9));}),[_1qm,_])),_1qo=_1qn,_1qp=B(A(_1ql,[_1qo,_])),_1qq=_1qp;return _1qo;};},_1qr=new T(function(){return B(unCStr("textarea"));}),_1qs=function(_1qt,_){return new F(function(){return _1nf(_1qr,_1qt,_);});},_1qu=function(_1qv,_1qw){return function(_1qx,_){var _1qy=B(A(new T(function(){return B(_1pa(_1qs,[0,_1p2,_1qv],_9));}),[_1qx,_])),_1qz=_1qy,_1qA=B(_56(_1qw,_1qz,_)),_1qB=_1qA;return _1qz;};},_1qC=new T(function(){return B(unCStr("color:red"));}),_1qD=new T(function(){return B(unCStr("style"));}),_1qE=[0,_1qD,_1qC],_1qF=[0,98],_1qG=[1,_1qF,_9],_1qH=function(_1qI){return new F(function(){return _1pa(function(_1qJ,_){var _1qK=B(_1nf(_1qG,_1qJ,_)),_1qL=_1qK,_1qM=B(A(_1qI,[_1qL,_])),_1qN=_1qM;return _1qL;},_1qE,_9);});},_1qO=function(_1qP,_1qQ,_){var _1qR=E(_1qP);if(!_1qR[0]){return _1qQ;}else{var _1qS=B(A(_1qR[1],[_1qQ,_])),_1qT=_1qS,_1qU=B(_1qO(_1qR[2],_1qQ,_)),_1qV=_1qU;return _1qQ;}},_1qW=function(_1qX,_1qY,_){return new F(function(){return _1qO(_1qX,_1qY,_);});},_1qZ=function(_1r0,_1r1,_1r2,_){var _1r3=B(A(_1r0,[_1r2,_])),_1r4=_1r3,_1r5=B(A(_1r1,[_1r2,_])),_1r6=_1r5;return _1r2;},_1r7=[0,_5t,_1qZ,_1qW],_1r8=[0,_1r7,_1oJ,_56,_56,_1nl,_1qH,_1ps,_1pA,_1pe,_1qu,_1qj,_1pH,_1pW,_1q7,_1oT],_1r9=function(_1ra,_1rb,_){var _1rc=B(A(_1rb,[_])),_1rd=_1rc;return _1ra;},_1re=function(_1rf,_1rg,_){var _1rh=B(A(_1rg,[_])),_1ri=_1rh;return new T(function(){return B(A(_1rf,[_1ri]));});},_1rj=[0,_1re,_1r9],_1rk=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1rl=new T(function(){return B(unCStr("base"));}),_1rm=new T(function(){return B(unCStr("IOException"));}),_1rn=new T(function(){var _1ro=hs_wordToWord64(4053623282),_1rp=_1ro,_1rq=hs_wordToWord64(3693590983),_1rr=_1rq;return [0,_1rp,_1rr,[0,_1rp,_1rr,_1rl,_1rk,_1rm],_9];}),_1rs=function(_1rt){return E(_1rn);},_1ru=function(_1rv){var _1rw=E(_1rv);return new F(function(){return _2y(B(_2w(_1rw[1])),_1rs,_1rw[2]);});},_1rx=new T(function(){return B(unCStr(": "));}),_1ry=[0,41],_1rz=new T(function(){return B(unCStr(" ("));}),_1rA=new T(function(){return B(unCStr("already exists"));}),_1rB=new T(function(){return B(unCStr("does not exist"));}),_1rC=new T(function(){return B(unCStr("protocol error"));}),_1rD=new T(function(){return B(unCStr("failed"));}),_1rE=new T(function(){return B(unCStr("invalid argument"));}),_1rF=new T(function(){return B(unCStr("inappropriate type"));}),_1rG=new T(function(){return B(unCStr("hardware fault"));}),_1rH=new T(function(){return B(unCStr("unsupported operation"));}),_1rI=new T(function(){return B(unCStr("timeout"));}),_1rJ=new T(function(){return B(unCStr("resource vanished"));}),_1rK=new T(function(){return B(unCStr("interrupted"));}),_1rL=new T(function(){return B(unCStr("resource busy"));}),_1rM=new T(function(){return B(unCStr("resource exhausted"));}),_1rN=new T(function(){return B(unCStr("end of file"));}),_1rO=new T(function(){return B(unCStr("illegal operation"));}),_1rP=new T(function(){return B(unCStr("permission denied"));}),_1rQ=new T(function(){return B(unCStr("user error"));}),_1rR=new T(function(){return B(unCStr("unsatisified constraints"));}),_1rS=new T(function(){return B(unCStr("system error"));}),_1rT=function(_1rU,_1rV){switch(E(_1rU)){case 0:return new F(function(){return _e(_1rA,_1rV);});break;case 1:return new F(function(){return _e(_1rB,_1rV);});break;case 2:return new F(function(){return _e(_1rL,_1rV);});break;case 3:return new F(function(){return _e(_1rM,_1rV);});break;case 4:return new F(function(){return _e(_1rN,_1rV);});break;case 5:return new F(function(){return _e(_1rO,_1rV);});break;case 6:return new F(function(){return _e(_1rP,_1rV);});break;case 7:return new F(function(){return _e(_1rQ,_1rV);});break;case 8:return new F(function(){return _e(_1rR,_1rV);});break;case 9:return new F(function(){return _e(_1rS,_1rV);});break;case 10:return new F(function(){return _e(_1rC,_1rV);});break;case 11:return new F(function(){return _e(_1rD,_1rV);});break;case 12:return new F(function(){return _e(_1rE,_1rV);});break;case 13:return new F(function(){return _e(_1rF,_1rV);});break;case 14:return new F(function(){return _e(_1rG,_1rV);});break;case 15:return new F(function(){return _e(_1rH,_1rV);});break;case 16:return new F(function(){return _e(_1rI,_1rV);});break;case 17:return new F(function(){return _e(_1rJ,_1rV);});break;default:return new F(function(){return _e(_1rK,_1rV);});}},_1rW=[0,125],_1rX=new T(function(){return B(unCStr("{handle: "));}),_1rY=function(_1rZ,_1s0,_1s1,_1s2,_1s3,_1s4){var _1s5=new T(function(){var _1s6=new T(function(){return B(_1rT(_1s0,new T(function(){var _1s7=E(_1s2);return _1s7[0]==0?E(_1s4):B(_e(_1rz,new T(function(){return B(_e(_1s7,[1,_1ry,_1s4]));},1)));},1)));},1),_1s8=E(_1s1);return _1s8[0]==0?E(_1s6):B(_e(_1s8,new T(function(){return B(_e(_1rx,_1s6));},1)));},1),_1s9=E(_1s3);if(!_1s9[0]){var _1sa=E(_1rZ);if(!_1sa[0]){return E(_1s5);}else{var _1sb=E(_1sa[1]);return _1sb[0]==0?B(_e(_1rX,new T(function(){return B(_e(_1sb[1],[1,_1rW,new T(function(){return B(_e(_1rx,_1s5));})]));},1))):B(_e(_1rX,new T(function(){return B(_e(_1sb[1],[1,_1rW,new T(function(){return B(_e(_1rx,_1s5));})]));},1)));}}else{return new F(function(){return _e(_1s9[1],new T(function(){return B(_e(_1rx,_1s5));},1));});}},_1sc=function(_1sd){var _1se=E(_1sd);return new F(function(){return _1rY(_1se[1],_1se[2],_1se[3],_1se[4],_1se[6],_9);});},_1sf=function(_1sg,_1sh){var _1si=E(_1sg);return new F(function(){return _1rY(_1si[1],_1si[2],_1si[3],_1si[4],_1si[6],_1sh);});},_1sj=function(_1sk,_1sl){return new F(function(){return _2T(_1sf,_1sk,_1sl);});},_1sm=function(_1sn,_1so,_1sp){var _1sq=E(_1so);return new F(function(){return _1rY(_1sq[1],_1sq[2],_1sq[3],_1sq[4],_1sq[6],_1sp);});},_1sr=[0,_1sm,_1sc,_1sj],_1ss=new T(function(){return [0,_1rs,_1sr,_1st,_1ru];}),_1st=function(_1su){return [0,_1ss,_1su];},_1sv=7,_1sw=function(_1sx){return [0,_28,_1sv,_9,_1sx,_28,_28];},_1sy=function(_1sz,_){return new F(function(){return die(new T(function(){return B(_1st(new T(function(){return B(_1sw(_1sz));})));}));});},_1sA=function(_1sB,_){return new F(function(){return _1sy(_1sB,_);});},_1sC=function(_1sD,_){return new F(function(){return _1sA(_1sD,_);});},_1sE=function(_1sF,_){return new F(function(){return _1sC(_1sF,_);});},_1sG=function(_1sH,_1sI,_){var _1sJ=B(A(_1sH,[_])),_1sK=_1sJ;return new F(function(){return A(_1sI,[_1sK,_]);});},_1sL=function(_1sM,_1sN,_){var _1sO=B(A(_1sM,[_])),_1sP=_1sO;return new F(function(){return A(_1sN,[_]);});},_1sQ=[0,_1sG,_1sL,_5t,_1sE],_1sR=[0,_1sQ,_5q],_1sS=function(_1sT){return E(E(_1sT)[1]);},_1sU=function(_1sV){return E(E(_1sV)[2]);},_1sW=function(_1sX,_1sY){var _1sZ=new T(function(){return B(_1sS(_1sX));});return function(_1t0){return new F(function(){return A(new T(function(){return B(_NE(_1sZ));}),[new T(function(){return B(A(_1sU,[_1sX,_1sY]));}),function(_1t1){return new F(function(){return A(new T(function(){return B(_iK(_1sZ));}),[[0,_1t1,_1t0]]);});}]);});};},_1t2=function(_1t3,_1t4){return [0,_1t3,function(_1t5){return new F(function(){return _1sW(_1t4,_1t5);});}];},_1t6=function(_1t7,_1t8,_1t9,_1ta){return new F(function(){return A(_NE,[_1t7,new T(function(){return B(A(_1t8,[_1ta]));}),function(_1tb){return new F(function(){return A(_1t9,[new T(function(){return E(E(_1tb)[1]);}),new T(function(){return E(E(_1tb)[2]);})]);});}]);});},_1tc=function(_1td,_1te,_1tf,_1tg){return new F(function(){return A(_NE,[_1td,new T(function(){return B(A(_1te,[_1tg]));}),function(_1th){return new F(function(){return A(_1tf,[new T(function(){return E(E(_1th)[2]);})]);});}]);});},_1ti=function(_1tj,_1tk,_1tl,_1tm){return new F(function(){return _1tc(_1tj,_1tk,_1tl,_1tm);});},_1tn=function(_1to){return E(E(_1to)[4]);},_1tp=function(_1tq,_1tr){return function(_1ts){return E(new T(function(){return B(A(_1tn,[_1tq,_1tr]));}));};},_1tt=function(_1tu){return [0,function(_1tk,_1tl,_1tm){return new F(function(){return _1t6(_1tu,_1tk,_1tl,_1tm);});},function(_1tk,_1tl,_1tm){return new F(function(){return _1ti(_1tu,_1tk,_1tl,_1tm);});},function(_1tv,_1tw){return new F(function(){return A(new T(function(){return B(_iK(_1tu));}),[[0,_1tv,_1tw]]);});},function(_1tm){return new F(function(){return _1tp(_1tu,_1tm);});}];},_1tx=function(_1ty,_1tz,_1tA){return new F(function(){return A(_iK,[_1ty,[0,_1tz,_1tA]]);});},_1tB=[0,10],_1tC=function(_1tD,_1tE){var _1tF=E(_1tE);if(!_1tF[0]){return E(_5q);}else{var _1tG=_1tF[1],_1tH=E(_1tF[2]);if(!_1tH[0]){var _1tI=E(_1tG);return new F(function(){return _1tJ(_1tB,_1tI[3],_1tI[4]);});}else{return function(_1tK){return new F(function(){return A(new T(function(){var _1tL=E(_1tG);return B(_1tJ(_1tB,_1tL[3],_1tL[4]));}),[new T(function(){return B(A(_1tD,[new T(function(){return B(A(new T(function(){return B(_1tC(_1tD,_1tH));}),[_1tK]));})]));})]);});};}}},_1tM=new T(function(){return B(unCStr("(->)"));}),_1tN=new T(function(){return B(unCStr("GHC.Prim"));}),_1tO=new T(function(){var _1tP=hs_wordToWord64(4173248105),_1tQ=_1tP,_1tR=hs_wordToWord64(4270398258),_1tS=_1tR;return [0,_1tQ,_1tS,[0,_1tQ,_1tS,_1nv,_1tN,_1tM],_9];}),_1tT=new T(function(){return E(E(_1tO)[3]);}),_1tU=new T(function(){return B(unCStr("GHC.Types"));}),_1tV=new T(function(){return B(unCStr("[]"));}),_1tW=new T(function(){var _1tX=hs_wordToWord64(4033920485),_1tY=_1tX,_1tZ=hs_wordToWord64(786266835),_1u0=_1tZ;return [0,_1tY,_1u0,[0,_1tY,_1u0,_1nv,_1tU,_1tV],_9];}),_1u1=[1,_1nw,_9],_1u2=function(_1u3){var _1u4=E(_1u3);if(!_1u4[0]){return [0];}else{var _1u5=E(_1u4[1]);return [1,[0,_1u5[1],_1u5[2]],new T(function(){return B(_1u2(_1u4[2]));})];}},_1u6=new T(function(){var _1u7=E(_1tW),_1u8=E(_1u7[3]),_1u9=B(_e(_1u7[4],_1u1));if(!_1u9[0]){var _1ua=E(_1u8);}else{var _1ub=B(_1o0(new T(function(){return B(_7r(B(_7X(_1ot,[1,[0,_1u8[1],_1u8[2]],new T(function(){return B(_1u2(_1u9));})]))));},1))),_1ua=E(_1u8);}var _1uc=_1ua,_1ud=_1uc;return _1ud;}),_1ue=[0,8],_1uf=[0,32],_1ug=function(_1uh){return [1,_1uf,_1uh];},_1ui=new T(function(){return B(unCStr(" -> "));}),_1uj=[0,9],_1uk=[0,93],_1ul=[0,91],_1um=[0,41],_1un=[0,44],_1uo=function(_1uh){return [1,_1un,_1uh];},_1up=[0,40],_1uq=[0,0],_1tJ=function(_1ur,_1us,_1ut){var _1uu=E(_1ut);if(!_1uu[0]){return function(_1uv){return new F(function(){return _e(E(_1us)[5],_1uv);});};}else{var _1uw=_1uu[1],_1ux=function(_1uy){var _1uz=E(_1us)[5],_1uA=function(_1uB){var _1uC=new T(function(){return B(_1tC(_1ug,_1uu));});return E(_1ur)[1]<=9?function(_1uD){return new F(function(){return _e(_1uz,[1,_1uf,new T(function(){return B(A(_1uC,[_1uD]));})]);});}:function(_1uE){return [1,_E,new T(function(){return B(_e(_1uz,[1,_1uf,new T(function(){return B(A(_1uC,[[1,_D,_1uE]]));})]));})];};},_1uF=E(_1uz);if(!_1uF[0]){return new F(function(){return _1uA(_);});}else{if(E(E(_1uF[1])[1])==40){var _1uG=E(_1uF[2]);if(!_1uG[0]){return new F(function(){return _1uA(_);});}else{if(E(E(_1uG[1])[1])==44){return function(_1uH){return [1,_1up,new T(function(){return B(A(new T(function(){return B(_1tC(_1uo,_1uu));}),[[1,_1um,_1uH]]));})];};}else{return new F(function(){return _1uA(_);});}}}else{return new F(function(){return _1uA(_);});}}},_1uI=E(_1uu[2]);if(!_1uI[0]){var _1uJ=E(_1us),_1uK=E(_1u6),_1uL=hs_eqWord64(_1uJ[1],_1uK[1]),_1uM=_1uL;if(!E(_1uM)){return new F(function(){return _1ux(_);});}else{var _1uN=hs_eqWord64(_1uJ[2],_1uK[2]),_1uO=_1uN;if(!E(_1uO)){return new F(function(){return _1ux(_);});}else{return function(_1uP){return [1,_1ul,new T(function(){return B(A(new T(function(){var _1uQ=E(_1uw);return B(_1tJ(_1uq,_1uQ[3],_1uQ[4]));}),[[1,_1uk,_1uP]]));})];};}}}else{if(!E(_1uI[2])[0]){var _1uR=E(_1us),_1uS=E(_1tT),_1uT=hs_eqWord64(_1uR[1],_1uS[1]),_1uU=_1uT;if(!E(_1uU)){return new F(function(){return _1ux(_);});}else{var _1uV=hs_eqWord64(_1uR[2],_1uS[2]),_1uW=_1uV;if(!E(_1uW)){return new F(function(){return _1ux(_);});}else{var _1uX=new T(function(){var _1uY=E(_1uI[1]);return B(_1tJ(_1ue,_1uY[3],_1uY[4]));}),_1uZ=new T(function(){var _1v0=E(_1uw);return B(_1tJ(_1uj,_1v0[3],_1v0[4]));});return E(_1ur)[1]<=8?function(_1v1){return new F(function(){return A(_1uZ,[new T(function(){return B(_e(_1ui,new T(function(){return B(A(_1uX,[_1v1]));},1)));})]);});}:function(_1v2){return [1,_E,new T(function(){return B(A(_1uZ,[new T(function(){return B(_e(_1ui,new T(function(){return B(A(_1uX,[[1,_D,_1v2]]));},1)));})]));})];};}}}else{return new F(function(){return _1ux(_);});}}}},_1v3=function(_1v4,_1v5){return new F(function(){return A(_1v4,[function(_){return new F(function(){return jsFind(toJSStr(E(_1v5)));});}]);});},_1v6=[0],_1v7=function(_1v8){return E(E(_1v8)[3]);},_1v9=new T(function(){return [0,"value"];}),_1va=function(_1vb){return E(E(_1vb)[6]);},_1vc=function(_1vd){return E(E(_1vd)[1]);},_1ve=new T(function(){return B(unCStr("Char"));}),_1vf=new T(function(){var _1vg=hs_wordToWord64(3763641161),_1vh=_1vg,_1vi=hs_wordToWord64(1343745632),_1vj=_1vi;return [0,_1vh,_1vj,[0,_1vh,_1vj,_1nv,_1tU,_1ve],_9];}),_1vk=function(_1vl){return E(_1vf);},_1vm=function(_1vn){return E(_1tW);},_1vo=new T(function(){return B(_1ow(_1vm,_1vk));}),_1vp=new T(function(){return B(A(_1vo,[_]));}),_1vq=function(_1vr,_1vs,_1vt,_1vu,_1vv,_1vw,_1vx,_1vy,_1vz){var _1vA=new T(function(){return B(A(_1vu,[_1v6]));});return new F(function(){return A(_1vs,[new T(function(){return B(_1v3(E(_1vr)[2],_1vz));}),function(_1vB){var _1vC=E(_1vB);return _1vC[0]==0?E(_1vA):B(A(_1vs,[new T(function(){return B(A(E(_1vr)[2],[function(_){var _1vD=jsGet(E(_1vC[1])[1],E(_1v9)[1]),_1vE=_1vD;return [1,new T(function(){return fromJSStr(_1vE);})];}]));}),function(_1vF){var _1vG=E(_1vF);if(!_1vG[0]){return E(_1vA);}else{var _1vH=_1vG[1];if(!E(new T(function(){var _1vI=B(A(_1vw,[_])),_1vJ=E(_1vp),_1vK=hs_eqWord64(_1vI[1],_1vJ[1]),_1vL=_1vK;if(!E(_1vL)){var _1vM=false;}else{var _1vN=hs_eqWord64(_1vI[2],_1vJ[2]),_1vO=_1vN,_1vM=E(_1vO)==0?false:true;}var _1vP=_1vM,_1vQ=_1vP;return _1vQ;}))){var _1vR=function(_1vS){return new F(function(){return A(_1vu,[[1,_1vH,new T(function(){return B(A(new T(function(){return B(_1va(_1vy));}),[new T(function(){return B(A(new T(function(){return B(_1v7(_1vy));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1vH,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1vT=B(A(_1vw,[_]));return B(A(_1tJ,[_1uq,_1vT[3],_1vT[4],_9]));})));})));})));})]));})]));})]]);});},_1vU=B(A(new T(function(){return B(A(_1vc,[_1vx,_1R]));}),[_1vH]));if(!_1vU[0]){return new F(function(){return _1vR(_);});}else{var _1vV=E(_1vU[1]);return E(_1vV[2])[0]==0?E(_1vU[2])[0]==0?B(A(_1vu,[[2,_1vV[1]]])):B(_1vR(_)):B(_1vR(_));}}else{return new F(function(){return A(_1vu,[[2,_1vH]]);});}}}]));}]);});},_1vW=function(_1vX){return E(E(_1vX)[10]);},_1vY=function(_1vZ){return new F(function(){return _kM([1,function(_1w0){return new F(function(){return A(_ss,[_1w0,function(_1w1){return E(new T(function(){return B(_tI(function(_1w2){var _1w3=E(_1w2);return _1w3[0]==0?B(A(_1vZ,[_1w3[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_u4(_1w4,_1vZ))];}));});},_1w4=function(_1w5,_1w6){return new F(function(){return _1vY(_1w6);});},_1w7=[0,91],_1w8=[1,_1w7,_9],_1w9=function(_1wa,_1wb){var _1wc=function(_1wd,_1we){return [1,function(_1wf){return new F(function(){return A(_ss,[_1wf,function(_1wg){return E(new T(function(){return B(_tI(function(_1wh){var _1wi=E(_1wh);if(_1wi[0]==2){var _1wj=E(_1wi[1]);if(!_1wj[0]){return [2];}else{var _1wk=_1wj[2];switch(E(E(_1wj[1])[1])){case 44:return E(_1wk)[0]==0?!E(_1wd)?[2]:E(new T(function(){return B(A(_1wa,[_u3,function(_1wl){return new F(function(){return _1wc(_nZ,function(_1wm){return new F(function(){return A(_1we,[[1,_1wl,_1wm]]);});});});}]));})):[2];case 93:return E(_1wk)[0]==0?E(new T(function(){return B(A(_1we,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1wn=function(_1wo){return new F(function(){return _kM([1,function(_1wp){return new F(function(){return A(_ss,[_1wp,function(_1wq){return E(new T(function(){return B(_tI(function(_1wr){var _1ws=E(_1wr);return _1ws[0]==2?!B(_lj(_1ws[1],_1w8))?[2]:E(new T(function(){return B(_kM(B(_1wc(_1S,_1wo)),new T(function(){return B(A(_1wa,[_u3,function(_1wt){return new F(function(){return _1wc(_nZ,function(_1wu){return new F(function(){return A(_1wo,[[1,_1wt,_1wu]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_u4(function(_1wv,_1ww){return new F(function(){return _1wn(_1ww);});},_1wo))];}));});};return new F(function(){return _1wn(_1wb);});},_1wx=function(_1wy){return new F(function(){return _kM(B(_kM([1,function(_1wz){return new F(function(){return A(_ss,[_1wz,function(_1wA){return E(new T(function(){return B(_tI(function(_1wB){var _1wC=E(_1wB);return _1wC[0]==1?B(A(_1wy,[_1wC[1]])):[2];}));}));}]);});}],new T(function(){return B(_1w9(_1w4,_1wy));}))),new T(function(){return [1,B(_u4(_1wD,_1wy))];}));});},_1wD=function(_1wE,_1wF){return new F(function(){return _1wx(_1wF);});},_1wG=new T(function(){return B(_1wx(_lA));}),_1wH=function(_1wI){return new F(function(){return _kC(_1wG,_1wI);});},_1wJ=new T(function(){return B(_1vY(_lA));}),_1wK=function(_1wI){return new F(function(){return _kC(_1wJ,_1wI);});},_1wL=function(_1wM){return E(_1wK);},_1wN=[0,_1wL,_1wH,_1w4,_1wD],_1wO=function(_1wP){return E(E(_1wP)[4]);},_1wQ=function(_1wR,_1wS,_1wT){return new F(function(){return _1w9(new T(function(){return B(_1wO(_1wR));}),_1wT);});},_1wU=function(_1wV){return function(_m0){return new F(function(){return _kC(new T(function(){return B(_1w9(new T(function(){return B(_1wO(_1wV));}),_lA));}),_m0);});};},_1wW=function(_1wX,_1wY){return function(_m0){return new F(function(){return _kC(new T(function(){return B(A(_1wO,[_1wX,_1wY,_lA]));}),_m0);});};},_1wZ=function(_1x0){return [0,function(_1wI){return new F(function(){return _1wW(_1x0,_1wI);});},new T(function(){return B(_1wU(_1x0));}),new T(function(){return B(_1wO(_1x0));}),function(_1x1,_1wI){return new F(function(){return _1wQ(_1x0,_1x1,_1wI);});}];},_1x2=new T(function(){return B(_1wZ(_1wN));}),_1x3=function(_1x4,_1x5,_1x6){var _1x7=new T(function(){return B(_1vW(_1x4));}),_1x8=new T(function(){return B(_1sS(_1x6));}),_1x9=new T(function(){return B(_iK(_1x8));});return function(_1xa,_1xb){return new F(function(){return A(new T(function(){return B(_NE(_1x8));}),[new T(function(){return B(A(new T(function(){return B(_NE(_1x8));}),[new T(function(){return B(A(new T(function(){return B(_iK(_1x8));}),[[0,_1xb,_1xb]]));}),function(_1xc){var _1xd=new T(function(){return E(E(_1xc)[1]);}),_1xe=new T(function(){return E(E(_1xd)[2]);});return new F(function(){return A(new T(function(){return B(_NE(_1x8));}),[new T(function(){return B(A(new T(function(){return B(_iK(_1x8));}),[[0,_5c,new T(function(){var _1xf=E(_1xd);return [0,_1xf[1],new T(function(){return [0,E(_1xe)[1]+1|0];}),_1xf[3],_1xf[4],_1xf[5],_1xf[6],_1xf[7]];})]]));}),function(_1xg){return new F(function(){return A(new T(function(){return B(_iK(_1x8));}),[[0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_1xe)[1],_9)),new T(function(){return E(E(_1xd)[1]);},1)));})],new T(function(){return E(E(_1xg)[2]);})]]);});}]);});}]));}),function(_1xh){var _1xi=new T(function(){return E(E(_1xh)[1]);});return new F(function(){return A(new T(function(){return B(_NE(_1x8));}),[new T(function(){return B(A(_1vq,[new T(function(){return B(_1t2(new T(function(){return B(_1tt(_1x8));}),_1x6));}),function(_1xj,_1p0,_1xk){return new F(function(){return _1t6(_1x8,_1xj,_1p0,_1xk);});},function(_1xj,_1p0,_1xk){return new F(function(){return _1ti(_1x8,_1xj,_1p0,_1xk);});},function(_1p0,_1xk){return new F(function(){return _1tx(_1x8,_1p0,_1xk);});},function(_1xk){return new F(function(){return _1tp(_1x8,_1xk);});},_1vo,_1x2,_1x4,_1xi,new T(function(){return E(E(_1xh)[2]);})]));}),function(_1xl){var _1xm=E(_1xl),_1xn=_1xm[2],_1xo=E(_1xm[1]);switch(_1xo[0]){case 0:return new F(function(){return A(_1x9,[[0,[0,new T(function(){return B(A(_1x7,[_1xi,_1xa]));}),_28],_1xn]]);});break;case 1:return new F(function(){return A(_1x9,[[0,[0,new T(function(){return B(A(_1x7,[_1xi,_1xo[1]]));}),_28],_1xn]]);});break;default:var _1xp=_1xo[1];return new F(function(){return A(_1x9,[[0,[0,new T(function(){return B(A(_1x7,[_1xi,_1xp]));}),[1,_1xp]],_1xn]]);});}}]);});}]);});};},_1xq=new T(function(){return B(_1x3(_1r8,_1rj,_1sR));}),_1xr=new T(function(){return B(_C8("w_s6mw{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv a5sJ} [tv]"));}),_1xs=new T(function(){return B(_C8("w_s6mx{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv a5sI} [tv]"));}),_1xt=function(_1xu){return E(E(_1xu)[2]);},_1xv=function(_1xw){return E(E(_1xw)[1]);},_1xx=function(_1xy,_1xz,_1xA){return function(_1xB,_){var _1xC=B(A(_1xz,[_1xB,_])),_1xD=_1xC,_1xE=E(_1xD),_1xF=E(_1xE[1]),_1xG=new T(function(){return B(A(new T(function(){return B(_1xt(_1xy));}),[_1xA,function(_){var _1xH=E(E(_1xB)[4]),_1xI=B(A(_1xH[1],[_])),_1xJ=_1xI,_1xK=E(_1xJ);if(!_1xK[0]){return _5c;}else{var _1xL=B(A(_1xH[2],[_1xK[1],_])),_1xM=_1xL;return _5c;}}]));});return [0,[0,function(_1xN,_){var _1xO=B(A(_1xF[1],[_1xN,_])),_1xP=_1xO,_1xQ=E(_1xP),_1xR=E(_1xG),_1xS=jsSetCB(_1xQ[1],toJSStr(E(new T(function(){return B(A(_1xv,[_1xy,_1xA]));}))),_1xG),_1xT=_1xS;return _1xQ;},_1xF[2]],_1xE[2]];};},_1xU=function(_1xV,_1xW,_1xX,_1xY,_1xZ,_1y0,_1y1,_1y2,_1y3,_1y4,_1y5){return function(_1y6,_1y7){return function(_m0,_19A){return new F(function(){return _65(function(_1y8,_){var _1y9=B(A(new T(function(){return B(_1xx(_55,new T(function(){return B(_1xx(_55,new T(function(){return B(A(_1xq,[_1y7]));}),_1p));}),_1o));}),[_1y8,_])),_1ya=_1y9,_1yb=E(_1ya),_1yc=E(_1yb[1]);return [0,[0,function(_1yd,_){var _1ye=B(A(_1yc[1],[_1yd,_])),_1yf=_1ye,_1yg=B(A(_5d,[_5q,_1yf,_bP,_cf,_])),_1yh=_1yg;return _1yf;},_1yc[2]],_1yb[2]];},function(_1yi){var _1yj=new T(function(){var _1yk=B(_Dg(_Cc,_DC,[0,new T(function(){return B(_e(_1yi,_1ne));}),E(_C5),E(_5c)]));if(!_1yk[0]){var _1yl=E(_1yk[1]);if(!_1yl[0]){var _1ym=E(E(_1yl[1])[1]);}else{var _1ym=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1yl[1]));})));})],_9],_9];}var _1yn=_1ym;}else{var _1yo=E(_1yk[1]);if(!_1yo[0]){var _1yp=E(E(_1yo[1])[1]);}else{var _1yp=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1yo[1]));})));})],_9],_9];}var _1yn=_1yp;}return _1yn;});return function(_m0,_19A){return new F(function(){return _65(_bA,function(_1yq,_1yr,_){return new F(function(){return _65(_bG,function(_1ys,_1yt,_){return new F(function(){return _65(_bL,function(_1yu,_1yv,_){return new F(function(){return _65(function(_1yw,_){return [0,[0,function(_1yx,_){var _1yy=B(_bX(_56,_9,_1yx,_)),_1yz=_1yy,_1yA=B(A(_5d,[_5q,_1yz,_5p,_1yq,_])),_1yB=_1yA,_1yC=B(A(_5d,[_5q,_1yz,_bP,_bM,_])),_1yD=_1yC;return _1yz;},_bS],_1yw];},function(_1yE,_1yF,_){return new F(function(){return _65(function(_1yG,_){return [0,[0,function(_1yH,_){var _1yI=B(_5T(_63,new T(function(){return B(_1n4(_1yj));}),_1yH,_)),_1yJ=_1yI,_1yK=B(A(_5d,[_5q,_1yJ,_5p,_1ys,_])),_1yL=_1yK,_1yM=B(A(_5d,[_5q,_1yJ,_bP,_bN,_])),_1yN=_1yM;return _1yJ;},_bS],_1yG];},function(_1yO){return E(new T(function(){var _1yP=E(new T(function(){var _1yQ=B(_1lh(_1yj,new T(function(){return E(E(_1y6)[1]);})));return _1yQ[0]==0?[0,_1yQ[1]]:[1,new T(function(){return B(_1ii(_1xV,_1xW,_1xX,_1xY,_1xZ,_1y0,_1y1,_1y2,_1y3,_1xr,_1xs,_1y4,_1y5,new T(function(){return E(E(_1y6)[2]);}),_1yQ[1]));})];}));if(!_1yP[0]){var _1yR=function(_1yS,_){return [0,[0,function(_1yT,_){var _1yU=B(_bX(_63,function(_bB,_){return new F(function(){return _c7(new T(function(){return B(_db(_1yP[1],_9));}),_bB,_);});},_1yT,_)),_1yV=_1yU,_1yW=B(A(_5d,[_5q,_1yV,_5p,_1yu,_])),_1yX=_1yW,_1yY=B(A(_5d,[_5q,_1yV,_bP,_bO,_])),_1yZ=_1yY;return _1yV;},_bS],_1yS];};}else{var _1z0=E(_1yP[1]);if(!_1z0[0]){var _1z1=function(_bB,_){return new F(function(){return _ch(_1yq,_bt,_bU,_bB,_);});};}else{var _1z1=function(_m0,_19A){return new F(function(){return _ch(_1yq,_bt,function(_1z2,_){return [0,[0,function(_bB,_){return new F(function(){return _5T(_56,new T(function(){var _1z3=E(_1z0[1]);return B(_bo(new T(function(){return B(_b9(_1y1,_1y0,_1xZ,_1xY,_1xX,_1xV,_1xW));}),_1z3[1],_1z3[2]));}),_bB,_);});},_bS],_1z2];},_m0,_19A);});};}var _1yR=_1z1;}return _1yR;}));},_1yF,_);});},_1yv,_);});},_1yt,_);});},_1yr,_);});},_m0,_19A);});};},_m0,_19A);});};};},_1z4=function(_1z5,_1z6,_1z7,_1z8){return new F(function(){return A(_1z5,[function(_){var _1z9=jsSet(E(_1z6)[1],toJSStr(E(_1z7)),toJSStr(E(_1z8)));return _5c;}]);});},_1za=new T(function(){return B(unCStr("innerHTML"));}),_1zb=new T(function(){return B(unCStr("textContent"));}),_1zc=function(_1zd,_1ze,_1zf,_1zg,_1zh,_1zi,_1zj,_1zk,_1zl,_1zm,_1zn,_1zo,_1zp,_){var _1zq=B(_1j(_1zp,_1zb,_)),_1zr=_1zq,_1zs=[0,_1zp],_1zt=B(A(_1z4,[_5q,_1zs,_1za,_9,_])),_1zu=_1zt,_1zv=E(_2l)[1],_1zw=takeMVar(_1zv),_1zx=_1zw,_1zy=B(A(_1xU,[_1zd,_1ze,_1zf,_1zg,_1zh,_1zi,_1zj,_1zk,_1zl,_1zm,_1zn,_1zo,_1zr,_1zx,_])),_1zz=_1zy,_1zA=E(_1zz),_1zB=E(_1zA[1]),_=putMVar(_1zv,_1zA[2]),_1zC=B(A(_1zB[1],[_1zs,_])),_1zD=_1zC;return _1zB[2];},_1zE=function(_){var _1zF=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1zG=_1zF;return _5c;},_1zH=new T(function(){return B(unCStr("embedding complete"));}),_1zI=new T(function(){return B(unCStr("proofbox"));}),_1zJ=function(_1zK,_1zL,_1zM,_1zN,_1zO,_1zP,_1zQ,_1zR,_1zS,_1zT,_1zU,_1zV,_){var _1zW=jsElemsByClassName(toJSStr(E(_1zI))),_1zX=_1zW,_1zY=B((function(_1zZ,_){while(1){var _1A0=E(_1zZ);if(!_1A0[0]){return _5c;}else{var _1A1=B(_1zc(_1zK,_1zL,_1zM,_1zN,_1zO,_1zP,_1zQ,_1zR,_1zS,_1zT,_1zU,_1zV,E(_1A0[1])[1],_)),_1A2=_1A1;_1zZ=_1A0[2];continue;}}})(_1zX,_)),_1A3=_1zY,_1A4=jsLog(toJSStr(E(_1zH))),_1A5=jsSetTimeout(60,_1zE);return _5c;},_1A6=new T(function(){return B(unCStr("ADD"));}),_1A7=new T(function(){return B(unCStr("ADJ"));}),_1A8=[0,1],_1A9=[1,_1A8],_1Aa=[1,_1A9],_1Ab=[0,_1A8],_1Ac=[1,_1Ab],_1Ad=new T(function(){return B(unCStr("DN"));}),_1Ae=new T(function(){return B(_lj(_9,_1Ad));}),_1Af=new T(function(){return B(unCStr("MTP"));}),_1Ag=new T(function(){return B(unCStr("MP"));}),_1Ah=new T(function(){return B(unCStr("ID"));}),_1Ai=new T(function(){return B(unCStr("CD"));}),_1Aj=[0,2],_1Ak=[1,_1Aj],_1Al=[1,_1Ak],_1Am=[0,_1Aj],_1An=[1,_1Am],_1Ao=function(_1Ap){if(!B(_lj(_1Ap,_1A6))){if(!B(_lj(_1Ap,_1A7))){if(!B(_lj(_1Ap,_1Ai))){if(!B(_lj(_1Ap,_1Ah))){if(!B(_lj(_1Ap,_1Ag))){if(!B(_lj(_1Ap,_1Af))){var _1Aq=E(_1Ap);return _1Aq[0]==0?!E(_1Ae)?[0]:E(_1Ac):E(E(_1Aq[1])[1])==83?E(_1Aq[2])[0]==0?E(_1Ac):!B(_lj(_1Aq,_1Ad))?[0]:E(_1Ac):!B(_lj(_1Aq,_1Ad))?[0]:E(_1Ac);}else{return E(_1An);}}else{return E(_1An);}}else{return E(_1Al);}}else{return E(_1Aa);}}else{return E(_1An);}}else{return E(_1Ac);}},_1Ar=function(_1As){return E(E(_1As)[2]);},_1At=function(_1Au,_1Av,_1Aw){while(1){var _1Ax=E(_1Av);if(!_1Ax[0]){return E(_1Aw)[0]==0?1:0;}else{var _1Ay=E(_1Aw);if(!_1Ay[0]){return 2;}else{var _1Az=B(A(_1Ar,[_1Au,_1Ax[1],_1Ay[1]]));if(_1Az==1){_1Av=_1Ax[2];_1Aw=_1Ay[2];continue;}else{return E(_1Az);}}}}},_1AA=function(_1AB){return E(E(_1AB)[3]);},_1AC=function(_1AD,_1AE,_1AF,_1AG,_1AH){switch(B(_1At(_1AD,_1AE,_1AG))){case 0:return true;case 1:return new F(function(){return A(_1AA,[_1AD,_1AF,_1AH]);});break;default:return false;}},_1AI=function(_1AJ,_1AK,_1AL,_1AM){var _1AN=E(_1AL),_1AO=E(_1AM);return new F(function(){return _1AC(_1AK,_1AN[1],_1AN[2],_1AO[1],_1AO[2]);});},_1AP=function(_1AQ){return E(E(_1AQ)[6]);},_1AR=function(_1AS,_1AT,_1AU,_1AV,_1AW){switch(B(_1At(_1AS,_1AT,_1AV))){case 0:return true;case 1:return new F(function(){return A(_1AP,[_1AS,_1AU,_1AW]);});break;default:return false;}},_1AX=function(_1AY,_1AZ,_1B0,_1B1){var _1B2=E(_1B0),_1B3=E(_1B1);return new F(function(){return _1AR(_1AZ,_1B2[1],_1B2[2],_1B3[1],_1B3[2]);});},_1B4=function(_1B5){return E(E(_1B5)[5]);},_1B6=function(_1B7,_1B8,_1B9,_1Ba,_1Bb){switch(B(_1At(_1B7,_1B8,_1Ba))){case 0:return false;case 1:return new F(function(){return A(_1B4,[_1B7,_1B9,_1Bb]);});break;default:return true;}},_1Bc=function(_1Bd,_1Be,_1Bf,_1Bg){var _1Bh=E(_1Bf),_1Bi=E(_1Bg);return new F(function(){return _1B6(_1Be,_1Bh[1],_1Bh[2],_1Bi[1],_1Bi[2]);});},_1Bj=function(_1Bk){return E(E(_1Bk)[4]);},_1Bl=function(_1Bm,_1Bn,_1Bo,_1Bp,_1Bq){switch(B(_1At(_1Bm,_1Bn,_1Bp))){case 0:return false;case 1:return new F(function(){return A(_1Bj,[_1Bm,_1Bo,_1Bq]);});break;default:return true;}},_1Br=function(_1Bs,_1Bt,_1Bu,_1Bv){var _1Bw=E(_1Bu),_1Bx=E(_1Bv);return new F(function(){return _1Bl(_1Bt,_1Bw[1],_1Bw[2],_1Bx[1],_1Bx[2]);});},_1By=function(_1Bz,_1BA,_1BB,_1BC,_1BD){switch(B(_1At(_1Bz,_1BA,_1BC))){case 0:return 0;case 1:return new F(function(){return A(_1Ar,[_1Bz,_1BB,_1BD]);});break;default:return 2;}},_1BE=function(_1BF,_1BG,_1BH,_1BI){var _1BJ=E(_1BH),_1BK=E(_1BI);return new F(function(){return _1By(_1BG,_1BJ[1],_1BJ[2],_1BK[1],_1BK[2]);});},_1BL=function(_1BM,_1BN,_1BO,_1BP){var _1BQ=E(_1BO),_1BR=_1BQ[1],_1BS=_1BQ[2],_1BT=E(_1BP),_1BU=_1BT[1],_1BV=_1BT[2];switch(B(_1At(_1BN,_1BR,_1BU))){case 0:return [0,_1BU,_1BV];case 1:return !B(A(_1AP,[_1BN,_1BS,_1BV]))?[0,_1BR,_1BS]:[0,_1BU,_1BV];default:return [0,_1BR,_1BS];}},_1BW=function(_1BX,_1BY,_1BZ,_1C0){var _1C1=E(_1BZ),_1C2=_1C1[1],_1C3=_1C1[2],_1C4=E(_1C0),_1C5=_1C4[1],_1C6=_1C4[2];switch(B(_1At(_1BY,_1C2,_1C5))){case 0:return [0,_1C2,_1C3];case 1:return !B(A(_1AP,[_1BY,_1C3,_1C6]))?[0,_1C5,_1C6]:[0,_1C2,_1C3];default:return [0,_1C5,_1C6];}},_1C7=function(_1C8,_1C9){return [0,_1C8,function(_ZJ,_ZK){return new F(function(){return _1BE(_1C8,_1C9,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1AI(_1C8,_1C9,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1Br(_1C8,_1C9,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1Bc(_1C8,_1C9,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1AX(_1C8,_1C9,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1BL(_1C8,_1C9,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1BW(_1C8,_1C9,_ZJ,_ZK);});}];},_1Ca=function(_1Cb,_1Cc,_1Cd,_1Ce){return !B(A(_1Cb,[_1Cd,_1Ce]))?B(_cO(B(A(_1Cc,[_1Cd,_16E])),B(A(_1Cc,[_1Ce,_16E]))))==2?false:true:false;},_1Cf=function(_1Cg,_1Ch,_1Ci,_1Cj){return new F(function(){return _1Ca(E(_1Cg)[1],_1Ch,_1Ci,_1Cj);});},_1Ck=function(_1Cl,_1Cm,_1Cn,_1Co){return B(_cO(B(A(_1Cm,[_1Cn,_16E])),B(A(_1Cm,[_1Co,_16E]))))==2?false:true;},_1Cp=function(_1Cq,_1Cr,_1Cs,_1Ct){return !B(A(_1Cq,[_1Cs,_1Ct]))?B(_cO(B(A(_1Cr,[_1Cs,_16E])),B(A(_1Cr,[_1Ct,_16E]))))==2?true:false:false;},_1Cu=function(_1Cv,_1Cw,_1Cx,_1Cy){return new F(function(){return _1Cp(E(_1Cv)[1],_1Cw,_1Cx,_1Cy);});},_1Cz=function(_1CA,_1CB,_1CC,_1CD){return !B(A(_1CA,[_1CC,_1CD]))?B(_cO(B(A(_1CB,[_1CC,_16E])),B(A(_1CB,[_1CD,_16E]))))==2?true:false:true;},_1CE=function(_1CF,_1CG,_1CH,_1CI){return new F(function(){return _1Cz(E(_1CF)[1],_1CG,_1CH,_1CI);});},_1CJ=function(_1CK,_1CL,_1CM,_1CN){return !B(A(_1CK,[_1CM,_1CN]))?B(_cO(B(A(_1CL,[_1CM,_16E])),B(A(_1CL,[_1CN,_16E]))))==2?2:0:1;},_1CO=function(_1CP,_1CQ,_1CR,_1CS){return new F(function(){return _1CJ(E(_1CP)[1],_1CQ,_1CR,_1CS);});},_1CT=function(_1CU,_1CV,_1CW,_1CX){return B(_cO(B(A(_1CV,[_1CW,_16E])),B(A(_1CV,[_1CX,_16E]))))==2?E(_1CW):E(_1CX);},_1CY=function(_1CZ,_1D0,_1D1,_1D2){return B(_cO(B(A(_1D0,[_1D1,_16E])),B(A(_1D0,[_1D2,_16E]))))==2?E(_1D2):E(_1D1);},_1D3=function(_1D4,_1D5){return [0,_1D4,function(_bi,_bj){return new F(function(){return _1CO(_1D4,_1D5,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Cf(_1D4,_1D5,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1CE(_1D4,_1D5,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Cu(_1D4,_1D5,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Ck(_1D4,_1D5,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1CT(_1D4,_1D5,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1CY(_1D4,_1D5,_bi,_bj);});}];},_1D6=function(_1D7,_1D8,_1D9,_1Da,_1Db,_1Dc,_1Dd){var _1De=function(_1Df,_1Dg){return new F(function(){return _af(_1D7,_1D8,_1D9,_1Db,_1Da,_1Dd,_1Dc,_1Df);});};return function(_1Dh,_1Di){var _1Dj=E(_1Dh);if(!_1Dj[0]){var _1Dk=E(_1Di);return _1Dk[0]==0?B(_cO(B(_a1(_1Dj[1])),B(_a1(_1Dk[1]))))==2?false:true:true;}else{var _1Dl=E(_1Di);return _1Dl[0]==0?false:B(_1At(new T(function(){return B(_1D3(new T(function(){return B(_16J(_1De));}),_1De));}),_1Dj[1],_1Dl[1]))==2?false:true;}};},_1Dm=function(_1Dn,_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw){return !B(A(_1D6,[_1Do,_1Dp,_1Dq,_1Dr,_1Ds,_1Dt,_1Du,_1Dv,_1Dw]))?E(_1Dv):E(_1Dw);},_1Dx=function(_1Dy,_1Dz,_1DA,_1DB,_1DC,_1DD,_1DE,_1DF,_1DG,_1DH){return !B(A(_1D6,[_1Dz,_1DA,_1DB,_1DC,_1DD,_1DE,_1DF,_1DG,_1DH]))?E(_1DH):E(_1DG);},_1DI=function(_1DJ,_1DK,_1DL,_1DM,_1DN,_1DO,_1DP){var _1DQ=function(_1DR,_1DS){return new F(function(){return _af(_1DJ,_1DK,_1DL,_1DN,_1DM,_1DP,_1DO,_1DR);});};return function(_1DT,_1DU){var _1DV=E(_1DT);if(!_1DV[0]){var _1DW=_1DV[1],_1DX=E(_1DU);if(!_1DX[0]){var _1DY=_1DX[1];return B(_10r(_1DW,_1DY,_1))[0]==0?B(_cO(B(_a1(_1DW)),B(_a1(_1DY))))==2?false:true:false;}else{return true;}}else{var _1DZ=E(_1DU);return _1DZ[0]==0?false:B(_1At(new T(function(){return B(_1D3(new T(function(){return B(_16J(_1DQ));}),_1DQ));}),_1DV[1],_1DZ[1]))==0?true:false;}};},_1E0=function(_1E1,_1E2,_1E3,_1E4,_1E5,_1E6,_1E7){var _1E8=function(_1E9,_1Ea){return new F(function(){return _af(_1E1,_1E2,_1E3,_1E5,_1E4,_1E7,_1E6,_1E9);});};return function(_1Eb,_1Ec){var _1Ed=E(_1Eb);if(!_1Ed[0]){var _1Ee=_1Ed[1],_1Ef=E(_1Ec);if(!_1Ef[0]){var _1Eg=_1Ef[1];return B(_10r(_1Ee,_1Eg,_1))[0]==0?B(_cO(B(_a1(_1Ee)),B(_a1(_1Eg))))==2?true:false:false;}else{return false;}}else{var _1Eh=E(_1Ec);return _1Eh[0]==0?true:B(_1At(new T(function(){return B(_1D3(new T(function(){return B(_16J(_1E8));}),_1E8));}),_1Ed[1],_1Eh[1]))==2?true:false;}};},_1Ei=function(_1Ej,_1Ek,_1El,_1Em,_1En,_1Eo,_1Ep){var _1Eq=function(_1Er,_1Es){return new F(function(){return _af(_1Ej,_1Ek,_1El,_1En,_1Em,_1Ep,_1Eo,_1Er);});};return function(_1Et,_1Eu){var _1Ev=E(_1Et);if(!_1Ev[0]){var _1Ew=_1Ev[1],_1Ex=E(_1Eu);if(!_1Ex[0]){var _1Ey=_1Ex[1];return B(_10r(_1Ew,_1Ey,_1))[0]==0?B(_cO(B(_a1(_1Ew)),B(_a1(_1Ey))))==2?true:false:true;}else{return false;}}else{var _1Ez=E(_1Eu);return _1Ez[0]==0?true:B(_1At(new T(function(){return B(_1D3(new T(function(){return B(_16J(_1Eq));}),_1Eq));}),_1Ev[1],_1Ez[1]))==0?false:true;}};},_1EA=function(_1EB,_1EC,_1ED,_1EE,_1EF,_1EG,_1EH){var _1EI=function(_1EJ,_1EK){return new F(function(){return _af(_1EB,_1EC,_1ED,_1EF,_1EE,_1EH,_1EG,_1EJ);});};return function(_1EL,_1EM){var _1EN=E(_1EL);if(!_1EN[0]){var _1EO=_1EN[1],_1EP=E(_1EM);if(!_1EP[0]){var _1EQ=_1EP[1];return B(_10r(_1EO,_1EQ,_1))[0]==0?B(_cO(B(_a1(_1EO)),B(_a1(_1EQ))))==2?2:0:1;}else{return 0;}}else{var _1ER=E(_1EM);return _1ER[0]==0?2:B(_1At(new T(function(){return B(_1D3(new T(function(){return B(_16J(_1EI));}),_1EI));}),_1EN[1],_1ER[1]));}};},_1ES=function(_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0){return [0,_1ET,new T(function(){return B(_1EA(_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0));}),new T(function(){return B(_1DI(_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0));}),new T(function(){return B(_1Ei(_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0));}),new T(function(){return B(_1E0(_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0));}),new T(function(){return B(_1D6(_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0));}),function(_bi,_bj){return new F(function(){return _1Dm(_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Dx(_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_bi,_bj);});}];},_1F1=new T(function(){return B(_105(_Q,_u,_Q,_Q,_N,_2,_15));}),_1F2=new T(function(){return B(_1ES(_1F1,_Q,_u,_Q,_Q,_N,_15,_2));}),_1F3=new T(function(){return B(_10p(_1F1));}),_1F4=new T(function(){return B(_1C7(_1F3,_1F2));}),_1F5=function(_1F6,_1F7,_1F8,_1F9){var _1Fa=E(_1F8),_1Fb=E(_1F9);return new F(function(){return _1AC(_1F7,_1Fa[1],_1Fa[2],_1Fb[1],_1Fb[2]);});},_1Fc=function(_1Fd,_1Fe,_1Ff,_1Fg){var _1Fh=E(_1Ff),_1Fi=E(_1Fg);return new F(function(){return _1AR(_1Fe,_1Fh[1],_1Fh[2],_1Fi[1],_1Fi[2]);});},_1Fj=function(_1Fk,_1Fl,_1Fm,_1Fn){var _1Fo=E(_1Fm),_1Fp=E(_1Fn);return new F(function(){return _1B6(_1Fl,_1Fo[1],_1Fo[2],_1Fp[1],_1Fp[2]);});},_1Fq=function(_1Fr,_1Fs,_1Ft,_1Fu){var _1Fv=E(_1Ft),_1Fw=E(_1Fu);return new F(function(){return _1Bl(_1Fs,_1Fv[1],_1Fv[2],_1Fw[1],_1Fw[2]);});},_1Fx=function(_1Fy,_1Fz,_1FA,_1FB){var _1FC=E(_1FA),_1FD=E(_1FB);return new F(function(){return _1By(_1Fz,_1FC[1],_1FC[2],_1FD[1],_1FD[2]);});},_1FE=function(_1FF,_1FG,_1FH,_1FI){var _1FJ=E(_1FH),_1FK=_1FJ[1],_1FL=_1FJ[2],_1FM=E(_1FI),_1FN=_1FM[1],_1FO=_1FM[2];switch(B(_1At(_1FG,_1FK,_1FN))){case 0:return [0,_1FN,_1FO];case 1:return !B(A(_1AP,[_1FG,_1FL,_1FO]))?[0,_1FK,_1FL]:[0,_1FN,_1FO];default:return [0,_1FK,_1FL];}},_1FP=function(_1FQ,_1FR,_1FS,_1FT){var _1FU=E(_1FS),_1FV=_1FU[1],_1FW=_1FU[2],_1FX=E(_1FT),_1FY=_1FX[1],_1FZ=_1FX[2];switch(B(_1At(_1FR,_1FV,_1FY))){case 0:return [0,_1FV,_1FW];case 1:return !B(A(_1AP,[_1FR,_1FW,_1FZ]))?[0,_1FY,_1FZ]:[0,_1FV,_1FW];default:return [0,_1FY,_1FZ];}},_1G0=function(_1G1,_1G2){return [0,_1G1,function(_ZJ,_ZK){return new F(function(){return _1Fx(_1G1,_1G2,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1F5(_1G1,_1G2,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1Fq(_1G1,_1G2,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1Fj(_1G1,_1G2,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1Fc(_1G1,_1G2,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1FE(_1G1,_1G2,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1FP(_1G1,_1G2,_ZJ,_ZK);});}];},_1G3=function(_1G4,_1G5){return B(_cO(_1G4,_1G5))==0?false:true;},_1G6=function(_1G7){return E(E(_1G7)[1]);},_1G8=function(_1G9){return function(_1Ga,_1Gb){var _1Gc=E(_1Ga),_1Gd=E(_1Gb);switch(B(_1At(new T(function(){return B(_1G0(new T(function(){return B(_ZH(new T(function(){return B(_1G6(_1G9));})));}),_1G9));}),_1Gc[1],_1Gd[1]))){case 0:return false;case 1:return new F(function(){return _1G3(_1Gc[2],_1Gd[2]);});break;default:return true;}};},_1Ge=new T(function(){return B(_1G8(_1F4));}),_1Gf=function(_1Gg,_1Gh,_1Gi){var _1Gj=E(_1Gg);if(_1Gj==1){var _1Gk=E(_1Gi);return _1Gk[0]==0?[0,new T(function(){return [0,1,E(E(_1Gh)),E(_1em),E(_1em)];}),_9,_9]:!B(A(_1Ge,[_1Gh,_1Gk[1]]))?[0,new T(function(){return [0,1,E(E(_1Gh)),E(_1em),E(_1em)];}),_1Gk,_9]:[0,new T(function(){return [0,1,E(E(_1Gh)),E(_1em),E(_1em)];}),_9,_1Gk];}else{var _1Gl=B(_1Gf(_1Gj>>1,_1Gh,_1Gi)),_1Gm=_1Gl[1],_1Gn=_1Gl[3],_1Go=E(_1Gl[2]);if(!_1Go[0]){return [0,_1Gm,_9,_1Gn];}else{var _1Gp=_1Go[1],_1Gq=E(_1Go[2]);if(!_1Gq[0]){return [0,new T(function(){return B(_1fJ(_1Gp,_1Gm));}),_9,_1Gn];}else{var _1Gr=_1Gq[1];if(!B(A(_1Ge,[_1Gp,_1Gr]))){var _1Gs=B(_1Gf(_1Gj>>1,_1Gr,_1Gq[2]));return [0,new T(function(){return B(_1gn(_1Gp,_1Gm,_1Gs[1]));}),_1Gs[2],_1Gs[3]];}else{return [0,_1Gm,_9,_1Go];}}}}},_1Gt=function(_1Gu,_1Gv){return B(_cO(_1Gu,_1Gv))==2?false:true;},_1Gw=function(_1Gx){return function(_1Gy,_1Gz){var _1GA=E(_1Gy),_1GB=E(_1Gz);switch(B(_1At(new T(function(){return B(_1G0(new T(function(){return B(_ZH(new T(function(){return B(_1G6(_1Gx));})));}),_1Gx));}),_1GA[1],_1GB[1]))){case 0:return true;case 1:return new F(function(){return _1Gt(_1GA[2],_1GB[2]);});break;default:return false;}};},_1GC=function(_1GD,_1GE,_1GF,_1GG){return !B(A(_1Gw,[_1GE,_1GF,_1GG]))?E(_1GF):E(_1GG);},_1GH=function(_1GI,_1GJ,_1GK,_1GL){return !B(A(_1Gw,[_1GJ,_1GK,_1GL]))?E(_1GL):E(_1GK);},_1GM=function(_1GN,_1GO){return B(_cO(_1GN,_1GO))==0?true:false;},_1GP=function(_1GQ){return function(_1GR,_1GS){var _1GT=E(_1GR),_1GU=E(_1GS);switch(B(_1At(new T(function(){return B(_1G0(new T(function(){return B(_ZH(new T(function(){return B(_1G6(_1GQ));})));}),_1GQ));}),_1GT[1],_1GU[1]))){case 0:return true;case 1:return new F(function(){return _1GM(_1GT[2],_1GU[2]);});break;default:return false;}};},_1GV=function(_1GW,_1GX){return B(_cO(_1GW,_1GX))==2?true:false;},_1GY=function(_1GZ){return function(_1H0,_1H1){var _1H2=E(_1H0),_1H3=E(_1H1);switch(B(_1At(new T(function(){return B(_1G0(new T(function(){return B(_ZH(new T(function(){return B(_1G6(_1GZ));})));}),_1GZ));}),_1H2[1],_1H3[1]))){case 0:return false;case 1:return new F(function(){return _1GV(_1H2[2],_1H3[2]);});break;default:return true;}};},_1H4=function(_1H5){return function(_1H6,_1H7){var _1H8=E(_1H6),_1H9=E(_1H7);switch(B(_1At(new T(function(){return B(_1G0(new T(function(){return B(_ZH(new T(function(){return B(_1G6(_1H5));})));}),_1H5));}),_1H8[1],_1H9[1]))){case 0:return 0;case 1:return new F(function(){return _cO(_1H8[2],_1H9[2]);});break;default:return 2;}};},_1Ha=function(_1Hb,_1Hc){return [0,_1Hb,new T(function(){return B(_1H4(_1Hc));}),new T(function(){return B(_1GP(_1Hc));}),new T(function(){return B(_1G8(_1Hc));}),new T(function(){return B(_1GY(_1Hc));}),new T(function(){return B(_1Gw(_1Hc));}),function(_ZJ,_ZK){return new F(function(){return _1GC(_1Hb,_1Hc,_ZJ,_ZK);});},function(_ZJ,_ZK){return new F(function(){return _1GH(_1Hb,_1Hc,_ZJ,_ZK);});}];},_1Hd=function(_1He,_1Hf,_1Hg,_1Hh,_1Hi){return !B(_Zj(new T(function(){return B(_ZH(_1He));}),_1Hf,_1Hh))?true:!B(_lj(_1Hg,_1Hi))?true:false;},_1Hj=function(_1Hk,_1Hl,_1Hm){var _1Hn=E(_1Hl),_1Ho=E(_1Hm);return new F(function(){return _1Hd(_1Hk,_1Hn[1],_1Hn[2],_1Ho[1],_1Ho[2]);});},_1Hp=function(_1Hq){return function(_1Hr,_1Hs){var _1Ht=E(_1Hr),_1Hu=E(_1Hs);return !B(_Zj(new T(function(){return B(_ZH(_1Hq));}),_1Ht[1],_1Hu[1]))?false:B(_lj(_1Ht[2],_1Hu[2]));};},_1Hv=function(_1Hw){return [0,new T(function(){return B(_1Hp(_1Hw));}),function(_ZJ,_ZK){return new F(function(){return _1Hj(_1Hw,_ZJ,_ZK);});}];},_1Hx=new T(function(){return B(_1Hv(_1F3));}),_1Hy=new T(function(){return B(_1Ha(_1Hx,_1F4));}),_1Hz=function(_1HA,_1HB,_1HC){var _1HD=E(_1HB),_1HE=E(_1HC);if(!_1HE[0]){var _1HF=_1HE[2],_1HG=_1HE[3],_1HH=_1HE[4];switch(B(A(_1Ar,[_1HA,_1HD,_1HF]))){case 0:return new F(function(){return _1er(_1HF,B(_1Hz(_1HA,_1HD,_1HG)),_1HH);});break;case 1:return [0,_1HE[1],E(_1HD),E(_1HG),E(_1HH)];default:return new F(function(){return _1f3(_1HF,_1HG,B(_1Hz(_1HA,_1HD,_1HH)));});}}else{return [0,1,E(_1HD),E(_1em),E(_1em)];}},_1HI=function(_1HJ,_1HK){while(1){var _1HL=E(_1HK);if(!_1HL[0]){return E(_1HJ);}else{var _1HM=B(_1Hz(_1Hy,_1HL[1],_1HJ));_1HK=_1HL[2];_1HJ=_1HM;continue;}}},_1HN=function(_1HO,_1HP,_1HQ){return new F(function(){return _1HI(B(_1Hz(_1Hy,_1HP,_1HO)),_1HQ);});},_1HR=function(_1HS,_1HT,_1HU){while(1){var _1HV=E(_1HU);if(!_1HV[0]){return E(_1HT);}else{var _1HW=_1HV[1],_1HX=E(_1HV[2]);if(!_1HX[0]){return new F(function(){return _1fJ(_1HW,_1HT);});}else{var _1HY=_1HX[1];if(!B(A(_1Ge,[_1HW,_1HY]))){var _1HZ=B(_1Gf(_1HS,_1HY,_1HX[2])),_1I0=_1HZ[1],_1I1=E(_1HZ[3]);if(!_1I1[0]){var _1I2=_1HS<<1,_1I3=B(_1gn(_1HW,_1HT,_1I0));_1HU=_1HZ[2];_1HS=_1I2;_1HT=_1I3;continue;}else{return new F(function(){return _1HN(B(_1gn(_1HW,_1HT,_1I0)),_1I1[1],_1I1[2]);});}}else{return new F(function(){return _1HN(_1HT,_1HW,_1HX);});}}}}},_1I4=function(_1I5,_1I6,_1I7,_1I8){var _1I9=E(_1I8);if(!_1I9[0]){return new F(function(){return _1fJ(_1I7,_1I6);});}else{var _1Ia=_1I9[1];if(!B(A(_1Ge,[_1I7,_1Ia]))){var _1Ib=B(_1Gf(_1I5,_1Ia,_1I9[2])),_1Ic=_1Ib[1],_1Id=E(_1Ib[3]);if(!_1Id[0]){return new F(function(){return _1HR(_1I5<<1,B(_1gn(_1I7,_1I6,_1Ic)),_1Ib[2]);});}else{return new F(function(){return _1HN(B(_1gn(_1I7,_1I6,_1Ic)),_1Id[1],_1Id[2]);});}}else{return new F(function(){return _1HN(_1I6,_1I7,_1I9);});}}},_1Ie=function(_1If){var _1Ig=E(_1If);if(!_1Ig[0]){return [1];}else{var _1Ih=_1Ig[1],_1Ii=E(_1Ig[2]);if(!_1Ii[0]){return [0,1,E(E(_1Ih)),E(_1em),E(_1em)];}else{var _1Ij=_1Ii[1],_1Ik=_1Ii[2];if(!B(A(_1Ge,[_1Ih,_1Ij]))){return new F(function(){return _1I4(1,[0,1,E(E(_1Ih)),E(_1em),E(_1em)],_1Ij,_1Ik);});}else{return new F(function(){return _1HN([0,1,E(E(_1Ih)),E(_1em),E(_1em)],_1Ij,_1Ik);});}}}},_1Il=new T(function(){return B(_F(0,1,_9));}),_1Im=new T(function(){return B(unAppCStr("delta_",_1Il));}),_1In=[9,_,_,_1Im],_1Io=[0,_1In],_1Ip=[1,_1Io,_9],_1Iq=new T(function(){return B(unAppCStr("phi_",_1Il));}),_1Ir=[3,_,_,_1Iq],_1Is=[2,_,_1Ir],_1It=[1,_1Is,_9],_1Iu=[1,_1It],_1Iv=[0,_1Ip,_1Iu],_1Iw=new T(function(){return B(_F(0,2,_9));}),_1Ix=new T(function(){return B(unAppCStr("phi_",_1Iw));}),_1Iy=[3,_,_,_1Ix],_1Iz=[2,_,_1Iy],_1IA=[1,_1Iz,_9],_1IB=[1,_1IA],_1IC=new T(function(){return B(unAppCStr("delta_",_1Iw));}),_1ID=[9,_,_,_1IC],_1IE=[0,_1ID],_1IF=[1,_1IE,_9],_1IG=[0,_1IF,_1IB],_1IH=[1,_1IG,_9],_1II=[1,_1Iv,_1IH],_1IJ=[9,_,_OY,_1Is,_1Iz],_1IK=[1,_1IJ,_9],_1IL=[1,_1IK],_1IM=[1,_1Io,_1IF],_1IN=[0,_1IM,_1IL],_1IO=[0,_1II,_1IN],_1IP=[0,_1IF,_1Iu],_1IQ=[1,_1IP,_9],_1IR=[0,_1Ip,_1IB],_1IS=[1,_1IR,_1IQ],_1IT=[0,_1IS,_1IN],_1IU=[1,_1IT,_9],_1IV=[1,_1IO,_1IU],_1IW=[0,_1IV,_1A7],_1IX=[1,_1Iv,_9],_1IY=[9,_,_OA,_1Is,_1Iz],_1IZ=[1,_1IY,_9],_1J0=[1,_1IZ],_1J1=[0,_1Ip,_1J0],_1J2=[0,_1IX,_1J1],_1J3=[9,_,_OA,_1Iz,_1Is],_1J4=[1,_1J3,_9],_1J5=[1,_1J4],_1J6=[0,_1Ip,_1J5],_1J7=[0,_1IX,_1J6],_1J8=[1,_1J7,_9],_1J9=[1,_1J2,_1J8],_1Ja=[0,_1J9,_1A6],_1Jb=[1,_1Iu,_1IF],_1Jc=[7,_,_Pp,_1Iz],_1Jd=[1,_1Jc,_9],_1Je=[1,_1Jd],_1Jf=[0,_1Jb,_1Je],_1Jg=[1,_1Jf,_9],_1Jh=[1,_1Iu,_1Ip],_1Ji=[0,_1Jh,_1IB],_1Jj=[1,_1Ji,_1Jg],_1Jk=[7,_,_Pp,_1Is],_1Jl=[1,_1Jk,_9],_1Jm=[1,_1Jl],_1Jn=[0,_1IM,_1Jm],_1Jo=[0,_1Jj,_1Jn],_1Jp=[1,_1IR,_1Jg],_1Jq=[0,_1Jp,_1Jn],_1Jr=[0,_1IF,_1Je],_1Js=[1,_1Jr,_9],_1Jt=[1,_1Ji,_1Js],_1Ju=[0,_1Jt,_1Jn],_1Jv=[1,_1IR,_1Js],_1Jw=[0,_1Jv,_1Jn],_1Jx=[1,_1Ji,_9],_1Jy=[1,_1Jf,_1Jx],_1Jz=[0,_1Jy,_1Jn],_1JA=[1,_1Jr,_1Jx],_1JB=[0,_1JA,_1Jn],_1JC=[1,_1IR,_9],_1JD=[1,_1Jf,_1JC],_1JE=[0,_1JD,_1Jn],_1JF=[1,_1Jr,_1JC],_1JG=[0,_1JF,_1Jn],_1JH=[1,_1Jm,_1IF],_1JI=[0,_1JH,_1Je],_1JJ=[1,_1Jm,_1Ip],_1JK=[0,_1JJ,_1IB],_1JL=[1,_1JK,_9],_1JM=[1,_1JI,_1JL],_1JN=[0,_1IM,_1Iu],_1JO=[0,_1JM,_1JN],_1JP=[1,_1Jr,_1JL],_1JQ=[0,_1JP,_1JN],_1JR=[1,_1JI,_1JC],_1JS=[0,_1JR,_1JN],_1JT=[0,_1JF,_1JN],_1JU=[1,_1JT,_9],_1JV=[1,_1JS,_1JU],_1JW=[1,_1JQ,_1JV],_1JX=[1,_1JO,_1JW],_1JY=[1,_1JG,_1JX],_1JZ=[1,_1JE,_1JY],_1K0=[1,_1JB,_1JZ],_1K1=[1,_1Jz,_1K0],_1K2=[1,_1Jw,_1K1],_1K3=[1,_1Ju,_1K2],_1K4=[1,_1Jq,_1K3],_1K5=[1,_1Jo,_1K4],_1K6=[0,_1K5,_1Ah],_1K7=[1,_1K6,_9],_1K8=[1,_1Ja,_1K7],_1K9=[0,83],_1Ka=[1,_1K9,_9],_1Kb=[0,_1Ip,_1IL],_1Kc=[1,_1Kb,_9],_1Kd=[0,_1Kc,_1Iv],_1Ke=[0,_1Kc,_1IR],_1Kf=[1,_1Ke,_9],_1Kg=[1,_1Kd,_1Kf],_1Kh=[0,_1Kg,_1Ka],_1Ki=[1,_1Kh,_1K8],_1Kj=[0,_1IM,_1IB],_1Kk=[0,_1IF,_1Jm],_1Kl=[1,_1Kk,_9],_1Km=[1,_1J6,_1Kl],_1Kn=[0,_1Km,_1Kj],_1Ko=[1,_1J6,_9],_1Kp=[1,_1Kk,_1Ko],_1Kq=[0,_1Kp,_1Kj],_1Kr=[1,_1Kn,_9],_1Ks=[1,_1Kq,_1Kr],_1Kt=[1,_1Kn,_1Ks],_1Ku=[1,_1Kn,_1Kt],_1Kv=[0,_1Ku,_1Af],_1Kw=[1,_1Kv,_1Ki],_1Kx=[9,_,_No,_1Is,_1Iz],_1Ky=[1,_1Kx,_9],_1Kz=[1,_1Ky],_1KA=[0,_1IF,_1Kz],_1KB=[1,_1KA,_9],_1KC=[1,_1Iv,_1KB],_1KD=[0,_1KC,_1Kj],_1KE=[0,_1Ip,_1Kz],_1KF=[1,_1KE,_1IQ],_1KG=[0,_1KF,_1Kj],_1KH=[1,_1KG,_9],_1KI=[1,_1KD,_1KH],_1KJ=[0,_1KI,_1Ag],_1KK=[1,_1KJ,_1Kw],_1KL=[0,_1Jx,_1KE],_1KM=[0,_1JC,_1KE],_1KN=[1,_1KM,_9],_1KO=[1,_1KL,_1KN],_1KP=[0,_1KO,_1Ai],_1KQ=[1,_1KP,_1KK],_1KR=[1,_1IW,_1KQ],_1KS=new T(function(){return B(_1Ie(_1KR));}),_1KT=[0,_1Ao,_1KS],_1KU=function(_){return new F(function(){return _1zJ(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1KT,_);});},_1KV=function(_){return new F(function(){return _1KU(_);});};
var hasteMain = function() {B(A(_1KV, [0]));};window.onload = hasteMain;