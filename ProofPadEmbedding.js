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

var _0=0,_1=function(_){var _2=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_3=_2;return _0;},_4=function(_5,_6,_){var _7=jsGet(_5,toJSStr(E(_6))),_8=_7;return new T(function(){return fromJSStr(_8);});},_9=function(_a,_b,_c,_d){return new F(function(){return A(_a,[function(_){var _e=jsSet(E(_b)[1],toJSStr(E(_c)),toJSStr(E(_d)));return _0;}]);});},_f=[0],_g=[3,_],_h=[13,_],_i=new T(function(){return B(unCStr("wheel"));}),_j=new T(function(){return B(unCStr("mouseout"));}),_k=new T(function(){return B(unCStr("mouseover"));}),_l=new T(function(){return B(unCStr("mousemove"));}),_m=new T(function(){return B(unCStr("blur"));}),_n=new T(function(){return B(unCStr("focus"));}),_o=new T(function(){return B(unCStr("change"));}),_p=new T(function(){return B(unCStr("unload"));}),_q=new T(function(){return B(unCStr("load"));}),_r=new T(function(){return B(unCStr("submit"));}),_s=new T(function(){return B(unCStr("keydown"));}),_t=new T(function(){return B(unCStr("keyup"));}),_u=new T(function(){return B(unCStr("keypress"));}),_v=new T(function(){return B(unCStr("mouseup"));}),_w=new T(function(){return B(unCStr("mousedown"));}),_x=new T(function(){return B(unCStr("dblclick"));}),_y=new T(function(){return B(unCStr("click"));}),_z=function(_A){switch(E(_A)[0]){case 0:return E(_q);case 1:return E(_p);case 2:return E(_o);case 3:return E(_n);case 4:return E(_m);case 5:return E(_l);case 6:return E(_k);case 7:return E(_j);case 8:return E(_y);case 9:return E(_x);case 10:return E(_w);case 11:return E(_v);case 12:return E(_u);case 13:return E(_t);case 14:return E(_s);case 15:return E(_r);default:return E(_i);}},_B=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_C=new T(function(){return B(unCStr("hplayground-0.1.2.2"));}),_D=new T(function(){return B(unCStr("EventData"));}),_E=new T(function(){var _F=hs_wordToWord64(736961551),_G=_F,_H=hs_wordToWord64(735248784),_I=_H;return [0,_G,_I,[0,_G,_I,_C,_B,_D],_f];}),_J=[0,0],_K=false,_L=2,_M=[1],_N=new T(function(){return B(unCStr("Dynamic"));}),_O=new T(function(){return B(unCStr("Data.Dynamic"));}),_P=new T(function(){return B(unCStr("base"));}),_Q=new T(function(){var _R=hs_wordToWord64(628307645),_S=_R,_T=hs_wordToWord64(949574464),_U=_T;return [0,_S,_U,[0,_S,_U,_P,_O,_N],_f];}),_V=[0],_W=new T(function(){return B(unCStr("OnLoad"));}),_X=[0,_W,_V],_Y=[0,_E,_X],_Z=[0,_Q,_Y],_10=[0],_11=function(_){return _10;},_12=function(_13,_){return _10;},_14=[0,_11,_12],_15=[0,_f,_J,_L,_14,_K,_Z,_M],_16=function(_){var _=0,_17=newMVar(),_18=_17,_=putMVar(_18,_15);return [0,_18];},_19=function(_1a){var _1b=B(A(_1a,[_])),_1c=_1b;return E(_1c);},_1d=new T(function(){return B(_19(_16));}),_1e=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1f=new T(function(){return B(unCStr("base"));}),_1g=new T(function(){return B(unCStr("PatternMatchFail"));}),_1h=new T(function(){var _1i=hs_wordToWord64(18445595),_1j=_1i,_1k=hs_wordToWord64(52003073),_1l=_1k;return [0,_1j,_1l,[0,_1j,_1l,_1f,_1e,_1g],_f];}),_1m=function(_1n){return E(_1h);},_1o=function(_1p){return E(E(_1p)[1]);},_1q=function(_1r,_1s,_1t){var _1u=B(A(_1r,[_])),_1v=B(A(_1s,[_])),_1w=hs_eqWord64(_1u[1],_1v[1]),_1x=_1w;if(!E(_1x)){return [0];}else{var _1y=hs_eqWord64(_1u[2],_1v[2]),_1z=_1y;return E(_1z)==0?[0]:[1,_1t];}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1q(B(_1o(_1C[1])),_1m,_1C[2]);});},_1D=function(_1E){return E(E(_1E)[1]);},_1F=function(_1G,_1H){var _1I=E(_1G);return _1I[0]==0?E(_1H):[1,_1I[1],new T(function(){return B(_1F(_1I[2],_1H));})];},_1J=function(_1K,_1L){return new F(function(){return _1F(E(_1K)[1],_1L);});},_1M=[0,44],_1N=[0,93],_1O=[0,91],_1P=function(_1Q,_1R,_1S){var _1T=E(_1R);return _1T[0]==0?B(unAppCStr("[]",_1S)):[1,_1O,new T(function(){return B(A(_1Q,[_1T[1],new T(function(){var _1U=function(_1V){var _1W=E(_1V);return _1W[0]==0?E([1,_1N,_1S]):[1,_1M,new T(function(){return B(A(_1Q,[_1W[1],new T(function(){return B(_1U(_1W[2]));})]));})];};return B(_1U(_1T[2]));})]));})];},_1X=function(_1Y,_1Z){return new F(function(){return _1P(_1J,_1Y,_1Z);});},_20=function(_21,_22,_23){return new F(function(){return _1F(E(_22)[1],_23);});},_24=[0,_20,_1D,_1X],_25=new T(function(){return [0,_1m,_24,_26,_1A];}),_26=function(_27){return [0,_25,_27];},_28=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_29=function(_2a,_2b){return new F(function(){return die(new T(function(){return B(A(_2b,[_2a]));}));});},_2c=function(_2d,_2e){var _2f=E(_2e);if(!_2f[0]){return [0,_f,_f];}else{var _2g=_2f[1];if(!B(A(_2d,[_2g]))){return [0,_f,_2f];}else{var _2h=new T(function(){var _2i=B(_2c(_2d,_2f[2]));return [0,_2i[1],_2i[2]];});return [0,[1,_2g,new T(function(){return E(E(_2h)[1]);})],new T(function(){return E(E(_2h)[2]);})];}}},_2j=[0,32],_2k=[0,10],_2l=[1,_2k,_f],_2m=function(_2n){return E(E(_2n)[1])==124?false:true;},_2o=function(_2p,_2q){var _2r=B(_2c(_2m,B(unCStr(_2p)))),_2s=_2r[1],_2t=function(_2u,_2v){return new F(function(){return _1F(_2u,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1F(_2q,new T(function(){return B(_1F(_2v,_2l));},1)));})));},1));});},_2w=E(_2r[2]);if(!_2w[0]){return new F(function(){return _2t(_2s,_f);});}else{return E(E(_2w[1])[1])==124?B(_2t(_2s,[1,_2j,_2w[2]])):B(_2t(_2s,_f));}},_2x=function(_2y){return new F(function(){return _29([0,new T(function(){return B(_2o(_2y,_28));})],_26);});},_2z=new T(function(){return B(_2x("src/Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_2A=[0,_q,_V],_2B=[0,_E,_2A],_2C=[0,_p,_V],_2D=[0,_E,_2C],_2E=[0,_o,_V],_2F=[0,_E,_2E],_2G=[0,_n,_V],_2H=[0,_E,_2G],_2I=[0,_m,_V],_2J=[0,_E,_2I],_2K=[3],_2L=[0,_j,_2K],_2M=[0,_E,_2L],_2N=function(_2O,_2P){switch(E(_2O)[0]){case 0:return function(_){var _2Q=E(_1d)[1],_2R=takeMVar(_2Q),_2S=_2R,_=putMVar(_2Q,new T(function(){var _2T=E(_2S);return [0,_2T[1],_2T[2],_2T[3],_2T[4],_2T[5],_2B,_2T[7]];}));return new F(function(){return A(_2P,[_]);});};case 1:return function(_){var _2U=E(_1d)[1],_2V=takeMVar(_2U),_2W=_2V,_=putMVar(_2U,new T(function(){var _2X=E(_2W);return [0,_2X[1],_2X[2],_2X[3],_2X[4],_2X[5],_2D,_2X[7]];}));return new F(function(){return A(_2P,[_]);});};case 2:return function(_){var _2Y=E(_1d)[1],_2Z=takeMVar(_2Y),_30=_2Z,_=putMVar(_2Y,new T(function(){var _31=E(_30);return [0,_31[1],_31[2],_31[3],_31[4],_31[5],_2F,_31[7]];}));return new F(function(){return A(_2P,[_]);});};case 3:return function(_){var _32=E(_1d)[1],_33=takeMVar(_32),_34=_33,_=putMVar(_32,new T(function(){var _35=E(_34);return [0,_35[1],_35[2],_35[3],_35[4],_35[5],_2H,_35[7]];}));return new F(function(){return A(_2P,[_]);});};case 4:return function(_){var _36=E(_1d)[1],_37=takeMVar(_36),_38=_37,_=putMVar(_36,new T(function(){var _39=E(_38);return [0,_39[1],_39[2],_39[3],_39[4],_39[5],_2J,_39[7]];}));return new F(function(){return A(_2P,[_]);});};case 5:return function(_3a){return function(_){var _3b=E(_1d)[1],_3c=takeMVar(_3b),_3d=_3c,_=putMVar(_3b,new T(function(){var _3e=E(_3d);return [0,_3e[1],_3e[2],_3e[3],_3e[4],_3e[5],[0,_E,[0,_l,[2,E(_3a)]]],_3e[7]];}));return new F(function(){return A(_2P,[_]);});};};case 6:return function(_3f){return function(_){var _3g=E(_1d)[1],_3h=takeMVar(_3g),_3i=_3h,_=putMVar(_3g,new T(function(){var _3j=E(_3i);return [0,_3j[1],_3j[2],_3j[3],_3j[4],_3j[5],[0,_E,[0,_k,[2,E(_3f)]]],_3j[7]];}));return new F(function(){return A(_2P,[_]);});};};case 7:return function(_){var _3k=E(_1d)[1],_3l=takeMVar(_3k),_3m=_3l,_=putMVar(_3k,new T(function(){var _3n=E(_3m);return [0,_3n[1],_3n[2],_3n[3],_3n[4],_3n[5],_2M,_3n[7]];}));return new F(function(){return A(_2P,[_]);});};case 8:return function(_3o,_3p){return function(_){var _3q=E(_1d)[1],_3r=takeMVar(_3q),_3s=_3r,_=putMVar(_3q,new T(function(){var _3t=E(_3s);return [0,_3t[1],_3t[2],_3t[3],_3t[4],_3t[5],[0,_E,[0,_y,[1,_3o,E(_3p)]]],_3t[7]];}));return new F(function(){return A(_2P,[_]);});};};case 9:return function(_3u,_3v){return function(_){var _3w=E(_1d)[1],_3x=takeMVar(_3w),_3y=_3x,_=putMVar(_3w,new T(function(){var _3z=E(_3y);return [0,_3z[1],_3z[2],_3z[3],_3z[4],_3z[5],[0,_E,[0,_x,[1,_3u,E(_3v)]]],_3z[7]];}));return new F(function(){return A(_2P,[_]);});};};case 10:return function(_3A,_3B){return function(_){var _3C=E(_1d)[1],_3D=takeMVar(_3C),_3E=_3D,_=putMVar(_3C,new T(function(){var _3F=E(_3E);return [0,_3F[1],_3F[2],_3F[3],_3F[4],_3F[5],[0,_E,[0,_w,[1,_3A,E(_3B)]]],_3F[7]];}));return new F(function(){return A(_2P,[_]);});};};case 11:return function(_3G,_3H){return function(_){var _3I=E(_1d)[1],_3J=takeMVar(_3I),_3K=_3J,_=putMVar(_3I,new T(function(){var _3L=E(_3K);return [0,_3L[1],_3L[2],_3L[3],_3L[4],_3L[5],[0,_E,[0,_v,[1,_3G,E(_3H)]]],_3L[7]];}));return new F(function(){return A(_2P,[_]);});};};case 12:return function(_3M,_){var _3N=E(_1d)[1],_3O=takeMVar(_3N),_3P=_3O,_=putMVar(_3N,new T(function(){var _3Q=E(_3P);return [0,_3Q[1],_3Q[2],_3Q[3],_3Q[4],_3Q[5],[0,_E,[0,_u,[4,_3M]]],_3Q[7]];}));return new F(function(){return A(_2P,[_]);});};case 13:return function(_3R,_){var _3S=E(_1d)[1],_3T=takeMVar(_3S),_3U=_3T,_=putMVar(_3S,new T(function(){var _3V=E(_3U);return [0,_3V[1],_3V[2],_3V[3],_3V[4],_3V[5],[0,_E,[0,_t,[4,_3R]]],_3V[7]];}));return new F(function(){return A(_2P,[_]);});};case 14:return function(_3W,_){var _3X=E(_1d)[1],_3Y=takeMVar(_3X),_3Z=_3Y,_=putMVar(_3X,new T(function(){var _40=E(_3Z);return [0,_40[1],_40[2],_40[3],_40[4],_40[5],[0,_E,[0,_s,[4,_3W]]],_40[7]];}));return new F(function(){return A(_2P,[_]);});};default:return E(_2z);}},_41=[0,_z,_2N],_42=function(_43,_44,_45,_46){return new F(function(){return A(_43,[function(_){var _47=jsSetAttr(E(_44)[1],toJSStr(E(_45)),toJSStr(E(_46)));return _0;}]);});},_48=function(_49,_4a){var _4b=jsShowI(_49),_4c=_4b;return new F(function(){return _1F(fromJSStr(_4c),_4a);});},_4d=[0,41],_4e=[0,40],_4f=function(_4g,_4h,_4i){if(_4h>=0){return new F(function(){return _48(_4h,_4i);});}else{return _4g<=6?B(_48(_4h,_4i)):[1,_4e,new T(function(){var _4j=jsShowI(_4h),_4k=_4j;return B(_1F(fromJSStr(_4k),[1,_4d,_4i]));})];}},_4l=[0,112],_4m=function(_4n){var _4o=new T(function(){return E(E(_4n)[2]);});return function(_4p,_){return [0,[1,_4l,new T(function(){return B(_1F(B(_4f(0,E(_4o)[1],_f)),new T(function(){return E(E(_4n)[1]);},1)));})],new T(function(){var _4q=E(_4n);return [0,_4q[1],new T(function(){return [0,E(_4o)[1]+1|0];}),_4q[3],_4q[4],_4q[5],_4q[6],_4q[7]];})];};},_4r=new T(function(){return B(unCStr("id"));}),_4s=function(_4t){return E(_4t);},_4u=new T(function(){return B(unCStr("noid"));}),_4v=function(_4w,_){return _4w;},_4x=function(_4y,_4z,_){var _4A=jsFind(toJSStr(E(_4z))),_4B=_4A,_4C=E(_4B);if(!_4C[0]){var _4D=E(_1d)[1],_4E=takeMVar(_4D),_4F=_4E,_4G=B(A(_4y,[_4F,_])),_4H=_4G,_4I=E(_4H),_=putMVar(_4D,_4I[2]);return E(_4I[1])[2];}else{var _4J=E(_4C[1]),_4K=jsClearChildren(_4J[1]),_4L=E(_1d)[1],_4M=takeMVar(_4L),_4N=_4M,_4O=B(A(_4y,[_4N,_])),_4P=_4O,_4Q=E(_4P),_4R=E(_4Q[1]),_=putMVar(_4L,_4Q[2]),_4S=B(A(_4R[1],[_4J,_])),_4T=_4S;return _4R[2];}},_4U=new T(function(){return B(unCStr("span"));}),_4V=function(_4W,_4X,_4Y,_){var _4Z=jsCreateElem(toJSStr(E(_4U))),_50=_4Z,_51=jsAppendChild(_50,E(_4Y)[1]),_52=[0,_50],_53=B(A(_4W,[_4X,_52,_])),_54=_53;return _52;},_55=function(_56){return E(_56);},_57=function(_58,_59,_5a,_){var _5b=B(A(_4m,[_5a,_5a,_])),_5c=_5b,_5d=E(_5c),_5e=_5d[1],_5f=E(_5d[2]),_5g=_5f[2],_5h=E(_5f[4]),_5i=B(A(_58,[[0,_5f[1],_5g,_5f[3],[0,function(_){return new F(function(){return _4x(function(_5j,_){var _5k=B(A(_58,[new T(function(){var _5l=E(_5j);return [0,_5l[1],_5g,_5l[3],_5l[4],_5l[5],_5l[6],_5l[7]];}),_])),_5m=_5k;return [0,[0,_4v,E(E(_5m)[1])[2]],_5j];},_4u,_);});},function(_5n,_){var _5o=B(_4x(new T(function(){return B(A(_59,[_5n]));},1),_5e,_)),_5p=_5o,_5q=E(_5p);return _5q[0]==0?_10:B(A(_5h[2],[_5q[1],_]));}],_5f[5],_5f[6],_5f[7]],_])),_5r=_5i,_5s=E(_5r),_5t=_5s[2],_5u=E(_5s[1]),_5v=_5u[1],_5w=E(_5u[2]);if(!_5w[0]){return [0,[0,function(_5x,_){var _5y=B(A(_5v,[_5x,_])),_5z=_5y;if(!E(E(_5a)[5])){var _5A=B(_4V(_55,_4v,_5x,_)),_5B=_5A,_5C=B(A(_42,[_4s,_5B,_4r,_5e,_])),_5D=_5C;return _5x;}else{return _5x;}},_10],new T(function(){var _5E=E(_5t);return [0,_5E[1],_5E[2],_5E[3],_5h,_5E[5],_5E[6],_5E[7]];})];}else{var _5F=B(A(_59,[_5w[1],new T(function(){var _5G=E(_5t);return [0,_5G[1],_5G[2],_5G[3],_5h,_5G[5],_5G[6],_5G[7]];}),_])),_5H=_5F,_5I=E(_5H),_5J=E(_5I[1]),_5K=_5J[1];return [0,[0,function(_5L,_){var _5M=B(A(_5v,[_5L,_])),_5N=_5M;if(!E(E(_5a)[5])){var _5O=B(_4V(_55,_5K,_5L,_)),_5P=_5O,_5Q=B(A(_42,[_4s,_5P,_4r,_5e,_])),_5R=_5Q;return _5L;}else{var _5S=B(A(_5K,[_5L,_])),_5T=_5S;return _5L;}},_5J[2]],_5I[2]];}},_5U=function(_5V,_5W,_){var _5X=jsCreateTextNode(toJSStr(E(_5V))),_5Y=_5X,_5Z=jsAppendChild(_5Y,E(_5W)[1]);return [0,_5Y];},_60=new T(function(){return B(unCStr("Prelude.undefined"));}),_61=new T(function(){return B(err(_60));}),_62=function(_63,_64){return E(_61);},_65=new T(function(){return B(unCStr(" \u2194 "));}),_66=new T(function(){return B(unCStr(" \u2192 "));}),_67=new T(function(){return B(unCStr(" \u2228 "));}),_68=[0,41],_69=[1,_68,_f],_6a=new T(function(){return B(unCStr(" \u2227 "));}),_6b=[0,40],_6c=[0,172],_6d=function(_6e,_6f){switch(E(_6e)[0]){case 0:var _6g=E(_6f);return _6g[0]==0?E(_61):E(_6g[2])[0]==0?[0,_6c,_6g[1]]:E(_61);case 1:var _6h=E(_6f);if(!_6h[0]){return E(_61);}else{var _6i=E(_6h[2]);return _6i[0]==0?E(_61):E(_6i[2])[0]==0?[0,_6b,new T(function(){return B(_1F(_6h[1],new T(function(){return B(_1F(_6a,new T(function(){return B(_1F(_6i[1],_69));},1)));},1)));})]:E(_61);}break;case 2:var _6j=E(_6f);if(!_6j[0]){return E(_61);}else{var _6k=E(_6j[2]);return _6k[0]==0?E(_61):E(_6k[2])[0]==0?[0,_6b,new T(function(){return B(_1F(_6j[1],new T(function(){return B(_1F(_67,new T(function(){return B(_1F(_6k[1],_69));},1)));},1)));})]:E(_61);}break;case 3:var _6l=E(_6f);if(!_6l[0]){return E(_61);}else{var _6m=E(_6l[2]);return _6m[0]==0?E(_61):E(_6m[2])[0]==0?[0,_6b,new T(function(){return B(_1F(_6l[1],new T(function(){return B(_1F(_66,new T(function(){return B(_1F(_6m[1],_69));},1)));},1)));})]:E(_61);}break;default:var _6n=E(_6f);if(!_6n[0]){return E(_61);}else{var _6o=E(_6n[2]);return _6o[0]==0?E(_61):E(_6o[2])[0]==0?[0,_6b,new T(function(){return B(_1F(_6n[1],new T(function(){return B(_1F(_65,new T(function(){return B(_1F(_6o[1],_69));},1)));},1)));})]:E(_61);}}},_6p=function(_6q,_6r){var _6s=B(_6d(_6q,_6r));return [1,_6s[1],_6s[2]];},_6t=function(_6u){return new F(function(){return unAppCStr("P_",new T(function(){return B(_4f(0,E(E(_6u)[2])[1],_f));}));});},_6v=function(_6w,_6x){return new F(function(){return _6t(_6w);});},_6y=function(_6z){return E(_61);},_6A=[0,_],_6B=function(_6C){return [1,_,_6C];},_6D=[0,_],_6E=function(_6F){return [1,_,_6F];},_6G=function(_6H){var _6I=E(_6H);switch(_6I[0]){case 0:return E(_6D);case 1:return new F(function(){return _6E(_6I[1]);});break;case 2:return [3,_,_6I[1],new T(function(){return B(_6G(_6I[2]));})];default:return [5,_,_6I[1],new T(function(){return B(_6G(_6I[2]));}),new T(function(){return B(_6G(_6I[3]));})];}},_6J=function(_6K){var _6L=E(_6K);switch(_6L[0]){case 0:return E(_6A);case 1:return new F(function(){return _6B(_6L[1]);});break;case 2:return [3,_,_6L[1],new T(function(){return B(_6G(_6L[2]));})];case 3:return [5,_,_6L[1],new T(function(){return B(_6G(_6L[2]));}),new T(function(){return B(_6G(_6L[3]));})];case 4:return [7,_,_6L[1],new T(function(){return B(_6J(_6L[2]));})];case 5:return [9,_,_6L[1],new T(function(){return B(_6J(_6L[2]));}),new T(function(){return B(_6J(_6L[3]));})];default:return [11,_,_6L[1],function(_6M){return new F(function(){return _6J(B(A(_6L[2],[_6M])));});}];}},_6N=function(_6O){return E(_61);},_6P=function(_6Q,_6R){switch(E(_6Q)[0]){case 0:switch(E(_6R)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_6R)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_6R)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_6R)[0]==3?1:2;}},_6S=new T(function(){return B(unCStr("end of input"));}),_6T=new T(function(){return B(unCStr("unexpected"));}),_6U=new T(function(){return B(unCStr("expecting"));}),_6V=new T(function(){return B(unCStr("unknown parse error"));}),_6W=new T(function(){return B(unCStr("or"));}),_6X=[0,58],_6Y=[0,34],_6Z=[0,41],_70=[1,_6Z,_f],_71=function(_72,_73,_74){var _75=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_1F(B(_4f(0,_73,_f)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_1F(B(_4f(0,_74,_f)),_70));})));},1)));})));}),_76=E(_72);return _76[0]==0?E(_75):[1,_6Y,new T(function(){return B(_1F(_76,new T(function(){return B(unAppCStr("\" ",_75));},1)));})];},_77=function(_78,_79){while(1){var _7a=E(_78);if(!_7a[0]){return E(_79)[0]==0?true:false;}else{var _7b=E(_79);if(!_7b[0]){return false;}else{if(E(_7a[1])[1]!=E(_7b[1])[1]){return false;}else{_78=_7a[2];_79=_7b[2];continue;}}}}},_7c=function(_7d,_7e){return !B(_77(_7d,_7e))?true:false;},_7f=[0,_77,_7c],_7g=function(_7h,_7i,_7j){var _7k=E(_7j);if(!_7k[0]){return E(_7i);}else{return new F(function(){return _1F(_7i,new T(function(){return B(_1F(_7h,new T(function(){return B(_7g(_7h,_7k[1],_7k[2]));},1)));},1));});}},_7l=function(_7m){return E(_7m)[0]==0?false:true;},_7n=new T(function(){return B(unCStr(", "));}),_7o=function(_7p){var _7q=E(_7p);if(!_7q[0]){return [0];}else{return new F(function(){return _1F(_7q[1],new T(function(){return B(_7o(_7q[2]));},1));});}},_7r=function(_7s,_7t){while(1){var _7u=(function(_7v,_7w){var _7x=E(_7w);if(!_7x[0]){return [0];}else{var _7y=_7x[1],_7z=_7x[2];if(!B(A(_7v,[_7y]))){var _7A=_7v;_7t=_7z;_7s=_7A;return null;}else{return [1,_7y,new T(function(){return B(_7r(_7v,_7z));})];}}})(_7s,_7t);if(_7u!=null){return _7u;}}},_7B=function(_7C,_7D){var _7E=E(_7D);return _7E[0]==0?[0]:[1,_7C,new T(function(){return B(_7B(_7E[1],_7E[2]));})];},_7F=function(_7G,_7H){while(1){var _7I=E(_7H);if(!_7I[0]){return E(_7G);}else{_7G=_7I[1];_7H=_7I[2];continue;}}},_7J=function(_7K){switch(E(_7K)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_7L=function(_7M){return E(_7M)[0]==1?true:false;},_7N=function(_7O){return E(_7O)[0]==2?true:false;},_7P=[0,10],_7Q=[1,_7P,_f],_7R=function(_7S){return new F(function(){return _1F(_7Q,_7S);});},_7T=[0,32],_7U=function(_7V,_7W){var _7X=E(_7W);return _7X[0]==0?[0]:[1,new T(function(){return B(A(_7V,[_7X[1]]));}),new T(function(){return B(_7U(_7V,_7X[2]));})];},_7Y=function(_7Z){var _80=E(_7Z);switch(_80[0]){case 0:return E(_80[1]);case 1:return E(_80[1]);case 2:return E(_80[1]);default:return E(_80[1]);}},_81=function(_82){return E(E(_82)[1]);},_83=function(_84,_85,_86){while(1){var _87=E(_86);if(!_87[0]){return false;}else{if(!B(A(_81,[_84,_85,_87[1]]))){_86=_87[2];continue;}else{return true;}}}},_88=function(_89,_8a){var _8b=function(_8c,_8d){while(1){var _8e=(function(_8f,_8g){var _8h=E(_8f);if(!_8h[0]){return [0];}else{var _8i=_8h[1],_8j=_8h[2];if(!B(_83(_89,_8i,_8g))){return [1,_8i,new T(function(){return B(_8b(_8j,[1,_8i,_8g]));})];}else{_8c=_8j;var _8k=_8g;_8d=_8k;return null;}}})(_8c,_8d);if(_8e!=null){return _8e;}}};return new F(function(){return _8b(_8a,_f);});},_8l=function(_8m,_8n,_8o,_8p,_8q,_8r){var _8s=E(_8r);if(!_8s[0]){return E(_8n);}else{var _8t=new T(function(){var _8u=B(_2c(_7J,_8s));return [0,_8u[1],_8u[2]];}),_8v=new T(function(){var _8w=B(_2c(_7L,E(_8t)[2]));return [0,_8w[1],_8w[2]];}),_8x=new T(function(){return E(E(_8v)[1]);}),_8y=function(_8z,_8A){var _8B=E(_8A);if(!_8B[0]){return E(_8z);}else{var _8C=new T(function(){return B(_1F(_8m,[1,_7T,new T(function(){return B(_7F(_8z,_8B));})]));}),_8D=B(_88(_7f,B(_7r(_7l,B(_7B(_8z,_8B))))));if(!_8D[0]){return new F(function(){return _1F(_f,[1,_7T,_8C]);});}else{var _8E=_8D[1],_8F=E(_8D[2]);if(!_8F[0]){return new F(function(){return _1F(_8E,[1,_7T,_8C]);});}else{return new F(function(){return _1F(B(_1F(_8E,new T(function(){return B(_1F(_7n,new T(function(){return B(_7g(_7n,_8F[1],_8F[2]));},1)));},1))),[1,_7T,_8C]);});}}}},_8G=function(_8H,_8I){var _8J=B(_88(_7f,B(_7r(_7l,B(_7U(_7Y,_8I))))));if(!_8J[0]){return [0];}else{var _8K=_8J[1],_8L=_8J[2],_8M=E(_8H);return _8M[0]==0?B(_8y(_8K,_8L)):B(_1F(_8M,[1,_7T,new T(function(){return B(_8y(_8K,_8L));})]));}},_8N=new T(function(){var _8O=B(_2c(_7N,E(_8v)[2]));return [0,_8O[1],_8O[2]];});return new F(function(){return _7o(B(_7U(_7R,B(_88(_7f,B(_7r(_7l,[1,new T(function(){if(!E(_8x)[0]){var _8P=E(E(_8t)[1]);if(!_8P[0]){var _8Q=[0];}else{var _8R=E(_8P[1]);switch(_8R[0]){case 0:var _8S=E(_8R[1]),_8T=_8S[0]==0?B(_1F(_8p,[1,_7T,_8q])):B(_1F(_8p,[1,_7T,_8S]));break;case 1:var _8U=E(_8R[1]),_8T=_8U[0]==0?B(_1F(_8p,[1,_7T,_8q])):B(_1F(_8p,[1,_7T,_8U]));break;case 2:var _8V=E(_8R[1]),_8T=_8V[0]==0?B(_1F(_8p,[1,_7T,_8q])):B(_1F(_8p,[1,_7T,_8V]));break;default:var _8W=E(_8R[1]),_8T=_8W[0]==0?B(_1F(_8p,[1,_7T,_8q])):B(_1F(_8p,[1,_7T,_8W]));}var _8Q=_8T;}var _8X=_8Q,_8Y=_8X;}else{var _8Y=[0];}return _8Y;}),[1,new T(function(){return B(_8G(_8p,_8x));}),[1,new T(function(){return B(_8G(_8o,E(_8N)[1]));}),[1,new T(function(){return B((function(_8Z){var _90=B(_88(_7f,B(_7r(_7l,B(_7U(_7Y,_8Z))))));return _90[0]==0?[0]:B(_8y(_90[1],_90[2]));})(E(_8N)[2]));}),_f]]]])))))));});}},_91=[1,_f,_f],_92=function(_93,_94){var _95=function(_96,_97){var _98=E(_96);if(!_98[0]){return E(_97);}else{var _99=_98[1],_9a=E(_97);if(!_9a[0]){return E(_98);}else{var _9b=_9a[1];return B(A(_93,[_99,_9b]))==2?[1,_9b,new T(function(){return B(_95(_98,_9a[2]));})]:[1,_99,new T(function(){return B(_95(_98[2],_9a));})];}}},_9c=function(_9d){var _9e=E(_9d);if(!_9e[0]){return [0];}else{var _9f=E(_9e[2]);return _9f[0]==0?E(_9e):[1,new T(function(){return B(_95(_9e[1],_9f[1]));}),new T(function(){return B(_9c(_9f[2]));})];}},_9g=function(_9h){while(1){var _9i=E(_9h);if(!_9i[0]){return E(new T(function(){return B(_9g(B(_9c(_f))));}));}else{if(!E(_9i[2])[0]){return E(_9i[1]);}else{_9h=B(_9c(_9i));continue;}}}},_9j=new T(function(){return B(_9k(_f));}),_9k=function(_9l){var _9m=E(_9l);if(!_9m[0]){return E(_91);}else{var _9n=_9m[1],_9o=E(_9m[2]);if(!_9o[0]){return [1,_9m,_f];}else{var _9p=_9o[1],_9q=_9o[2];if(B(A(_93,[_9n,_9p]))==2){return new F(function(){return (function(_9r,_9s,_9t){while(1){var _9u=(function(_9v,_9w,_9x){var _9y=E(_9x);if(!_9y[0]){return [1,[1,_9v,_9w],_9j];}else{var _9z=_9y[1];if(B(A(_93,[_9v,_9z]))==2){_9r=_9z;var _9A=[1,_9v,_9w];_9t=_9y[2];_9s=_9A;return null;}else{return [1,[1,_9v,_9w],new T(function(){return B(_9k(_9y));})];}}})(_9r,_9s,_9t);if(_9u!=null){return _9u;}}})(_9p,[1,_9n,_f],_9q);});}else{return new F(function(){return (function(_9B,_9C,_9D){while(1){var _9E=(function(_9F,_9G,_9H){var _9I=E(_9H);if(!_9I[0]){return [1,new T(function(){return B(A(_9G,[[1,_9F,_f]]));}),_9j];}else{var _9J=_9I[1],_9K=_9I[2];switch(B(A(_93,[_9F,_9J]))){case 0:_9B=_9J;_9C=function(_9L){return new F(function(){return A(_9G,[[1,_9F,_9L]]);});};_9D=_9K;return null;case 1:_9B=_9J;_9C=function(_9M){return new F(function(){return A(_9G,[[1,_9F,_9M]]);});};_9D=_9K;return null;default:return [1,new T(function(){return B(A(_9G,[[1,_9F,_f]]));}),new T(function(){return B(_9k(_9I));})];}}})(_9B,_9C,_9D);if(_9E!=null){return _9E;}}})(_9p,function(_9N){return [1,_9n,_9N];},_9q);});}}}};return new F(function(){return _9g(B(_9k(_94)));});},_9O=function(_9P,_9Q,_9R,_9S){return new F(function(){return _1F(B(_71(_9P,_9Q,_9R)),[1,_6X,new T(function(){return B(_8l(_6W,_6V,_6U,_6T,_6S,B(_92(_6P,_9S))));})]);});},_9T=function(_9U){var _9V=E(_9U),_9W=E(_9V[1]);return new F(function(){return _9O(_9W[1],_9W[2],_9W[3],_9V[2]);});},_9X=function(_9Y,_9Z){switch(E(_9Y)[0]){case 0:return E(_9Z)[0]==0?true:false;case 1:return E(_9Z)[0]==1?true:false;case 2:return E(_9Z)[0]==2?true:false;case 3:return E(_9Z)[0]==3?true:false;default:return E(_9Z)[0]==4?true:false;}},_a0=function(_a1,_a2){return E(_a1)[1]==E(_a2)[1];},_a3=function(_a4,_a5){return new F(function(){return _a0(E(_a4)[2],E(_a5)[2]);});},_a6=function(_a7,_a8){return E(_61);},_a9=new T(function(){return B(unCStr(" . "));}),_aa=function(_ab){var _ac=E(_ab);switch(_ac[0]){case 0:return E(_ac[3]);case 1:return E(_ac[3]);case 2:return E(_ac[3]);case 3:return E(_ac[3]);case 4:return E(_ac[3]);case 5:return E(_ac[3]);case 6:return E(_ac[3]);case 7:return E(_ac[3]);case 8:return E(_ac[3]);default:return E(_ac[3]);}},_ad=[0,41],_ae=[1,_ad,_f],_af=new T(function(){return B(_2x("AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_ag=[0,44],_ah=[0,40],_ai=function(_aj,_ak,_al){var _am=E(_al);switch(_am[0]){case 0:return E(_af);case 1:return new F(function(){return A(_aj,[_am[2],_f]);});break;case 2:return new F(function(){return _aa(_am[2]);});break;case 3:return new F(function(){return A(_ak,[_am[2],[1,new T(function(){return B(_ai(_aj,_ak,_am[3]));}),_f]]);});break;case 4:return new F(function(){return _1F(B(_aa(_am[2])),[1,_ah,new T(function(){return B(_1F(B(_ai(_aj,_ak,_am[3])),_ae));})]);});break;case 5:return new F(function(){return A(_ak,[_am[2],[1,new T(function(){return B(_ai(_aj,_ak,_am[3]));}),[1,new T(function(){return B(_ai(_aj,_ak,_am[4]));}),_f]]]);});break;default:return new F(function(){return _1F(B(_aa(_am[2])),[1,_ah,new T(function(){return B(_1F(B(_ai(_aj,_ak,_am[3])),[1,_ag,new T(function(){return B(_1F(B(_ai(_aj,_ak,_am[4])),_ae));})]));})]);});}},_an=[0],_ao=function(_ap,_aq,_ar,_as,_at,_au,_av,_aw){var _ax=E(_aw);switch(_ax[0]){case 0:return [0];case 1:return new F(function(){return A(_as,[_ax[2],_f]);});break;case 2:return new F(function(){return _aa(_ax[2]);});break;case 3:return new F(function(){return A(_ap,[_ax[2],[1,new T(function(){return B(_ai(_as,_at,_ax[3]));}),_f]]);});break;case 4:return new F(function(){return _1F(B(_aa(_ax[2])),[1,_ah,new T(function(){return B(_1F(B(_ai(_as,_at,_ax[3])),_ae));})]);});break;case 5:return new F(function(){return A(_ap,[_ax[2],[1,new T(function(){return B(_ai(_as,_at,_ax[3]));}),[1,new T(function(){return B(_ai(_as,_at,_ax[4]));}),_f]]]);});break;case 6:return new F(function(){return _1F(B(_aa(_ax[2])),[1,_ah,new T(function(){return B(_1F(B(_ai(_as,_at,_ax[3])),[1,_ag,new T(function(){return B(_1F(B(_ai(_as,_at,_ax[4])),_ae));})]));})]);});break;case 7:return new F(function(){return A(_aq,[_ax[2],[1,new T(function(){return B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,_ax[3]));}),_f]]);});break;case 8:return new F(function(){return _1F(B(_aa(_ax[2])),new T(function(){return B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,_ax[3]));},1));});break;case 9:return new F(function(){return A(_aq,[_ax[2],[1,new T(function(){return B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,_ax[3]));}),[1,new T(function(){return B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,_ax[4]));}),_f]]]);});break;case 10:return [1,_ah,new T(function(){return B(_1F(B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,_ax[3])),new T(function(){return B(_1F(B(_aa(_ax[2])),new T(function(){return B(_1F(B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,_ax[4])),_ae));},1)));},1)));})];case 11:var _ay=_ax[2],_az=_ax[3];return new F(function(){return A(_ar,[_ay,[1,new T(function(){return B(A(_au,[new T(function(){return B(A(_az,[_an]));}),_ay]));}),[1,new T(function(){return B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,B(A(_az,[_an]))));}),_f]]]);});break;default:var _aA=_ax[2],_aB=_ax[3];return new F(function(){return _1F(B(_aa(_aA)),new T(function(){return B(_1F(B(A(_av,[new T(function(){return B(A(_aB,[_an]));}),_aA])),[1,_ah,new T(function(){return B(_1F(B(_ao(_ap,_aq,_ar,_as,_at,_au,_av,B(A(_aB,[_an])))),_ae));})]));},1));});}},_aC=function(_aD){var _aE=E(_aD);if(!_aE[0]){return [0];}else{return new F(function(){return _1F(_aE[1],new T(function(){return B(_aC(_aE[2]));},1));});}},_aF=function(_aG,_aH){var _aI=E(_aH);return _aI[0]==0?[0]:[1,_aG,[1,_aI[1],new T(function(){return B(_aF(_aG,_aI[2]));})]];},_aJ=function(_aK,_aL,_aM,_aN,_aO,_aP,_aQ,_aR){var _aS=E(_aR);if(!_aS[0]){return new F(function(){return _aa(_aS[1]);});}else{var _aT=B(_7U(function(_aU){return new F(function(){return _ao(_aK,_aL,_aM,_aO,_aN,_aP,_aQ,_aU);});},_aS[1]));return _aT[0]==0?[0]:B(_aC([1,_aT[1],new T(function(){return B(_aF(_a9,_aT[2]));})]));}},_aV=new T(function(){return B(unCStr(" . "));}),_aW=function(_aX){return new F(function(){return _aJ(_6y,_6p,_6y,_6y,_6v,_62,_6N,_aX);});},_aY=new T(function(){return B(unCStr(" \u2234 "));}),_aZ=function(_b0,_b1){var _b2=new T(function(){return B(_1F(_aY,new T(function(){return B(_aJ(_6y,_6p,_6y,_6y,_6v,_62,_6N,_b1));},1)));},1),_b3=B(_7U(_aW,_b0));if(!_b3[0]){return E(_b2);}else{return new F(function(){return _1F(B(_aC([1,_b3[1],new T(function(){return B(_aF(_aV,_b3[2]));})])),_b2);});}},_b4=function(_b5,_b6,_b7){while(1){var _b8=E(_b6);if(!_b8[0]){return E(_b7)[0]==0?true:false;}else{var _b9=E(_b7);if(!_b9[0]){return false;}else{if(!B(A(_81,[_b5,_b8[1],_b9[1]]))){return false;}else{_b6=_b8[2];_b7=_b9[2];continue;}}}}},_ba=function(_bb,_bc,_bd){var _be=E(_bc),_bf=E(_bd);return !B(_b4(_bb,_be[1],_bf[1]))?true:!B(A(_81,[_bb,_be[2],_bf[2]]))?true:false;},_bg=function(_bh,_bi,_bj,_bk,_bl){return !B(_b4(_bh,_bi,_bk))?false:B(A(_81,[_bh,_bj,_bl]));},_bm=function(_bn,_bo,_bp){var _bq=E(_bo),_br=E(_bp);return new F(function(){return _bg(_bn,_bq[1],_bq[2],_br[1],_br[2]);});},_bs=function(_bt){return [0,function(_bu,_bv){return new F(function(){return _bm(_bt,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _ba(_bt,_bu,_bv);});}];},_bw=function(_bx,_by){while(1){var _bz=E(_bx);if(!_bz[0]){return E(_by)[0]==0?true:false;}else{var _bA=E(_by);if(!_bA[0]){return false;}else{if(E(_bz[1])[1]!=E(_bA[1])[1]){return false;}else{_bx=_bz[2];_by=_bA[2];continue;}}}}},_bB=function(_bC,_bD,_bE,_bF,_bG,_bH,_bI,_bJ,_bK){return new F(function(){return _bw(B(_aJ(_bC,_bD,_bE,_bF,_bG,_bH,_bI,_bJ)),B(_aJ(_bC,_bD,_bE,_bF,_bG,_bH,_bI,_bK)));});},_bL=function(_bM,_bN,_bO,_bP,_bQ,_bR,_bS,_bT,_bU){return !B(_bB(_bM,_bN,_bO,_bP,_bQ,_bR,_bS,_bT,_bU))?true:false;},_bV=function(_bW,_bX,_bY,_bZ,_c0,_c1,_c2){return [0,function(_c3,_c4){return new F(function(){return _bB(_bW,_bX,_bY,_bZ,_c0,_c1,_c2,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _bL(_bW,_bX,_bY,_bZ,_c0,_c1,_c2,_c3,_c4);});}];},_c5=function(_c6,_c7,_c8){var _c9=E(_c7),_ca=E(_c8);return !B(_b4(_c6,_c9[1],_ca[1]))?true:!B(A(_81,[_c6,_c9[2],_ca[2]]))?true:false;},_cb=function(_cc,_cd,_ce){var _cf=E(_cd),_cg=E(_ce);return new F(function(){return _bg(_cc,_cf[1],_cf[2],_cg[1],_cg[2]);});},_ch=function(_ci){return [0,function(_bu,_bv){return new F(function(){return _cb(_ci,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _c5(_ci,_bu,_bv);});}];},_cj=function(_ck,_cl,_cm){var _cn=E(_ck);switch(_cn[0]){case 0:var _co=E(_cl);return _co[0]==0?!B(_bw(_cn[3],_co[3]))?[0]:[1,_cm]:[0];case 1:var _cp=E(_cl);return _cp[0]==1?!B(_bw(_cn[3],_cp[3]))?[0]:[1,_cm]:[0];case 2:var _cq=E(_cl);return _cq[0]==2?!B(_bw(_cn[3],_cq[3]))?[0]:[1,_cm]:[0];case 3:var _cr=E(_cl);return _cr[0]==3?!B(_bw(_cn[3],_cr[3]))?[0]:[1,_cm]:[0];case 4:var _cs=E(_cl);return _cs[0]==4?!B(_bw(_cn[3],_cs[3]))?[0]:[1,_cm]:[0];case 5:var _ct=E(_cl);return _ct[0]==5?!B(_bw(_cn[3],_ct[3]))?[0]:[1,_cm]:[0];case 6:var _cu=E(_cl);return _cu[0]==6?!B(_bw(_cn[3],_cu[3]))?[0]:[1,_cm]:[0];case 7:var _cv=E(_cl);return _cv[0]==7?!B(_bw(_cn[3],_cv[3]))?[0]:[1,_cm]:[0];case 8:var _cw=E(_cl);return _cw[0]==8?!B(_bw(_cn[3],_cw[3]))?[0]:[1,_cm]:[0];default:var _cx=E(_cl);return _cx[0]==9?!B(_bw(_cn[3],_cx[3]))?[0]:[1,_cm]:[0];}},_cy=new T(function(){return B(_2x("AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_cz=function(_cA,_cB){return [3,_,_cA,_cB];},_cC=function(_cD,_cE,_cF){while(1){var _cG=E(_cF);if(!_cG[0]){return [0];}else{var _cH=E(_cG[1]),_cI=B(A(_cD,[_cE,_cH[2],_cH[3]]));if(!_cI[0]){_cF=_cG[2];continue;}else{return E(_cI);}}}},_cJ=function(_cK,_cL){while(1){var _cM=(function(_cN,_cO){var _cP=E(_cO);switch(_cP[0]){case 2:var _cQ=B(_cC(_cj,_cP[2],_cN));if(!_cQ[0]){return E(_cP);}else{var _cR=_cN;_cL=_cQ[1];_cK=_cR;return null;}break;case 4:var _cS=_cP[3],_cT=B(_cC(_cj,_cP[2],_cN));if(!_cT[0]){return E(_cP);}else{var _cU=E(_cT[1]);switch(_cU[0]){case 3:return E(_cU[3])[0]==0?B(_cz(_cU[2],_cS)):E(_cP);case 4:if(!E(_cU[3])[0]){var _cR=_cN;_cL=[4,_,_cU[2],_cS];_cK=_cR;return null;}else{return E(_cP);}break;default:return E(_cP);}}break;case 6:var _cV=_cP[3],_cW=_cP[4],_cX=B(_cC(_cj,_cP[2],_cN));if(!_cX[0]){return E(_cP);}else{var _cY=E(_cX[1]);switch(_cY[0]){case 5:if(!E(_cY[3])[0]){if(!E(_cY[4])[0]){var _cR=_cN;_cL=[5,_,_cY[2],_cV,_cW];_cK=_cR;return null;}else{return E(_cP);}}else{return E(_cP);}break;case 6:if(!E(_cY[3])[0]){if(!E(_cY[4])[0]){var _cR=_cN;_cL=[6,_,_cY[2],_cV,_cW];_cK=_cR;return null;}else{return E(_cP);}}else{return E(_cP);}break;default:return E(_cP);}}break;case 7:return [7,_,_cP[2],new T(function(){return B(_cJ(_cN,_cP[3]));})];case 8:var _cZ=_cP[2],_d0=_cP[3],_d1=B(_cC(_cj,_cZ,_cN));if(!_d1[0]){return [8,_,_cZ,new T(function(){return B(_cJ(_cN,_d0));})];}else{var _d2=E(_d1[1]);switch(_d2[0]){case 7:return E(_d2[3])[0]==0?[7,_,_d2[2],new T(function(){return B(_cJ(_cN,_d0));})]:[8,_,_cZ,new T(function(){return B(_cJ(_cN,_d0));})];case 8:if(!E(_d2[3])[0]){var _cR=_cN;_cL=[8,_,_d2[2],_d0];_cK=_cR;return null;}else{return [8,_,_cZ,new T(function(){return B(_cJ(_cN,_d0));})];}break;default:return [8,_,_cZ,new T(function(){return B(_cJ(_cN,_d0));})];}}break;case 9:return [9,_,_cP[2],new T(function(){return B(_cJ(_cN,_cP[3]));}),new T(function(){return B(_cJ(_cN,_cP[4]));})];case 10:var _d3=_cP[2],_d4=_cP[3],_d5=_cP[4],_d6=B(_cC(_cj,_d3,_cN));if(!_d6[0]){return [10,_,_d3,new T(function(){return B(_cJ(_cN,_d4));}),new T(function(){return B(_cJ(_cN,_d5));})];}else{var _d7=E(_d6[1]);switch(_d7[0]){case 9:return E(_d7[3])[0]==0?E(_d7[4])[0]==0?[9,_,_d7[2],new T(function(){return B(_cJ(_cN,B(_cJ(_cN,_d4))));}),new T(function(){return B(_cJ(_cN,B(_cJ(_cN,_d5))));})]:[10,_,_d3,new T(function(){return B(_cJ(_cN,_d4));}),new T(function(){return B(_cJ(_cN,_d5));})]:[10,_,_d3,new T(function(){return B(_cJ(_cN,_d4));}),new T(function(){return B(_cJ(_cN,_d5));})];case 10:if(!E(_d7[3])[0]){if(!E(_d7[4])[0]){var _cR=_cN;_cL=[10,_,_d7[2],_d4,_d5];_cK=_cR;return null;}else{return [10,_,_d3,new T(function(){return B(_cJ(_cN,_d4));}),new T(function(){return B(_cJ(_cN,_d5));})];}}else{return [10,_,_d3,new T(function(){return B(_cJ(_cN,_d4));}),new T(function(){return B(_cJ(_cN,_d5));})];}break;default:return [10,_,_d3,new T(function(){return B(_cJ(_cN,_d4));}),new T(function(){return B(_cJ(_cN,_d5));})];}}break;case 11:return [11,_,_cP[2],function(_d8){return new F(function(){return _cJ(_cN,B(A(_cP[3],[_d8])));});}];case 12:var _d9=_cP[2],_da=_cP[3],_db=B(_cC(_cj,_d9,_cN));if(!_db[0]){return [12,_,_d9,function(_dc){return new F(function(){return _cJ(_cN,B(A(_da,[_dc])));});}];}else{var _dd=E(_db[1]);switch(_dd[0]){case 11:return [11,_,_dd[2],function(_de){return new F(function(){return _cJ(_cN,B(A(_da,[_de])));});}];case 12:var _cR=_cN;_cL=[12,_,_dd[2],_da];_cK=_cR;return null;default:return [12,_,_d9,function(_df){return new F(function(){return _cJ(_cN,B(A(_da,[_df])));});}];}}break;default:return E(_cP);}})(_cK,_cL);if(_cM!=null){return _cM;}}},_dg=function(_dh,_di){var _dj=E(_di);if(!_dj[0]){var _dk=B(_cC(_cj,_dj[1],_dh));if(!_dk[0]){return E(_dj);}else{var _dl=E(_dk[1]);return _dl[0]==0?E(_cy):[1,new T(function(){return B(_7U(function(_dm){return new F(function(){return _cJ(_dh,_dm);});},_dl[1]));})];}}else{return [1,new T(function(){return B(_7U(function(_dn){return new F(function(){return _cJ(_dh,_dn);});},_dj[1]));})];}},_do=function(_dp,_dq,_dr,_ds,_dt,_du,_dv,_dw,_dx){var _dy=E(_dx);return [0,new T(function(){return B(_7U(function(_dz){return new F(function(){return _dg(_dw,_dz);});},_dy[1]));}),new T(function(){return B(_dg(_dw,_dy[2]));})];},_dA=function(_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dI,_dJ){var _dK=E(_dJ);return [0,new T(function(){return B(_7U(function(_dL){return new F(function(){return _do(_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dI,_dL);});},_dK[1]));}),new T(function(){return B(_do(_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dI,_dK[2]));})];},_dM=function(_dN){return E(E(_dN)[1]);},_dO=function(_dP,_dQ){var _dR=E(_dQ);return new F(function(){return A(_dM,[_dR[1],E(_dP)[2],_dR[2]]);});},_dS=function(_dT,_dU,_dV){var _dW=E(_dV);if(!_dW[0]){return [0];}else{var _dX=_dW[1],_dY=_dW[2];return !B(A(_dT,[_dU,_dX]))?[1,_dX,new T(function(){return B(_dS(_dT,_dU,_dY));})]:E(_dY);}},_dZ=function(_e0,_e1,_e2){while(1){var _e3=E(_e2);if(!_e3[0]){return false;}else{if(!B(A(_e0,[_e1,_e3[1]]))){_e2=_e3[2];continue;}else{return true;}}}},_e4=function(_e5,_e6){var _e7=function(_e8,_e9){while(1){var _ea=(function(_eb,_ec){var _ed=E(_eb);if(!_ed[0]){return [0];}else{var _ee=_ed[1],_ef=_ed[2];if(!B(_dZ(_e5,_ee,_ec))){return [1,_ee,new T(function(){return B(_e7(_ef,[1,_ee,_ec]));})];}else{_e8=_ef;var _eg=_ec;_e9=_eg;return null;}}})(_e8,_e9);if(_ea!=null){return _ea;}}};return new F(function(){return _e7(_e6,_f);});},_eh=function(_ei,_ej,_ek){return new F(function(){return _1F(_ej,new T(function(){return B((function(_el,_em){while(1){var _en=E(_em);if(!_en[0]){return E(_el);}else{var _eo=B(_dS(_ei,_en[1],_el));_em=_en[2];_el=_eo;continue;}}})(B(_e4(_ei,_ek)),_ej));},1));});},_ep=function(_eq,_er){while(1){var _es=(function(_et,_eu){var _ev=E(_eu);switch(_ev[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_et,_ev[2]],_f];case 3:var _ew=_et;_er=_ev[3];_eq=_ew;return null;case 4:return new F(function(){return _eh(_dO,[1,[0,_et,_ev[2]],_f],new T(function(){return B(_ep(_et,_ev[3]));},1));});break;case 5:return new F(function(){return _eh(_dO,B(_ep(_et,_ev[3])),new T(function(){return B(_ep(_et,_ev[4]));},1));});break;default:return new F(function(){return _eh(_dO,B(_eh(_dO,[1,[0,_et,_ev[2]],_f],new T(function(){return B(_ep(_et,_ev[3]));},1))),new T(function(){return B(_ep(_et,_ev[4]));},1));});}})(_eq,_er);if(_es!=null){return _es;}}},_ex=function(_ey,_ez,_eA,_eB){while(1){var _eC=(function(_eD,_eE,_eF,_eG){var _eH=E(_eG);switch(_eH[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_eD,_eH[2]],_f];case 3:return new F(function(){return _ep(_eD,_eH[3]);});break;case 4:return new F(function(){return _eh(_dO,[1,[0,_eD,_eH[2]],_f],new T(function(){return B(_ep(_eD,_eH[3]));},1));});break;case 5:return new F(function(){return _eh(_dO,B(_ep(_eD,_eH[3])),new T(function(){return B(_ep(_eD,_eH[4]));},1));});break;case 6:return new F(function(){return _eh(_dO,B(_eh(_dO,[1,[0,_eD,_eH[2]],_f],new T(function(){return B(_ep(_eD,_eH[3]));},1))),new T(function(){return B(_ep(_eD,_eH[4]));},1));});break;case 7:var _eI=_eD,_eJ=_eE,_eK=_eF;_eB=_eH[3];_ey=_eI;_ez=_eJ;_eA=_eK;return null;case 8:return new F(function(){return _eh(_dO,[1,[0,_eD,_eH[2]],_f],new T(function(){return B(_ex(_eD,_eE,_eF,_eH[3]));},1));});break;case 9:return new F(function(){return _eh(_dO,B(_ex(_eD,_eE,_eF,_eH[3])),new T(function(){return B(_ex(_eD,_eE,_eF,_eH[4]));},1));});break;case 10:return new F(function(){return _eh(_dO,B(_eh(_dO,[1,[0,_eD,_eH[2]],_f],new T(function(){return B(_ex(_eD,_eE,_eF,_eH[3]));},1))),new T(function(){return B(_ex(_eD,_eE,_eF,_eH[4]));},1));});break;case 11:var _eI=_eD,_eJ=_eE,_eK=_eF;_eB=B(A(_eH[3],[_an]));_ey=_eI;_ez=_eJ;_eA=_eK;return null;default:return new F(function(){return _eh(_dO,[1,[0,_eD,_eH[2]],_f],new T(function(){return B(_ex(_eD,_eE,_eF,B(A(_eH[3],[_an]))));},1));});}})(_ey,_ez,_eA,_eB);if(_eC!=null){return _eC;}}},_eL=function(_eM,_eN,_eO,_eP,_eQ){var _eR=function(_eS){return new F(function(){return _ex(_eM,_eN,_eO,_eS);});};return new F(function(){return _1F(B(_7o(B(_7U(function(_eT){var _eU=E(_eT);if(!_eU[0]){return [1,[0,_eM,_eU[1]],_f];}else{return new F(function(){return _7o(B(_7U(_eR,_eU[1])));});}},_eP)))),new T(function(){var _eV=E(_eQ);if(!_eV[0]){var _eW=[1,[0,_eM,_eV[1]],_f];}else{var _eW=B(_7o(B(_7U(_eR,_eV[1]))));}return _eW;},1));});},_eX=function(_eY,_eZ,_f0,_f1,_f2,_f3,_f4,_f5,_f6){var _f7=E(_f6);return new F(function(){return _1F(B(_7o(B(_7U(function(_f8){var _f9=E(_f8);return new F(function(){return _eL(_eY,_f2,_f3,_f9[1],_f9[2]);});},_f7[1])))),new T(function(){var _fa=E(_f7[2]);return B(_eL(_eY,_f2,_f3,_fa[1],_fa[2]));},1));});},_fb=function(_fc,_fd,_fe,_ff,_fg,_fh,_fi,_fj,_fk,_fl,_fm){return [0,_fc,_fd,_fe,_ff,function(_dL){return new F(function(){return _eX(_fc,_fg,_fh,_fi,_fj,_fk,_fl,_fm,_dL);});},function(_fn,_dL){return new F(function(){return _dA(_fg,_fh,_fi,_fj,_fk,_fl,_fm,_fn,_dL);});}];},_fo=function(_fp){return E(E(_fp)[2]);},_fq=function(_fr){return E(E(_fr)[1]);},_fs=[0,_fq,_fo],_ft=[0,125],_fu=new T(function(){return B(unCStr("given = "));}),_fv=new T(function(){return B(unCStr(", "));}),_fw=new T(function(){return B(unCStr("needed = "));}),_fx=new T(function(){return B(unCStr("AbsRule {"));}),_fy=[0,0],_fz=function(_fA){return E(E(_fA)[3]);},_fB=function(_fC){return E(E(_fC)[1]);},_fD=function(_fE,_fF,_fG,_fH){var _fI=function(_fJ){return new F(function(){return _1F(_fx,new T(function(){return B(_1F(_fw,new T(function(){return B(A(new T(function(){return B(A(_fz,[_fE,_fG]));}),[new T(function(){return B(_1F(_fv,new T(function(){return B(_1F(_fu,new T(function(){return B(A(new T(function(){return B(A(_fB,[_fE,_fy,_fH]));}),[[1,_ft,_fJ]]));},1)));},1)));})]));},1)));},1));});};return _fF<11?E(_fI):function(_fK){return [1,_4e,new T(function(){return B(_fI([1,_4d,_fK]));})];};},_fL=function(_fM,_fN){var _fO=E(_fN);return new F(function(){return A(_fD,[_fM,0,_fO[1],_fO[2],_f]);});},_fP=function(_fQ,_fR,_fS){return new F(function(){return _1P(function(_fT){var _fU=E(_fT);return new F(function(){return _fD(_fQ,0,_fU[1],_fU[2]);});},_fR,_fS);});},_fV=function(_fW,_fX,_fY){var _fZ=E(_fY);return new F(function(){return _fD(_fW,E(_fX)[1],_fZ[1],_fZ[2]);});},_g0=function(_g1){return [0,function(_bu,_bv){return new F(function(){return _fV(_g1,_bu,_bv);});},function(_bv){return new F(function(){return _fL(_g1,_bv);});},function(_bu,_bv){return new F(function(){return _fP(_g1,_bu,_bv);});}];},_g2=function(_g3,_g4,_g5,_g6,_g7,_g8,_g9,_ga,_gb){return new F(function(){return _1P(function(_gc,_gd){return new F(function(){return _1F(B(_aJ(_g3,_g4,_g5,_g6,_g7,_g8,_g9,_gc)),_gd);});},_ga,_gb);});},_ge=function(_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_gn,_go){return new F(function(){return _1F(B(_aJ(_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gn)),_go);});},_gp=function(_gq,_gr,_gs,_gt,_gu,_gv,_gw){return [0,function(_gx,_c3,_c4){return new F(function(){return _ge(_gq,_gr,_gs,_gt,_gu,_gv,_gw,_gx,_c3,_c4);});},function(_c4){return new F(function(){return _aJ(_gq,_gr,_gs,_gt,_gu,_gv,_gw,_c4);});},function(_c3,_c4){return new F(function(){return _g2(_gq,_gr,_gs,_gt,_gu,_gv,_gw,_c3,_c4);});}];},_gy=new T(function(){return B(unCStr("Sequent "));}),_gz=[0,11],_gA=[0,32],_gB=function(_gC,_gD,_gE,_gF){var _gG=new T(function(){return B(A(_fB,[_gC,_gz,_gF]));}),_gH=new T(function(){return B(A(_fz,[_gC,_gE]));});return _gD<11?function(_gI){return new F(function(){return _1F(_gy,new T(function(){return B(A(_gH,[[1,_gA,new T(function(){return B(A(_gG,[_gI]));})]]));},1));});}:function(_gJ){return [1,_4e,new T(function(){return B(_1F(_gy,new T(function(){return B(A(_gH,[[1,_gA,new T(function(){return B(A(_gG,[[1,_4d,_gJ]]));})]]));},1)));})];};},_gK=function(_gL,_gM){var _gN=E(_gM);return new F(function(){return A(_gB,[_gL,0,_gN[1],_gN[2],_f]);});},_gO=function(_gP,_gQ,_gR){return new F(function(){return _1P(function(_gS){var _gT=E(_gS);return new F(function(){return _gB(_gP,0,_gT[1],_gT[2]);});},_gQ,_gR);});},_gU=function(_gV,_gW,_gX){var _gY=E(_gX);return new F(function(){return _gB(_gV,E(_gW)[1],_gY[1],_gY[2]);});},_gZ=function(_h0){return [0,function(_bu,_bv){return new F(function(){return _gU(_h0,_bu,_bv);});},function(_bv){return new F(function(){return _gK(_h0,_bv);});},function(_bu,_bv){return new F(function(){return _gO(_h0,_bu,_bv);});}];},_h1=function(_h2,_h3){return new F(function(){return _1F(B(_aa(_h2)),_h3);});},_h4=function(_h5,_h6){return new F(function(){return _1P(_h1,_h5,_h6);});},_h7=function(_h8,_h9,_ha){return new F(function(){return _1F(B(_aa(_h9)),_ha);});},_hb=[0,_h7,_aa,_h4],_hc=function(_hd,_he,_hf,_hg,_hh,_hi,_hj,_hk,_hl,_hm,_hn,_ho){var _hp=E(_ho);return new F(function(){return _eL(_hd,_hk,_hl,_hp[1],_hp[2]);});},_hq=function(_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_hB){return [0,_hr,_hs,_ht,_hu,function(_dL){return new F(function(){return _hc(_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_hB,_dL);});},function(_fn,_dL){return new F(function(){return _do(_hv,_hw,_hx,_hy,_hz,_hA,_hB,_fn,_dL);});}];},_hC=function(_hD,_hE){return [0];},_hF=function(_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP,_hQ,_hR,_hS,_hT){return [0,_hG,_hH,_hC,_61];},_hU=function(_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4,_i5,_i6){var _i7=E(_i6);if(!_i7[0]){return [1,[0,_hV,_i7[1]],_f];}else{return new F(function(){return _7o(B(_7U(function(_i8){return new F(function(){return _ex(_hV,_i2,_i3,_i8);});},_i7[1])));});}},_i9=function(_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_ii,_ij,_ik){return [0,_ia,_ib,_ic,_id,function(_dL){return new F(function(){return _hU(_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_ii,_ij,_ik,_dL);});},_dg];},_il=function(_im){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_im));}))));});},_in=new T(function(){return B(_il("w_srWu{v} [lid] main:AbstractSyntaxMultiUnification.S_NextVar{tc rHY}\n                  sv{tv arAx} [tv] quant{tv arAv} [tv]"));}),_io=new T(function(){return B(_il("w_srWt{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv arAv} [tv]"));}),_ip=new T(function(){return B(_il("w_srWs{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv arAu} [tv]"));}),_iq=new T(function(){return B(_il("w_srWr{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv arAx} [tv]"));}),_ir=new T(function(){return B(_il("w_srWq{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv arAt} [tv]"));}),_is=new T(function(){return B(_il("w_srWp{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv arAw} [tv]"));}),_it=new T(function(){return B(_il("w_srWv{v} [lid] main:AbstractSyntaxMultiUnification.SchemeVar{tc rH8}\n                  sv{tv arAx} [tv]"));}),_iu=new T(function(){return B(_il("w_srWo{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv arAv} [tv]"));}),_iv=new T(function(){return B(_il("w_srWn{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv arAu} [tv]"));}),_iw=new T(function(){return B(_il("w_srWm{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv arAx} [tv]"));}),_ix=new T(function(){return B(_il("w_srWl{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv arAt} [tv]"));}),_iy=new T(function(){return B(_il("w_srWk{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv arAw} [tv]"));}),_iz=function(_iA,_iB){return function(_iC,_iD){var _iE=E(_iC);return _iE[0]==0?[1,[0,new T(function(){return B(_iF(_iA,_iB,_iy,_ix,_iw,_iv,_iu,_is,_ir,_iq,_ip,_io,_in,_it));}),_iE[1],_iD]]:[0];};},_iG=function(_iH){return [0,E(_iH)];},_iF=function(_iI,_iJ,_iK,_iL,_iM,_iN,_iO,_iP,_iQ,_iR,_iS,_iT,_iU,_iV){return [0,_iI,_iJ,new T(function(){return B(_iz(_iI,_iJ));}),_iG];},_iW=[1,_f],_iX=function(_iY,_iZ){while(1){var _j0=E(_iY);if(!_j0[0]){return E(_iZ);}else{_iY=_j0[2];var _j1=_iZ+1|0;_iZ=_j1;continue;}}},_j2=[0,95],_j3=[1,_j2,_f],_j4=[1,_j3,_f],_j5=function(_j6,_j7,_j8){return !B(_bw(B(A(_j6,[_j7,_j4])),B(A(_j6,[_j8,_j4]))))?true:false;},_j9=function(_ja){return [0,function(_jb,_jc){return new F(function(){return _bw(B(A(_ja,[_jb,_j4])),B(A(_ja,[_jc,_j4])));});},function(_c3,_c4){return new F(function(){return _j5(_ja,_c3,_c4);});}];},_jd=function(_je,_jf){return new F(function(){return _cJ(_je,_jf);});},_jg=function(_jh,_ji,_jj,_jk,_jl,_jm,_jn,_jo,_jp,_jq,_jr){return [0,_jh,_ji,_jj,_jk,function(_js){return new F(function(){return _ex(_jh,_jo,_jp,_js);});},_jd];},_jt=new T(function(){return B(_il("w_snPU{v} [lid] main:AbstractSyntaxMultiUnification.S_NextVar{tc rHY}\n                  sv{tv akOl} [tv] quant{tv akOj} [tv]"));}),_ju=new T(function(){return B(_il("w_snPT{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv akOj} [tv]"));}),_jv=new T(function(){return B(_il("w_snPS{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv akOi} [tv]"));}),_jw=new T(function(){return B(_il("w_snPR{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv akOl} [tv]"));}),_jx=new T(function(){return B(_il("w_snPQ{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv akOh} [tv]"));}),_jy=new T(function(){return B(_il("w_snPP{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv akOk} [tv]"));}),_jz=new T(function(){return B(_il("w_snPV{v} [lid] main:AbstractSyntaxMultiUnification.SchemeVar{tc rH8}\n                  sv{tv akOl} [tv]"));}),_jA=new T(function(){return B(_il("w_snPO{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv akOj} [tv]"));}),_jB=new T(function(){return B(_il("w_snPN{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv akOi} [tv]"));}),_jC=new T(function(){return B(_il("w_snPM{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv akOl} [tv]"));}),_jD=new T(function(){return B(_il("w_snPL{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv akOh} [tv]"));}),_jE=new T(function(){return B(_il("w_snPK{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv akOk} [tv]"));}),_jF=function(_jG,_jH,_jI,_jJ){var _jK=E(_jI);switch(_jK[0]){case 2:return [1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jK[2],_jJ]];case 4:var _jM=_jK[2];if(!E(_jK[3])[0]){var _jN=E(_jJ);switch(_jN[0]){case 3:return E(_jN[3])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jM,_jN]]:[0];case 4:return E(_jN[3])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jM,_jN]]:[0];default:return [0];}}else{return [0];}break;case 6:var _jO=_jK[2];if(!E(_jK[3])[0]){if(!E(_jK[4])[0]){var _jP=E(_jJ);switch(_jP[0]){case 5:return E(_jP[3])[0]==0?E(_jP[4])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jO,_jP]]:[0]:[0];case 6:return E(_jP[3])[0]==0?E(_jP[4])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jO,_jP]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _jQ=_jK[2];if(!E(_jK[3])[0]){var _jR=E(_jJ);switch(_jR[0]){case 7:return E(_jR[3])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jQ,_jR]]:[0];case 8:return E(_jR[3])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jQ,_jR]]:[0];default:return [0];}}else{return [0];}break;case 10:var _jS=_jK[2];if(!E(_jK[3])[0]){if(!E(_jK[4])[0]){var _jT=E(_jJ);switch(_jT[0]){case 9:return E(_jT[3])[0]==0?E(_jT[4])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jS,_jT]]:[0]:[0];case 10:return E(_jT[3])[0]==0?E(_jT[4])[0]==0?[1,[0,new T(function(){return B(_jL(_jG,_jH,_jE,_jD,_jC,_jB,_jA,_jy,_jx,_jw,_jv,_ju,_jt,_jz));}),_jS,_jT]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_jU=new T(function(){return B(_2x("AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_jV=function(_jW){var _jX=E(_jW);switch(_jX[0]){case 3:return [2,_,_jX];case 4:return [4,_,_jX,_6D];case 5:return [6,_,_jX,_6D,_6D];case 6:return [8,_,_jX,_6A];case 7:return [10,_,_jX,_6A,_6A];default:return E(_jU);}},_jL=function(_jY,_jZ,_k0,_k1,_k2,_k3,_k4,_k5,_k6,_k7,_k8,_k9,_ka,_kb){return [0,_jY,_jZ,function(_kc,_kd){return new F(function(){return _jF(_jY,_jZ,_kc,_kd);});},_jV];},_ke=function(_kf,_kg,_kh){return new F(function(){return _1P(function(_ki,_kj){return new F(function(){return _1F(B(A(_kf,[_ki,_j4])),_kj);});},_kg,_kh);});},_kk=function(_kl){return [0,function(_km,_kn,_ko){return new F(function(){return _1F(B(A(_kl,[_kn,_j4])),_ko);});},function(_kp){return new F(function(){return A(_kl,[_kp,_j4]);});},function(_c3,_c4){return new F(function(){return _ke(_kl,_c3,_c4);});}];},_kq=[1,_f],_kr=function(_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_kC,_kD){var _kE=E(_kC);if(_kE[0]==2){return E(_kq);}else{var _kF=E(_kD);if(_kF[0]==2){return E(_kq);}else{var _kG=function(_kH){var _kI=function(_kJ){var _kK=function(_kL){var _kM=function(_kN){var _kO=function(_kP){var _kQ=function(_kR){var _kS=function(_kT){var _kU=function(_kV){var _kW=function(_kX){var _kY=function(_kZ){var _l0=function(_l1){var _l2=function(_l3){var _l4=E(_kE);switch(_l4[0]){case 1:var _l5=E(_kF);return _l5[0]==1?!B(A(_kt,[_l4[2],_l5[2]]))?[0]:E(_kq):[0];case 3:var _l6=E(_kF);return _l6[0]==3?!B(A(_ks,[_l4[2],_l6[2]]))?[0]:E(_kq):[0];case 4:var _l7=_l4[2],_l8=E(_kF);switch(_l8[0]){case 3:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[4,_,_l7,_6D],[3,_,_l8[2],_6D]]));}),_f]];case 4:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[4,_,_l7,_6D],[4,_,_l8[2],_6D]]));}),_f]];default:return [0];}break;case 5:var _la=E(_kF);return _la[0]==5?!B(A(_ks,[_l4[2],_la[2]]))?[0]:E(_kq):[0];case 6:var _lb=_l4[2],_lc=E(_kF);switch(_lc[0]){case 5:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[6,_,_lb,_6D,_6D],[5,_,_lc[2],_6D,_6D]]));}),_f]];case 6:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[6,_,_lb,_6D,_6D],[6,_,_lc[2],_6D,_6D]]));}),_f]];default:return [0];}break;case 7:var _ld=E(_kF);return _ld[0]==7?!B(A(_ku,[_l4[2],_ld[2]]))?[0]:[1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_l4[3],_ld[3]]));}),_f]]:[0];case 8:var _le=_l4[2],_lf=_l4[3],_lg=E(_kF);switch(_lg[0]){case 7:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[8,_,_le,_6A],[7,_,_lg[2],_6A]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_lf,_lg[3]]));}),_f]]];case 8:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[8,_,_le,_6A],[8,_,_lg[2],_6A]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_lf,_lg[3]]));}),_f]]];default:return [0];}break;case 9:var _lh=E(_kF);return _lh[0]==9?!B(A(_ku,[_l4[2],_lh[2]]))?[0]:[1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_l4[3],_lh[3]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_l4[4],_lh[4]]));}),_f]]]:[0];case 10:var _li=_l4[2],_lj=_l4[3],_lk=_l4[4],_ll=function(_lm){var _ln=E(_kF);switch(_ln[0]){case 9:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[10,_,_li,_6A,_6A],[9,_,_ln[2],_6A,_6A]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_lj,_ln[3]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_lk,_ln[4]]));}),_f]]]];case 10:return [1,[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,[10,_,_li,_6A,_6A],[10,_,_ln[2],_6A,_6A]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_lj,_ln[3]]));}),[1,new T(function(){return B(A(_l9,[_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_lk,_ln[4]]));}),_f]]]];default:return [0];}};return E(_lj)[0]==0?E(_lk)[0]==0?E(_kq):B(_ll(_)):B(_ll(_));default:return [0];}},_lo=E(_kF);return _lo[0]==10?E(_lo[3])[0]==0?E(_lo[4])[0]==0?E(_kq):B(_l2(_)):B(_l2(_)):B(_l2(_));},_lp=E(_kE);return _lp[0]==8?E(_lp[3])[0]==0?E(_kq):B(_l0(_)):B(_l0(_));},_lq=E(_kF);switch(_lq[0]){case 6:return E(_lq[3])[0]==0?E(_lq[4])[0]==0?E(_kq):B(_kY(_)):B(_kY(_));case 8:return E(_lq[3])[0]==0?E(_kq):B(_kY(_));default:return new F(function(){return _kY(_);});}},_lr=E(_kE);return _lr[0]==6?E(_lr[3])[0]==0?E(_lr[4])[0]==0?E(_kq):B(_kW(_)):B(_kW(_)):B(_kW(_));},_ls=E(_kF);return _ls[0]==4?E(_ls[3])[0]==0?E(_kq):B(_kU(_)):B(_kU(_));},_lt=E(_kE);switch(_lt[0]){case 4:return E(_lt[3])[0]==0?E(_kq):B(_kS(_));case 9:return E(_lt[3])[0]==0?E(_lt[4])[0]==0?E(_kq):B(_kS(_)):B(_kS(_));default:return new F(function(){return _kS(_);});}},_lu=E(_kF);return _lu[0]==9?E(_lu[3])[0]==0?E(_lu[4])[0]==0?E(_kq):B(_kQ(_)):B(_kQ(_)):B(_kQ(_));},_lv=E(_kE);return _lv[0]==7?E(_lv[3])[0]==0?E(_kq):B(_kO(_)):B(_kO(_));},_lw=E(_kF);switch(_lw[0]){case 5:return E(_lw[3])[0]==0?E(_lw[4])[0]==0?E(_kq):B(_kM(_)):B(_kM(_));case 7:return E(_lw[3])[0]==0?E(_kq):B(_kM(_));default:return new F(function(){return _kM(_);});}},_lx=E(_kE);return _lx[0]==5?E(_lx[3])[0]==0?E(_lx[4])[0]==0?E(_kq):B(_kK(_)):B(_kK(_)):B(_kK(_));},_ly=E(_kF);return _ly[0]==3?E(_ly[3])[0]==0?E(_kq):B(_kI(_)):B(_kI(_));},_lz=E(_kE);return _lz[0]==3?E(_lz[3])[0]==0?E(_kq):B(_kG(_)):B(_kG(_));}}},_lA=function(_lB,_lC,_lD){return [0,_lB,_lC,_lD];},_lE=new T(function(){return B(_il("w_snQ3{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv akNG} [tv]"));}),_lF=new T(function(){return B(_il("w_snPZ{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv akNH} [tv]"));}),_lG=function(_lH){return [0,function(_lI,_lJ){return B(A(_lH,[_lI,_lJ,_61]))[0]==0?false:true;},function(_lK,_lL){return B(A(_lH,[_lK,_lL,_61]))[0]==0?true:false;}];},_lM=new T(function(){return B(_lG(_cj));}),_l9=function(_lN,_lO,_lP,_lQ,_lR,_lS,_lT,_lU,_lV,_lW){var _lX=function(_lY,_lZ){return new F(function(){return _ao(_lR,_lT,_lU,_lS,_lQ,_lV,_lW,_lY);});};return function(_m0,_m1){return new F(function(){return _lA(new T(function(){return B(_jL(function(_m2,_m3){return new F(function(){return _kr(_lN,_lO,_lP,_lQ,_lR,_lS,_lT,_lU,_lV,_lW,_m2,_m3);});},new T(function(){return B(_jg(_lM,_hb,new T(function(){return B(_j9(_lX));}),new T(function(){return B(_kk(_lX));}),_lR,_lT,_lU,_lQ,_lS,_lV,_lW));}),_lF,_lN,_lO,_lP,_lE,_lQ,_lR,_lS,_lT,_lU,_lV,_lW));}),_m0,_m1);});};},_m4=function(_m5,_m6,_m7){var _m8=E(_m6);if(!_m8[0]){return [0];}else{var _m9=E(_m7);return _m9[0]==0?[0]:[1,new T(function(){return B(A(_m5,[_m8[1],_m9[1]]));}),new T(function(){return B(_m4(_m5,_m8[2],_m9[2]));})];}},_ma=function(_mb,_mc,_md,_me,_mf,_mg,_mh,_mi,_mj,_mk,_ml,_mm){var _mn=E(_ml);if(!_mn[0]){return E(_iW);}else{var _mo=_mn[1],_mp=E(_mm);if(!_mp[0]){return E(_iW);}else{var _mq=_mp[1];return B(_iX(_mo,0))!=B(_iX(_mq,0))?[0]:[1,new T(function(){return B(_m4(new T(function(){return B(_l9(_mb,_mc,_md,_me,_mf,_mg,_mh,_mi,_mj,_mk));}),_mo,_mq));})];}}},_mr=new T(function(){return B(_il("w_srXf{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv arAd} [tv]"));}),_ms=new T(function(){return B(_il("w_srXj{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv arAc} [tv]"));}),_mt=new T(function(){return B(_lG(_cj));}),_mu=function(_mv,_mw,_mx,_my,_mz,_mA,_mB,_mC,_mD,_mE){var _mF=new T(function(){return B(_iF(function(_mG,_mH){return new F(function(){return _ma(_mv,_mw,_mx,_my,_mz,_mA,_mB,_mC,_mD,_mE,_mG,_mH);});},new T(function(){return B(_i9(_mt,_hb,new T(function(){return B(_bV(_mz,_mB,_mC,_my,_mA,_mD,_mE));}),new T(function(){return B(_gp(_mz,_mB,_mC,_my,_mA,_mD,_mE));}),_mz,_mB,_mC,_my,_mA,_mD,_mE));}),_mr,_mv,_mw,_mx,_ms,_my,_mz,_mA,_mB,_mC,_mD,_mE));});return function(_mI,_mJ){var _mK=E(_mI),_mL=_mK[1],_mM=E(_mJ),_mN=_mM[1];return B(_iX(_mL,0))!=B(_iX(_mN,0))?[0]:[1,[1,[0,_mF,_mK[2],_mM[2]],new T(function(){return B(_m4(function(_fn,_dL){return [0,_mF,_fn,_dL];},_mL,_mN));})]];};},_mO=new T(function(){return B(_il("w_srZR{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv arzK} [tv]"));}),_mP=new T(function(){return B(_il("w_srZV{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv arzJ} [tv]"));}),_mQ=function(_mR,_mS,_mT,_mU,_mV,_mW,_mX,_mY,_mZ,_n0){var _n1=new T(function(){return B(_hF(new T(function(){return B(_mu(_mR,_mS,_mT,_mU,_mV,_mW,_mX,_mY,_mZ,_n0));}),new T(function(){return B(_hq(_mt,_hb,new T(function(){return B(_ch(new T(function(){return B(_bV(_mV,_mX,_mY,_mU,_mW,_mZ,_n0));})));}),new T(function(){return B(_gZ(new T(function(){return B(_gp(_mV,_mX,_mY,_mU,_mW,_mZ,_n0));})));}),_mV,_mX,_mY,_mU,_mW,_mZ,_n0));}),_mO,_mR,_mS,_mT,_mP,_mU,_mV,_mW,_mX,_mY,_mZ,_n0));});return function(_n2,_n3){var _n4=E(_n2),_n5=_n4[1],_n6=E(_n3),_n7=_n6[1];return B(_iX(_n5,0))!=B(_iX(_n7,0))?[0]:[1,[1,[0,_n1,_n4[2],_n6[2]],new T(function(){return B(_m4(function(_fn,_dL){return [0,_n1,_fn,_dL];},_n5,_n7));})]];};},_n8=function(_n9,_na){while(1){var _nb=E(_na);if(!_nb[0]){return false;}else{var _nc=E(_nb[1]);if(!B(A(_dM,[_nc[1],_n9,_nc[2]]))){_na=_nb[2];continue;}else{return true;}}}},_nd=[0,_f],_ne=function(_nf,_ng,_nh,_ni,_nj,_nk,_nl,_nm,_nn,_no,_np){var _nq=E(_ni);return !B(A(_nq[1],[new T(function(){return B(A(_nn,[_no]));}),_np]))?!B(_n8(_no,B(A(_nk,[_np]))))?[0,[1,[0,[0,_nf,[0,_ng,_nh,_nq,_nj,_nk,_nl],_nm,_nn],_no,_np],_f]]:[1,[1,_,[0,_nf,[0,_ng,_nh,_nq,_nj,_nk,_nl],_nm,_nn],[3,_nh,_nj,_no,_np]]]:E(_nd);},_nr=function(_ns){return new F(function(){return _2x("JudgementHandler.hs:(54,15)-(56,42)|case");});},_nt=new T(function(){return B(_nr(_));}),_nu=new T(function(){return B(unCStr(": empty list"));}),_nv=new T(function(){return B(unCStr("Prelude."));}),_nw=function(_nx){return new F(function(){return err(B(_1F(_nv,new T(function(){return B(_1F(_nx,_nu));},1))));});},_ny=new T(function(){return B(unCStr("head"));}),_nz=new T(function(){return B(_nw(_ny));}),_nA=function(_nB){return E(E(_nB)[2]);},_nC=function(_nD,_nE){while(1){var _nF=E(_nD);if(!_nF){return E(_nE);}else{var _nG=E(_nE);if(!_nG[0]){return [0];}else{_nD=_nF-1|0;_nE=_nG[2];continue;}}}},_nH=function(_nI,_nJ){var _nK=E(_nI)[1];return _nK>=0?B(_nC(_nK,_nJ)):E(_nJ);},_nL=function(_nM){return new F(function(){return _2x("JudgementHandler.hs:96:31-64|function conc");});},_nN=new T(function(){return B(_nL(_));}),_nO=function(_nP){var _nQ=E(_nP);switch(_nQ[0]){case 3:return [2,_,_nQ];case 4:return [4,_,_nQ,_6D];case 5:return [6,_,_nQ,_6D,_6D];case 6:return [8,_,_nQ,_6A];case 7:return [10,_,_nQ,_6A,_6A];default:return E(_jU);}},_nR=function(_nS){var _nT=E(_nS);if(!_nT[0]){return [0];}else{var _nU=E(_nT[1]);if(!_nU[0]){return [0];}else{return new F(function(){return _1F(_nU[1],new T(function(){return B(_nR(_nT[2]));},1));});}}},_nV=function(_nW){var _nX=E(_nW);return [0,[1,[1,new T(function(){return B(_nR(_nX[1]));})],_f],_nX[2]];},_nY=function(_nZ,_o0,_o1){return !B(_83(_nZ,_o0,_o1))?E(_o1):[1,_o0,new T(function(){return B(_7r(function(_o2){return !B(A(_81,[_nZ,_o2,_o0]))?true:false;},_o1));})];},_o3=function(_o4,_o5,_o6,_o7,_o8,_o9,_oa){return function(_ob,_oc){var _od=E(_ob);if(!_od[0]){return new F(function(){return _nV(_oc);});}else{var _oe=E(_oc);return [0,[1,[1,new T(function(){return B(_nY(new T(function(){return B(_j9(function(_of,_og){return new F(function(){return _ao(_oa,_o9,_o8,_o6,_o7,_o4,_o5,_of);});}));}),_od[1],B(_nR(_oe[1]))));})],_f],_oe[2]];}};},_oh=new T(function(){return B(_lG(_cj));}),_oi=function(_oj){return E(E(_oj)[1]);},_ok=function(_ol,_om){var _on=E(_ol);if(!_on){return [0];}else{var _oo=E(_om);return _oo[0]==0?[0]:[1,_oo[1],new T(function(){return B(_ok(_on-1|0,_oo[2]));})];}},_op=function(_oq,_or){return _oq<0?[0]:B(_ok(_oq,_or));},_os=function(_ot,_ou){var _ov=E(_ot)[1];return _ov>0?B(_op(_ov,_ou)):[0];},_ow=function(_ox,_oy){return [1,_,_ox,_oy];},_oz=function(_oA){return E(E(_oA)[2]);},_oB=function(_oC){return E(E(_oC)[4]);},_oD=function(_oE,_oF,_oG){var _oH=E(_oE),_oI=E(_oH[2]);return new F(function(){return _ne(_oH[1],_oI[1],_oI[2],_oI[3],_oI[4],_oI[5],_oI[6],_oH[3],_oH[4],_oF,_oG);});},_oJ=function(_oK,_oL,_oM,_oN,_oO,_oP){var _oQ=B(A(_oM,[_oO,_oP]));if(!_oQ[0]){var _oR=B(A(_oM,[_oP,_oO]));if(!_oR[0]){var _oS=B(A(_oK,[_oO,_oP]));if(!_oS[0]){return [1,[0,new T(function(){return B(_oB(_oL));}),_oO,_oP]];}else{var _oT=B(_oU([0,_oK,_oL,_oM,_oN],_oS[1]));return _oT[0]==0?E(_oT):[1,[2,new T(function(){return B(_oB(_oL));}),_oT[1],_oO,_oP]];}}else{var _oV=E(_oR[1]);return new F(function(){return _oD(_oV[1],_oV[2],_oV[3]);});}}else{var _oW=E(_oQ[1]);return new F(function(){return _oD(_oW[1],_oW[2],_oW[3]);});}},_oX=function(_oY){return E(E(_oY)[6]);},_oU=function(_oZ,_p0){var _p1=E(_p0);if(!_p1[0]){return E(_nd);}else{var _p2=E(_p1[1]),_p3=E(_p2[1]),_p4=B(_oJ(_p3[1],_p3[2],_p3[3],_p3[4],_p2[2],_p2[3]));if(!_p4[0]){var _p5=_p4[1],_p6=B(_oU(_oZ,B(_7U(function(_p7){var _p8=E(_p7),_p9=_p8[1];return [0,_p9,new T(function(){return B(A(_oX,[B(_oz(_p9)),_p5,_p8[2]]));}),new T(function(){return B(A(_oX,[B(_oz(_p9)),_p5,_p8[3]]));})];},_p1[2]))));if(!_p6[0]){var _pa=_p6[1];return [0,new T(function(){var _pb=function(_pc){var _pd=E(_pc);return _pd[0]==0?E(_pa):[1,new T(function(){var _pe=E(_pd[1]),_pf=_pe[1];return [0,_pf,_pe[2],new T(function(){return B(A(_oX,[B(_oz(_pf)),_pa,_pe[3]]));})];}),new T(function(){return B(_pb(_pd[2]));})];};return B(_pb(_p5));})];}else{return [1,new T(function(){return B(_ow(_oZ,_p6[1]));})];}}else{return [1,[1,_,_p3,_p4[1]]];}}},_pg=function(_ph,_pi,_pj,_pk,_pl,_pm,_pn,_po,_pp,_pq,_pr,_ps){var _pt=new T(function(){return B(_nA(_ps));}),_pu=function(_pv,_pw){return new F(function(){return _ao(_pn,_pm,_pl,_pj,_pk,_ph,_pi,_pv);});},_px=new T(function(){return B(_jg(_oh,_hb,new T(function(){return B(_j9(_pu));}),new T(function(){return B(_kk(_pu));}),_pn,_pm,_pl,_pk,_pj,_ph,_pi));}),_py=function(_pz,_pA){return new F(function(){return _kr(_pr,_pp,_pq,_pk,_pn,_pj,_pm,_pl,_ph,_pi,_pz,_pA);});};return function(_pB,_pC,_pD){var _pE=new T(function(){return B(A(_po,[_pD]));});return [0,new T(function(){return B(_m4(function(_pF,_pG){var _pH=B(A(new T(function(){return B(_o3(_ph,_pi,_pj,_pk,_pl,_pm,_pn));}),[new T(function(){var _pI=E(E(_pG)[1]);if(!_pI[0]){var _pJ=[0];}else{var _pK=E(_pI[1]),_pJ=_pK[0]==0?[0]:[1,new T(function(){var _pL=E(_pK[1]);return _pL[0]==0?E(_nz):B(_cJ(new T(function(){var _pM=E(B(A(_pt,[_pB]))[2]);if(!_pM[0]){var _pN=E(_nN);}else{var _pO=E(_pM[1]);if(!_pO[0]){var _pP=E(_nN);}else{var _pQ=_pO[1];if(!E(_pO[2])[0]){var _pR=B(_jF(_py,_px,_pQ,_pE));if(!_pR[0]){var _pS=B(_jF(_py,_px,_pE,_pQ));if(!_pS[0]){var _pT=B(_py(_pQ,_pE));if(!_pT[0]){var _pU=[0];}else{var _pV=B(_oU([0,_py,_px,function(_pW,_pX){return new F(function(){return _jF(_py,_px,_pW,_pX);});},_nO],_pT[1])),_pU=_pV[0]==0?E(_pV[1]):[0];}var _pY=_pU;}else{var _pZ=E(_pS[1]),_q0=E(_pZ[1]),_q1=E(_q0[2]),_q2=B(_ne(_q0[1],_q1[1],_q1[2],_q1[3],_q1[4],_q1[5],_q1[6],_q0[3],_q0[4],_pZ[2],_pZ[3])),_pY=_q2[0]==0?E(_q2[1]):[0];}var _q3=_pY;}else{var _q4=E(_pR[1]),_q5=E(_q4[1]),_q6=E(_q5[2]),_q7=B(_ne(_q5[1],_q6[1],_q6[2],_q6[3],_q6[4],_q6[5],_q6[6],_q5[3],_q5[4],_q4[2],_q4[3])),_q3=_q7[0]==0?E(_q7[1]):[0];}var _q8=_q3;}else{var _q8=E(_nN);}var _pP=_q8;}var _pN=_pP;}var _q9=_pN;return _q9;}),_pL[1]));})];}var _qa=_pJ;return _qa;}),_pF])),_qb=_pH[2],_qc=E(E(_pG)[1]);if(!_qc[0]){return E(_nt);}else{var _qd=E(_qc[1]);if(!_qd[0]){return E(_qc[2])[0]==0?E(_pH):E(_nt);}else{var _qe=E(_pH[1]);if(!_qe[0]){return [0,_f,_qb];}else{var _qf=E(_qe[1]);if(!_qf[0]){return E(_pH);}else{var _qg=_qf[1],_qh=new T(function(){return [0,B(_iX(_qd[1],0))];});return [0,[1,[1,new T(function(){return B(_os(_qh,_qg));})],[1,[1,new T(function(){return B(_nH(_qh,_qg));})],_qe[2]]],_qb];}}}}},_pC,new T(function(){return B(A(new T(function(){return B(_oi(_ps));}),[_pB]));},1)));}),[0,new T(function(){return E(B(A(_pt,[_pB]))[1]);}),[1,[1,_pE,_f]]]];};},_qi=[1],_qj=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_qk=function(_ql){return new F(function(){return err(_qj);});},_qm=new T(function(){return B(_qk(_));}),_qn=function(_qo,_qp,_qq){var _qr=E(_qq);if(!_qr[0]){var _qs=_qr[1],_qt=E(_qp);if(!_qt[0]){var _qu=_qt[1],_qv=_qt[2];if(_qu<=(imul(3,_qs)|0)){return [0,(1+_qu|0)+_qs|0,E(E(_qo)),E(_qt),E(_qr)];}else{var _qw=E(_qt[3]);if(!_qw[0]){var _qx=_qw[1],_qy=E(_qt[4]);if(!_qy[0]){var _qz=_qy[1],_qA=_qy[2],_qB=_qy[3];if(_qz>=(imul(2,_qx)|0)){var _qC=function(_qD){var _qE=E(_qy[4]);return _qE[0]==0?[0,(1+_qu|0)+_qs|0,E(_qA),E([0,(1+_qx|0)+_qD|0,E(_qv),E(_qw),E(_qB)]),E([0,(1+_qs|0)+_qE[1]|0,E(E(_qo)),E(_qE),E(_qr)])]:[0,(1+_qu|0)+_qs|0,E(_qA),E([0,(1+_qx|0)+_qD|0,E(_qv),E(_qw),E(_qB)]),E([0,1+_qs|0,E(E(_qo)),E(_qi),E(_qr)])];},_qF=E(_qB);return _qF[0]==0?B(_qC(_qF[1])):B(_qC(0));}else{return [0,(1+_qu|0)+_qs|0,E(_qv),E(_qw),E([0,(1+_qs|0)+_qz|0,E(E(_qo)),E(_qy),E(_qr)])];}}else{return E(_qm);}}else{return E(_qm);}}}else{return [0,1+_qs|0,E(E(_qo)),E(_qi),E(_qr)];}}else{var _qG=E(_qp);if(!_qG[0]){var _qH=_qG[1],_qI=_qG[2],_qJ=_qG[4],_qK=E(_qG[3]);if(!_qK[0]){var _qL=_qK[1],_qM=E(_qJ);if(!_qM[0]){var _qN=_qM[1],_qO=_qM[2],_qP=_qM[3];if(_qN>=(imul(2,_qL)|0)){var _qQ=function(_qR){var _qS=E(_qM[4]);return _qS[0]==0?[0,1+_qH|0,E(_qO),E([0,(1+_qL|0)+_qR|0,E(_qI),E(_qK),E(_qP)]),E([0,1+_qS[1]|0,E(E(_qo)),E(_qS),E(_qi)])]:[0,1+_qH|0,E(_qO),E([0,(1+_qL|0)+_qR|0,E(_qI),E(_qK),E(_qP)]),E([0,1,E(E(_qo)),E(_qi),E(_qi)])];},_qT=E(_qP);return _qT[0]==0?B(_qQ(_qT[1])):B(_qQ(0));}else{return [0,1+_qH|0,E(_qI),E(_qK),E([0,1+_qN|0,E(E(_qo)),E(_qM),E(_qi)])];}}else{return [0,3,E(_qI),E(_qK),E([0,1,E(E(_qo)),E(_qi),E(_qi)])];}}else{var _qU=E(_qJ);return _qU[0]==0?[0,3,E(_qU[2]),E([0,1,E(_qI),E(_qi),E(_qi)]),E([0,1,E(E(_qo)),E(_qi),E(_qi)])]:[0,2,E(E(_qo)),E(_qG),E(_qi)];}}else{return [0,1,E(E(_qo)),E(_qi),E(_qi)];}}},_qV=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_qW=function(_qX){return new F(function(){return err(_qV);});},_qY=new T(function(){return B(_qW(_));}),_qZ=function(_r0,_r1,_r2){var _r3=E(_r1);if(!_r3[0]){var _r4=_r3[1],_r5=E(_r2);if(!_r5[0]){var _r6=_r5[1],_r7=_r5[2];if(_r6<=(imul(3,_r4)|0)){return [0,(1+_r4|0)+_r6|0,E(E(_r0)),E(_r3),E(_r5)];}else{var _r8=E(_r5[3]);if(!_r8[0]){var _r9=_r8[1],_ra=_r8[2],_rb=_r8[3],_rc=E(_r5[4]);if(!_rc[0]){var _rd=_rc[1];if(_r9>=(imul(2,_rd)|0)){var _re=function(_rf){var _rg=E(_r0),_rh=E(_r8[4]);return _rh[0]==0?[0,(1+_r4|0)+_r6|0,E(_ra),E([0,(1+_r4|0)+_rf|0,E(_rg),E(_r3),E(_rb)]),E([0,(1+_rd|0)+_rh[1]|0,E(_r7),E(_rh),E(_rc)])]:[0,(1+_r4|0)+_r6|0,E(_ra),E([0,(1+_r4|0)+_rf|0,E(_rg),E(_r3),E(_rb)]),E([0,1+_rd|0,E(_r7),E(_qi),E(_rc)])];},_ri=E(_rb);return _ri[0]==0?B(_re(_ri[1])):B(_re(0));}else{return [0,(1+_r4|0)+_r6|0,E(_r7),E([0,(1+_r4|0)+_r9|0,E(E(_r0)),E(_r3),E(_r8)]),E(_rc)];}}else{return E(_qY);}}else{return E(_qY);}}}else{return [0,1+_r4|0,E(E(_r0)),E(_r3),E(_qi)];}}else{var _rj=E(_r2);if(!_rj[0]){var _rk=_rj[1],_rl=_rj[2],_rm=_rj[4],_rn=E(_rj[3]);if(!_rn[0]){var _ro=_rn[1],_rp=_rn[2],_rq=_rn[3],_rr=E(_rm);if(!_rr[0]){var _rs=_rr[1];if(_ro>=(imul(2,_rs)|0)){var _rt=function(_ru){var _rv=E(_r0),_rw=E(_rn[4]);return _rw[0]==0?[0,1+_rk|0,E(_rp),E([0,1+_ru|0,E(_rv),E(_qi),E(_rq)]),E([0,(1+_rs|0)+_rw[1]|0,E(_rl),E(_rw),E(_rr)])]:[0,1+_rk|0,E(_rp),E([0,1+_ru|0,E(_rv),E(_qi),E(_rq)]),E([0,1+_rs|0,E(_rl),E(_qi),E(_rr)])];},_rx=E(_rq);return _rx[0]==0?B(_rt(_rx[1])):B(_rt(0));}else{return [0,1+_rk|0,E(_rl),E([0,1+_ro|0,E(E(_r0)),E(_qi),E(_rn)]),E(_rr)];}}else{return [0,3,E(_rp),E([0,1,E(E(_r0)),E(_qi),E(_qi)]),E([0,1,E(_rl),E(_qi),E(_qi)])];}}else{var _ry=E(_rm);return _ry[0]==0?[0,3,E(_rl),E([0,1,E(E(_r0)),E(_qi),E(_qi)]),E(_ry)]:[0,2,E(E(_r0)),E(_qi),E(_rj)];}}else{return [0,1,E(E(_r0)),E(_qi),E(_qi)];}}},_rz=function(_rA){return [0,1,E(E(_rA)),E(_qi),E(_qi)];},_rB=function(_rC,_rD){var _rE=E(_rD);if(!_rE[0]){return new F(function(){return _qn(_rE[2],B(_rB(_rC,_rE[3])),_rE[4]);});}else{return new F(function(){return _rz(_rC);});}},_rF=function(_rG,_rH){var _rI=E(_rH);if(!_rI[0]){return new F(function(){return _qZ(_rI[2],_rI[3],B(_rF(_rG,_rI[4])));});}else{return new F(function(){return _rz(_rG);});}},_rJ=function(_rK,_rL,_rM,_rN,_rO){return new F(function(){return _qZ(_rM,_rN,B(_rF(_rK,_rO)));});},_rP=function(_rQ,_rR,_rS,_rT,_rU){return new F(function(){return _qn(_rS,B(_rB(_rQ,_rT)),_rU);});},_rV=function(_rW,_rX,_rY,_rZ,_s0,_s1){var _s2=E(_rX);if(!_s2[0]){var _s3=_s2[1],_s4=_s2[2],_s5=_s2[3],_s6=_s2[4];if((imul(3,_s3)|0)>=_rY){if((imul(3,_rY)|0)>=_s3){return [0,(_s3+_rY|0)+1|0,E(E(_rW)),E(_s2),E([0,_rY,E(_rZ),E(_s0),E(_s1)])];}else{return new F(function(){return _qZ(_s4,_s5,B(_rV(_rW,_s6,_rY,_rZ,_s0,_s1)));});}}else{return new F(function(){return _qn(_rZ,B(_s7(_rW,_s3,_s4,_s5,_s6,_s0)),_s1);});}}else{return new F(function(){return _rP(_rW,_rY,_rZ,_s0,_s1);});}},_s7=function(_s8,_s9,_sa,_sb,_sc,_sd){var _se=E(_sd);if(!_se[0]){var _sf=_se[1],_sg=_se[2],_sh=_se[3],_si=_se[4];if((imul(3,_s9)|0)>=_sf){if((imul(3,_sf)|0)>=_s9){return [0,(_s9+_sf|0)+1|0,E(E(_s8)),E([0,_s9,E(_sa),E(_sb),E(_sc)]),E(_se)];}else{return new F(function(){return _qZ(_sa,_sb,B(_rV(_s8,_sc,_sf,_sg,_sh,_si)));});}}else{return new F(function(){return _qn(_sg,B(_s7(_s8,_s9,_sa,_sb,_sc,_sh)),_si);});}}else{return new F(function(){return _rJ(_s8,_s9,_sa,_sb,_sc);});}},_sj=function(_sk,_sl,_sm){var _sn=E(_sl);if(!_sn[0]){var _so=_sn[1],_sp=_sn[2],_sq=_sn[3],_sr=_sn[4],_ss=E(_sm);if(!_ss[0]){var _st=_ss[1],_su=_ss[2],_sv=_ss[3],_sw=_ss[4];if((imul(3,_so)|0)>=_st){if((imul(3,_st)|0)>=_so){return [0,(_so+_st|0)+1|0,E(E(_sk)),E(_sn),E(_ss)];}else{return new F(function(){return _qZ(_sp,_sq,B(_rV(_sk,_sr,_st,_su,_sv,_sw)));});}}else{return new F(function(){return _qn(_su,B(_s7(_sk,_so,_sp,_sq,_sr,_sv)),_sw);});}}else{return new F(function(){return _rJ(_sk,_so,_sp,_sq,_sr);});}}else{return new F(function(){return _rB(_sk,_sm);});}},_sx=function(_sy,_sz,_sA,_sB){var _sC=E(_sB);if(!_sC[0]){var _sD=new T(function(){var _sE=B(_sx(_sC[1],_sC[2],_sC[3],_sC[4]));return [0,_sE[1],_sE[2]];});return [0,new T(function(){return E(E(_sD)[1]);}),new T(function(){return B(_qn(_sz,_sA,E(_sD)[2]));})];}else{return [0,_sz,_sA];}},_sF=function(_sG,_sH,_sI,_sJ){var _sK=E(_sI);if(!_sK[0]){var _sL=new T(function(){var _sM=B(_sF(_sK[1],_sK[2],_sK[3],_sK[4]));return [0,_sM[1],_sM[2]];});return [0,new T(function(){return E(E(_sL)[1]);}),new T(function(){return B(_qZ(_sH,E(_sL)[2],_sJ));})];}else{return [0,_sH,_sJ];}},_sN=function(_sO,_sP){var _sQ=E(_sO);if(!_sQ[0]){var _sR=_sQ[1],_sS=E(_sP);if(!_sS[0]){var _sT=_sS[1];if(_sR<=_sT){var _sU=B(_sF(_sT,_sS[2],_sS[3],_sS[4]));return new F(function(){return _qn(_sU[1],_sQ,_sU[2]);});}else{var _sV=B(_sx(_sR,_sQ[2],_sQ[3],_sQ[4]));return new F(function(){return _qZ(_sV[1],_sV[2],_sS);});}}else{return E(_sQ);}}else{return E(_sP);}},_sW=function(_sX,_sY,_sZ,_t0,_t1){var _t2=E(_sX);if(!_t2[0]){var _t3=_t2[1],_t4=_t2[2],_t5=_t2[3],_t6=_t2[4];if((imul(3,_t3)|0)>=_sY){if((imul(3,_sY)|0)>=_t3){return new F(function(){return _sN(_t2,[0,_sY,E(_sZ),E(_t0),E(_t1)]);});}else{return new F(function(){return _qZ(_t4,_t5,B(_sW(_t6,_sY,_sZ,_t0,_t1)));});}}else{return new F(function(){return _qn(_sZ,B(_t7(_t3,_t4,_t5,_t6,_t0)),_t1);});}}else{return [0,_sY,E(_sZ),E(_t0),E(_t1)];}},_t7=function(_t8,_t9,_ta,_tb,_tc){var _td=E(_tc);if(!_td[0]){var _te=_td[1],_tf=_td[2],_tg=_td[3],_th=_td[4];if((imul(3,_t8)|0)>=_te){if((imul(3,_te)|0)>=_t8){return new F(function(){return _sN([0,_t8,E(_t9),E(_ta),E(_tb)],_td);});}else{return new F(function(){return _qZ(_t9,_ta,B(_sW(_tb,_te,_tf,_tg,_th)));});}}else{return new F(function(){return _qn(_tf,B(_t7(_t8,_t9,_ta,_tb,_tg)),_th);});}}else{return [0,_t8,E(_t9),E(_ta),E(_tb)];}},_ti=function(_tj,_tk){var _tl=E(_tj);if(!_tl[0]){var _tm=_tl[1],_tn=_tl[2],_to=_tl[3],_tp=_tl[4],_tq=E(_tk);if(!_tq[0]){var _tr=_tq[1],_ts=_tq[2],_tt=_tq[3],_tu=_tq[4];if((imul(3,_tm)|0)>=_tr){if((imul(3,_tr)|0)>=_tm){return new F(function(){return _sN(_tl,_tq);});}else{return new F(function(){return _qZ(_tn,_to,B(_sW(_tp,_tr,_ts,_tt,_tu)));});}}else{return new F(function(){return _qn(_ts,B(_t7(_tm,_tn,_to,_tp,_tt)),_tu);});}}else{return E(_tl);}}else{return E(_tk);}},_tv=function(_tw,_tx){var _ty=E(_tx);if(!_ty[0]){var _tz=_ty[2],_tA=_ty[3],_tB=_ty[4];if(!B(A(_tw,[_tz]))){return new F(function(){return _ti(B(_tv(_tw,_tA)),B(_tv(_tw,_tB)));});}else{return new F(function(){return _sj(_tz,B(_tv(_tw,_tA)),B(_tv(_tw,_tB)));});}}else{return [1];}},_tC=function(_tD,_tE,_tF,_tG){while(1){var _tH=E(_tG);if(!_tH[0]){_tD=_tH[1];_tE=_tH[2];_tF=_tH[3];_tG=_tH[4];continue;}else{return E(_tE);}}},_tI=function(_tJ,_tK){return [0];},_tL=function(_tM){return E(E(_tM)[1]);},_tN=function(_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX,_tY){var _tZ=new T(function(){return B(_pg(_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX,_tY,_fs));}),_u0=new T(function(){return B(_mQ(_tY,_tW,_tX,_tR,_tU,_tQ,_tT,_tS,_tO,_tP));}),_u1=[0,_u0,new T(function(){return B(_fb(_oh,_hb,new T(function(){return B(_bs(new T(function(){return B(_ch(new T(function(){return B(_bV(_tU,_tT,_tS,_tR,_tQ,_tO,_tP));})));})));}),new T(function(){return B(_g0(new T(function(){return B(_gZ(new T(function(){return B(_gp(_tU,_tT,_tS,_tR,_tQ,_tO,_tP));})));})));}),_tU,_tT,_tS,_tR,_tQ,_tO,_tP));}),_tI,_61];return function(_u2,_u3,_u4){var _u5=B(_tv(function(_u6){var _u7=B(A(_u0,[new T(function(){return B(A(_tZ,[_u6,_u3,_u4]));}),_u6]));return _u7[0]==0?false:B(_oU(_u1,_u7[1]))[0]==0?true:false;},B(_tL(_u2))));if(!_u5[0]){var _u8=new T(function(){var _u9=E(_u5[4]);return _u9[0]==0?B(_tC(_u9[1],_u9[2],_u9[3],_u9[4])):E(_u5[2]);}),_ua=new T(function(){return B(A(_tZ,[_u8,_u3,_u4]));}),_ub=B(A(_u0,[_u8,_ua]));if(!_ub[0]){return [0];}else{var _uc=B(_oU(_u1,_ub[1]));if(!_uc[0]){var _ud=_uc[1];return [1,new T(function(){var _ue=E(E(_ua)[2]);return [0,new T(function(){return B(_7U(function(_uf){return new F(function(){return _dg(_ud,_uf);});},_ue[1]));}),new T(function(){return B(_dg(_ud,_ue[2]));})];})];}else{return [0];}}}else{return [0];}};},_ug=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_uh=new T(function(){return B(err(_ug));}),_ui=function(_uj,_uk,_ul,_um){while(1){var _un=E(_ul);if(!_un[0]){_uj=_un[1];_uk=_un[2];_ul=_un[3];_um=_un[4];continue;}else{return E(_uk);}}},_uo=function(_up,_uq){var _ur=B(_tv(function(_us){return new F(function(){return _bw(E(_us)[2],_up);});},_uq));if(!_ur[0]){var _ut=E(_ur[3]);return _ut[0]==0?B(_ui(_ut[1],_ut[2],_ut[3],_ut[4])):E(_ur[2]);}else{return E(_uh);}},_uu=[1,_f],_uv=function(_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG,_uH,_uI,_uJ){var _uK=E(_uJ);if(!_uK[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_uD,[_uI]));}),_f]],_f],[1,[1,new T(function(){return B(A(_uD,[_uI]));}),_f]]]];}else{var _uL=function(_uM){var _uN=E(_uM);if(!_uN[0]){return E(_uu);}else{var _uO=E(_uN[1]),_uP=B(_uv(_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG,_uH,_uO[1],_uO[2]));if(!_uP[0]){return [0];}else{var _uQ=B(_uL(_uN[2]));return _uQ[0]==0?[0]:[1,[1,_uP[1],_uQ[1]]];}}},_uR=B(_uL(_uK[2]));return _uR[0]==0?[0]:B(A(_tN,[_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG,new T(function(){return B(_uo(_uK[1],_uH));}),_uR[1],_uI]));}},_uS=2,_uT=function(_uU,_){return [0,[0,_4v,[1,_uU]],_uU];},_uV=function(_uW){return function(_uX,_){return [0,[0,_4v,[1,[1,_4l,new T(function(){var _uY=E(_uW);return B(_1F(B(_4f(0,E(_uY[2])[1],_f)),_uY[1]));})]]],_uX];};},_uZ=function(_v0,_){return new F(function(){return _57(_uT,_uV,_v0,_);});},_v1=function(_v2){return function(_v3,_){return [0,[0,_4v,[1,[1,_4l,new T(function(){var _v4=E(_v2);return B(_1F(B(_4f(0,E(_v4[2])[1],_f)),_v4[1]));})]]],_v3];};},_v5=function(_v0,_){return new F(function(){return _57(_uT,_v1,_v0,_);});},_v6=new T(function(){return B(unCStr("rslt"));}),_v7=new T(function(){return B(unCStr("root"));}),_v8=new T(function(){return B(unCStr("analysis"));}),_v9=new T(function(){return B(unCStr("invalid"));}),_va=function(_v0,_){return new F(function(){return _4V(_5U,_v9,_v0,_);});},_vb=[1,_0],_vc=[0,_va,_vb],_vd=function(_ve,_){return [0,_vc,_ve];},_vf=new T(function(){return B(unCStr("div"));}),_vg=function(_vh,_vi,_vj,_){var _vk=jsCreateElem(toJSStr(E(_vf))),_vl=_vk,_vm=jsAppendChild(_vl,E(_vj)[1]),_vn=[0,_vl],_vo=B(A(_vh,[_vi,_vn,_])),_vp=_vo;return _vn;},_vq=function(_vr,_vs,_){var _vt=E(_vr);if(!_vt[0]){return _vs;}else{var _vu=B(_vg(_5U,_vt[1],_vs,_)),_vv=_vu,_vw=B(_vq(_vt[2],_vs,_)),_vx=_vw;return _vs;}},_vy=function(_vz){return function(_vA,_){return [0,[0,_4v,[1,[1,_4l,new T(function(){var _vB=E(_vz);return B(_1F(B(_4f(0,E(_vB[2])[1],_f)),_vB[1]));})]]],_vA];};},_vC=function(_v0,_){return new F(function(){return _57(_uT,_vy,_v0,_);});},_vD=new T(function(){return B(unCStr("class"));}),_vE=new T(function(){return B(unCStr("span"));}),_vF=function(_vG,_vH,_vI,_vJ,_){var _vK=B(A(_vI,[_vJ,_])),_vL=_vK,_vM=E(_vL),_vN=E(_vM[1]),_vO=_vN[1];return [0,[0,function(_vP,_){var _vQ=jsFind(toJSStr(E(_vG))),_vR=_vQ,_vS=E(_vR);if(!_vS[0]){return _vP;}else{var _vT=_vS[1];switch(E(_vH)){case 0:var _vU=B(A(_vO,[_vT,_])),_vV=_vU;return _vP;case 1:var _vW=E(_vT),_vX=_vW[1],_vY=jsGetChildren(_vX),_vZ=_vY,_w0=E(_vZ);if(!_w0[0]){var _w1=B(A(_vO,[_vW,_])),_w2=_w1;return _vP;}else{var _w3=jsCreateElem(toJSStr(E(_vE))),_w4=_w3,_w5=jsAddChildBefore(_w4,_vX,E(_w0[1])[1]),_w6=B(A(_vO,[[0,_w4],_])),_w7=_w6;return _vP;}break;default:var _w8=E(_vT),_w9=jsClearChildren(_w8[1]),_wa=B(A(_vO,[_w8,_])),_wb=_wa;return _vP;}}},_vN[2]],_vM[2]];},_wc=function(_wd,_we){while(1){var _wf=E(_wd);if(!_wf[0]){return E(_we)[0]==0?1:0;}else{var _wg=E(_we);if(!_wg[0]){return 2;}else{var _wh=E(_wf[1])[1],_wi=E(_wg[1])[1];if(_wh!=_wi){return _wh>_wi?2:0;}else{_wd=_wf[2];_we=_wg[2];continue;}}}}},_wj=new T(function(){return B(_1F(_f,_f));}),_wk=function(_wl,_wm,_wn,_wo,_wp,_wq,_wr,_ws){var _wt=[0,_wl,_wm,_wn],_wu=function(_wv){var _ww=E(_wo);if(!_ww[0]){var _wx=E(_ws);if(!_wx[0]){switch(B(_wc(_wl,_wp))){case 0:return [0,[0,_wp,_wq,_wr],_f];case 1:return _wm>=_wq?_wm!=_wq?[0,_wt,_f]:_wn>=_wr?_wn!=_wr?[0,_wt,_f]:[0,_wt,_wj]:[0,[0,_wp,_wq,_wr],_f]:[0,[0,_wp,_wq,_wr],_f];default:return [0,_wt,_f];}}else{return [0,[0,_wp,_wq,_wr],_wx];}}else{switch(B(_wc(_wl,_wp))){case 0:return [0,[0,_wp,_wq,_wr],_ws];case 1:return _wm>=_wq?_wm!=_wq?[0,_wt,_ww]:_wn>=_wr?_wn!=_wr?[0,_wt,_ww]:[0,_wt,new T(function(){return B(_1F(_ww,_ws));})]:[0,[0,_wp,_wq,_wr],_ws]:[0,[0,_wp,_wq,_wr],_ws];default:return [0,_wt,_ww];}}};if(!E(_ws)[0]){var _wy=E(_wo);return _wy[0]==0?B(_wu(_)):[0,_wt,_wy];}else{return new F(function(){return _wu(_);});}},_wz=function(_wA,_wB){while(1){var _wC=E(_wA);if(!_wC[0]){return E(_wB);}else{_wA=_wC[2];var _wD=[1,_wC[1],_wB];_wB=_wD;continue;}}},_wE=new T(function(){return B(_wz(_f,_f));}),_wF=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_wG=new T(function(){return B(err(_wF));}),_wH=function(_wI,_wJ,_wK,_wL,_wM){var _wN=function(_wO,_wP,_wQ){var _wR=[1,_wP,_wO];return new F(function(){return A(_wI,[_wQ,new T(function(){var _wS=E(_wO);return function(_wT,_wU,_wV){return new F(function(){return _wN(_wR,_wT,_wU);});};}),_wL,_wG,function(_wW){return new F(function(){return A(_wK,[new T(function(){return B(_wz(_wR,_f));}),_wQ,new T(function(){var _wX=E(E(_wQ)[2]),_wY=E(_wW),_wZ=E(_wY[1]),_x0=B(_wk(_wZ[1],_wZ[2],_wZ[3],_wY[2],_wX[1],_wX[2],_wX[3],_f));return [0,E(_x0[1]),_x0[2]];})]);});}]);});};return new F(function(){return A(_wI,[_wJ,function(_x1,_x2,_x3){return new F(function(){return _wN(_f,_x1,_x2);});},_wL,_wG,function(_x4){return new F(function(){return A(_wM,[_wE,_wJ,new T(function(){var _x5=E(E(_wJ)[2]),_x6=E(_x4),_x7=E(_x6[1]),_x8=B(_wk(_x7[1],_x7[2],_x7[3],_x6[2],_x5[1],_x5[2],_x5[3],_f));return [0,E(_x8[1]),_x8[2]];})]);});}]);});},_x9=function(_xa,_xb){var _xc=E(_xa),_xd=E(_xc[1]),_xe=E(_xb),_xf=E(_xe[1]),_xg=B(_wk(_xd[1],_xd[2],_xd[3],_xc[2],_xf[1],_xf[2],_xf[3],_xe[2]));return [0,E(_xg[1]),_xg[2]];},_xh=function(_xi,_xj,_xk,_xl,_xm,_xn){var _xo=function(_xp,_xq,_xr,_xs,_xt){return new F(function(){return _wH(_xi,_xq,function(_xu,_xv,_xw){return new F(function(){return A(_xr,[[1,_xp,_xu],_xv,new T(function(){var _xx=E(E(_xv)[2]),_xy=E(_xw),_xz=E(_xy[1]),_xA=B(_wk(_xz[1],_xz[2],_xz[3],_xy[2],_xx[1],_xx[2],_xx[3],_f));return [0,E(_xA[1]),_xA[2]];})]);});},_xs,function(_xB,_xC,_xD){return new F(function(){return A(_xt,[[1,_xp,_xB],_xC,new T(function(){var _xE=E(E(_xC)[2]),_xF=E(_xD),_xG=E(_xF[1]),_xH=B(_wk(_xG[1],_xG[2],_xG[3],_xF[2],_xE[1],_xE[2],_xE[3],_f));return [0,E(_xH[1]),_xH[2]];})]);});});});};return new F(function(){return A(_xi,[_xj,function(_xI,_xJ,_xK){return new F(function(){return _xo(_xI,_xJ,_xk,_xl,function(_xL,_xM,_xN){return new F(function(){return A(_xk,[_xL,_xM,new T(function(){return B(_x9(_xK,_xN));})]);});});});},_xl,function(_xO,_xP,_xQ){return new F(function(){return _xo(_xO,_xP,_xk,_xl,function(_xR,_xS,_xT){return new F(function(){return A(_xm,[_xR,_xS,new T(function(){return B(_x9(_xQ,_xT));})]);});});});},_xn]);});},_xU=function(_xV,_xW,_xX,_xY,_xZ){var _y0=function(_y1,_y2){return new F(function(){return A(_xV,[_y2,new T(function(){var _y3=E(_y1);return function(_y4,_y5,_y6){return new F(function(){return _y0(_f,_y5);});};}),_xY,_wG,function(_y7){return new F(function(){return A(_xX,[_0,_y2,new T(function(){var _y8=E(E(_y2)[2]),_y9=E(_y7),_ya=E(_y9[1]),_yb=B(_wk(_ya[1],_ya[2],_ya[3],_y9[2],_y8[1],_y8[2],_y8[3],_f));return [0,E(_yb[1]),_yb[2]];})]);});}]);});};return new F(function(){return A(_xV,[_xW,function(_yc,_yd,_ye){return new F(function(){return _y0(_f,_yd);});},_xY,_wG,function(_yf){return new F(function(){return A(_xZ,[_0,_xW,new T(function(){var _yg=E(E(_xW)[2]),_yh=E(_yf),_yi=E(_yh[1]),_yj=B(_wk(_yi[1],_yi[2],_yi[3],_yh[2],_yg[1],_yg[2],_yg[3],_f));return [0,E(_yj[1]),_yj[2]];})]);});}]);});},_yk=function(_yl,_ym,_yn,_yo,_yp,_yq,_yr){var _ys=function(_yt,_yu,_yv,_yw,_yx){var _yy=[1,_yt,_f],_yz=function(_yA,_yB,_yC,_yD){return new F(function(){return _yk(_yl,_ym,_yA,function(_yE,_yF,_yG){return new F(function(){return A(_yB,[[1,_yt,_yE],_yF,new T(function(){var _yH=E(E(_yF)[2]),_yI=E(_yG),_yJ=E(_yI[1]),_yK=B(_wk(_yJ[1],_yJ[2],_yJ[3],_yI[2],_yH[1],_yH[2],_yH[3],_f));return [0,E(_yK[1]),_yK[2]];})]);});},_yC,function(_yL,_yM,_yN){return new F(function(){return A(_yD,[[1,_yt,_yL],_yM,new T(function(){var _yO=E(E(_yM)[2]),_yP=E(_yN),_yQ=E(_yP[1]),_yR=B(_wk(_yQ[1],_yQ[2],_yQ[3],_yP[2],_yO[1],_yO[2],_yO[3],_f));return [0,E(_yR[1]),_yR[2]];})]);});},function(_yS){return new F(function(){return A(_yD,[_yy,_yA,new T(function(){var _yT=E(E(_yA)[2]),_yU=_yT[1],_yV=_yT[2],_yW=_yT[3],_yX=E(_yS),_yY=E(_yX[1]),_yZ=B(_wk(_yY[1],_yY[2],_yY[3],_yX[2],_yU,_yV,_yW,_f)),_z0=E(_yZ[1]),_z1=B(_wk(_z0[1],_z0[2],_z0[3],_yZ[2],_yU,_yV,_yW,_f));return [0,E(_z1[1]),_z1[2]];})]);});});});};return new F(function(){return A(_ym,[_yu,function(_z2,_z3,_z4){return new F(function(){return _yz(_z3,_yv,_yw,function(_z5,_z6,_z7){return new F(function(){return A(_yv,[_z5,_z6,new T(function(){return B(_x9(_z4,_z7));})]);});});});},_yw,function(_z8,_z9,_za){return new F(function(){return _yz(_z9,_yv,_yw,function(_zb,_zc,_zd){return new F(function(){return A(_yx,[_zb,_zc,new T(function(){return B(_x9(_za,_zd));})]);});});});},function(_ze){return new F(function(){return A(_yx,[_yy,_yu,new T(function(){var _zf=E(E(_yu)[2]),_zg=E(_ze),_zh=E(_zg[1]),_zi=B(_wk(_zh[1],_zh[2],_zh[3],_zg[2],_zf[1],_zf[2],_zf[3],_f));return [0,E(_zi[1]),_zi[2]];})]);});}]);});};return new F(function(){return A(_yl,[_yn,function(_zj,_zk,_zl){return new F(function(){return _ys(_zj,_zk,_yo,_yp,function(_zm,_zn,_zo){return new F(function(){return A(_yo,[_zm,_zn,new T(function(){return B(_x9(_zl,_zo));})]);});});});},_yp,function(_zp,_zq,_zr){return new F(function(){return _ys(_zp,_zq,_yo,_yp,function(_zs,_zt,_zu){return new F(function(){return A(_yq,[_zs,_zt,new T(function(){return B(_x9(_zr,_zu));})]);});});});},_yr]);});},_zv=function(_zw,_zx){return new F(function(){return A(_zx,[_zw]);});},_zy=[0,34],_zz=[1,_zy,_f],_zA=[0,E(_f)],_zB=[1,_zA,_f],_zC=function(_zD,_zE){var _zF=_zD%_zE;if(_zD<=0){if(_zD>=0){return E(_zF);}else{if(_zE<=0){return E(_zF);}else{var _zG=E(_zF);return _zG==0?0:_zG+_zE|0;}}}else{if(_zE>=0){if(_zD>=0){return E(_zF);}else{if(_zE<=0){return E(_zF);}else{var _zH=E(_zF);return _zH==0?0:_zH+_zE|0;}}}else{var _zI=E(_zF);return _zI==0?0:_zI+_zE|0;}}},_zJ=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_zK=new T(function(){return B(err(_zJ));}),_zL=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_zM=new T(function(){return B(err(_zL));}),_zN=function(_zO,_zP){while(1){var _zQ=E(_zO);if(!_zQ[0]){return E(_zM);}else{var _zR=E(_zP);if(!_zR){return E(_zQ[1]);}else{_zO=_zQ[2];_zP=_zR-1|0;continue;}}}},_zS=new T(function(){return B(unCStr("ACK"));}),_zT=new T(function(){return B(unCStr("BEL"));}),_zU=new T(function(){return B(unCStr("BS"));}),_zV=new T(function(){return B(unCStr("SP"));}),_zW=[1,_zV,_f],_zX=new T(function(){return B(unCStr("US"));}),_zY=[1,_zX,_zW],_zZ=new T(function(){return B(unCStr("RS"));}),_A0=[1,_zZ,_zY],_A1=new T(function(){return B(unCStr("GS"));}),_A2=[1,_A1,_A0],_A3=new T(function(){return B(unCStr("FS"));}),_A4=[1,_A3,_A2],_A5=new T(function(){return B(unCStr("ESC"));}),_A6=[1,_A5,_A4],_A7=new T(function(){return B(unCStr("SUB"));}),_A8=[1,_A7,_A6],_A9=new T(function(){return B(unCStr("EM"));}),_Aa=[1,_A9,_A8],_Ab=new T(function(){return B(unCStr("CAN"));}),_Ac=[1,_Ab,_Aa],_Ad=new T(function(){return B(unCStr("ETB"));}),_Ae=[1,_Ad,_Ac],_Af=new T(function(){return B(unCStr("SYN"));}),_Ag=[1,_Af,_Ae],_Ah=new T(function(){return B(unCStr("NAK"));}),_Ai=[1,_Ah,_Ag],_Aj=new T(function(){return B(unCStr("DC4"));}),_Ak=[1,_Aj,_Ai],_Al=new T(function(){return B(unCStr("DC3"));}),_Am=[1,_Al,_Ak],_An=new T(function(){return B(unCStr("DC2"));}),_Ao=[1,_An,_Am],_Ap=new T(function(){return B(unCStr("DC1"));}),_Aq=[1,_Ap,_Ao],_Ar=new T(function(){return B(unCStr("DLE"));}),_As=[1,_Ar,_Aq],_At=new T(function(){return B(unCStr("SI"));}),_Au=[1,_At,_As],_Av=new T(function(){return B(unCStr("SO"));}),_Aw=[1,_Av,_Au],_Ax=new T(function(){return B(unCStr("CR"));}),_Ay=[1,_Ax,_Aw],_Az=new T(function(){return B(unCStr("FF"));}),_AA=[1,_Az,_Ay],_AB=new T(function(){return B(unCStr("VT"));}),_AC=[1,_AB,_AA],_AD=new T(function(){return B(unCStr("LF"));}),_AE=[1,_AD,_AC],_AF=new T(function(){return B(unCStr("HT"));}),_AG=[1,_AF,_AE],_AH=[1,_zU,_AG],_AI=[1,_zT,_AH],_AJ=[1,_zS,_AI],_AK=new T(function(){return B(unCStr("ENQ"));}),_AL=[1,_AK,_AJ],_AM=new T(function(){return B(unCStr("EOT"));}),_AN=[1,_AM,_AL],_AO=new T(function(){return B(unCStr("ETX"));}),_AP=[1,_AO,_AN],_AQ=new T(function(){return B(unCStr("STX"));}),_AR=[1,_AQ,_AP],_AS=new T(function(){return B(unCStr("SOH"));}),_AT=[1,_AS,_AR],_AU=new T(function(){return B(unCStr("NUL"));}),_AV=[1,_AU,_AT],_AW=[0,92],_AX=new T(function(){return B(unCStr("\\DEL"));}),_AY=new T(function(){return B(unCStr("\\a"));}),_AZ=new T(function(){return B(unCStr("\\\\"));}),_B0=new T(function(){return B(unCStr("\\SO"));}),_B1=new T(function(){return B(unCStr("\\r"));}),_B2=new T(function(){return B(unCStr("\\f"));}),_B3=new T(function(){return B(unCStr("\\v"));}),_B4=new T(function(){return B(unCStr("\\n"));}),_B5=new T(function(){return B(unCStr("\\t"));}),_B6=new T(function(){return B(unCStr("\\b"));}),_B7=function(_B8,_B9){if(_B8<=127){var _Ba=E(_B8);switch(_Ba){case 92:return new F(function(){return _1F(_AZ,_B9);});break;case 127:return new F(function(){return _1F(_AX,_B9);});break;default:if(_Ba<32){var _Bb=E(_Ba);switch(_Bb){case 7:return new F(function(){return _1F(_AY,_B9);});break;case 8:return new F(function(){return _1F(_B6,_B9);});break;case 9:return new F(function(){return _1F(_B5,_B9);});break;case 10:return new F(function(){return _1F(_B4,_B9);});break;case 11:return new F(function(){return _1F(_B3,_B9);});break;case 12:return new F(function(){return _1F(_B2,_B9);});break;case 13:return new F(function(){return _1F(_B1,_B9);});break;case 14:return new F(function(){return _1F(_B0,new T(function(){var _Bc=E(_B9);if(!_Bc[0]){var _Bd=[0];}else{var _Bd=E(E(_Bc[1])[1])==72?B(unAppCStr("\\&",_Bc)):E(_Bc);}return _Bd;},1));});break;default:return new F(function(){return _1F([1,_AW,new T(function(){var _Be=_Bb;return _Be>=0?B(_zN(_AV,_Be)):E(_zK);})],_B9);});}}else{return [1,[0,_Ba],_B9];}}}else{return [1,_AW,new T(function(){var _Bf=jsShowI(_B8),_Bg=_Bf;return B(_1F(fromJSStr(_Bg),new T(function(){var _Bh=E(_B9);if(!_Bh[0]){var _Bi=[0];}else{var _Bj=E(_Bh[1])[1];if(_Bj<48){var _Bk=E(_Bh);}else{var _Bk=_Bj>57?E(_Bh):B(unAppCStr("\\&",_Bh));}var _Bl=_Bk,_Bm=_Bl,_Bi=_Bm;}return _Bi;},1)));})];}},_Bn=new T(function(){return B(unCStr("\\\""));}),_Bo=function(_Bp,_Bq){var _Br=E(_Bp);if(!_Br[0]){return E(_Bq);}else{var _Bs=_Br[2],_Bt=E(E(_Br[1])[1]);if(_Bt==34){return new F(function(){return _1F(_Bn,new T(function(){return B(_Bo(_Bs,_Bq));},1));});}else{return new F(function(){return _B7(_Bt,new T(function(){return B(_Bo(_Bs,_Bq));}));});}}},_Bu=function(_Bv,_Bw,_Bx,_By,_Bz,_BA,_BB,_BC,_BD,_BE){var _BF=[0,_Bz,_BA,_BB];return new F(function(){return A(_Bv,[new T(function(){return B(A(_Bw,[_By]));}),function(_BG){var _BH=E(_BG);if(!_BH[0]){return E(new T(function(){return B(A(_BE,[[0,E(_BF),_zB]]));}));}else{var _BI=E(_BH[1]),_BJ=_BI[1],_BK=_BI[2];if(!B(A(_Bx,[_BJ]))){return new F(function(){return A(_BE,[[0,E(_BF),[1,[0,E([1,_zy,new T(function(){return B(_Bo([1,_BJ,_f],_zz));})])],_f]]]);});}else{var _BL=E(_BJ);switch(E(_BL[1])){case 9:var _BM=[0,_Bz,_BA,(_BB+8|0)-B(_zC(_BB-1|0,8))|0];break;case 10:var _BM=E([0,_Bz,_BA+1|0,1]);break;default:var _BM=E([0,_Bz,_BA,_BB+1|0]);}var _BN=_BM,_BO=[0,E(_BN),_f],_BP=[0,_BK,E(_BN),E(_BC)];return new F(function(){return A(_BD,[_BL,_BP,_BO]);});}}}]);});},_BQ=function(_BR,_BS){return E(_BR)[1]!=E(_BS)[1];},_BT=function(_BU,_BV){return E(_BU)[1]==E(_BV)[1];},_BW=[0,_BT,_BQ],_BX=new T(function(){return B(unCStr(" 	"));}),_BY=function(_BZ){return new F(function(){return _83(_BW,_BZ,_BX);});},_C0=function(_C1,_C2){return E(_C2);},_C3=function(_C4){return new F(function(){return err(_C4);});},_C5=function(_C6){return E(_C6);},_C7=[0,_zv,_C0,_C5,_C3],_C8=function(_C9){return E(E(_C9)[3]);},_Ca=function(_Cb,_Cc){var _Cd=E(_Cc);return _Cd[0]==0?B(A(_C8,[_Cb,_10])):B(A(_C8,[_Cb,[1,[0,_Cd[1],_Cd[2]]]]));},_Ce=function(_Cf){return new F(function(){return _Ca(_C7,_Cf);});},_Cg=function(_Ch,_Ci,_Cj,_Ck,_Cl){var _Cm=E(_Ch),_Cn=E(_Cm[2]);return new F(function(){return _Bu(_zv,_Ce,_BY,_Cm[1],_Cn[1],_Cn[2],_Cn[3],_Cm[3],_Ci,_Cl);});},_Co=function(_Cp){return [0,_Cp,function(_Cq){return new F(function(){return _Ca(_Cp,_Cq);});}];},_Cr=new T(function(){return B(_Co(_C7));}),_Cs=function(_Ct){return [2,E(E(_Ct))];},_Cu=function(_Cv,_Cw){switch(E(_Cv)[0]){case 0:switch(E(_Cw)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_Cw)[0]==1?false:true;case 2:return E(_Cw)[0]==2?false:true;default:return E(_Cw)[0]==3?false:true;}},_Cx=[2,E(_f)],_Cy=function(_Cq){return new F(function(){return _Cu(_Cx,_Cq);});},_Cz=function(_CA,_CB,_CC){var _CD=E(_CC);if(!_CD[0]){return [0,_CA,[1,_Cx,new T(function(){return B(_7r(_Cy,_CB));})]];}else{var _CE=_CD[1],_CF=E(_CD[2]);if(!_CF[0]){var _CG=new T(function(){return [2,E(E(_CE))];});return [0,_CA,[1,_CG,new T(function(){return B(_7r(function(_Cq){return new F(function(){return _Cu(_CG,_Cq);});},_CB));})]];}else{var _CH=new T(function(){return [2,E(E(_CE))];}),_CI=function(_CJ){var _CK=E(_CJ);if(!_CK[0]){return [0,_CA,[1,_CH,new T(function(){return B(_7r(function(_Cq){return new F(function(){return _Cu(_CH,_Cq);});},_CB));})]];}else{var _CL=B(_CI(_CK[2]));return [0,_CL[1],[1,new T(function(){return B(_Cs(_CK[1]));}),_CL[2]]];}};return new F(function(){return (function(_CM,_CN){var _CO=B(_CI(_CN));return [0,_CO[1],[1,new T(function(){return B(_Cs(_CM));}),_CO[2]]];})(_CF[1],_CF[2]);});}}},_CP=function(_CQ,_CR){var _CS=E(_CQ),_CT=B(_Cz(_CS[1],_CS[2],_CR));return [0,E(_CT[1]),_CT[2]];},_CU=function(_CV,_CW,_CX,_CY,_CZ,_D0,_D1){return new F(function(){return A(_CV,[_CX,_CY,_CZ,function(_D2,_D3,_D4){return new F(function(){return A(_D0,[_D2,_D3,new T(function(){var _D5=E(_D4),_D6=E(_D5[2]);if(!_D6[0]){var _D7=E(_D5);}else{var _D8=B(_Cz(_D5[1],_D6,_CW)),_D7=[0,E(_D8[1]),_D8[2]];}var _D9=_D7;return _D9;})]);});},function(_Da){return new F(function(){return A(_D1,[new T(function(){return B(_CP(_Da,_CW));})]);});}]);});},_Db=function(_Dc,_Dd){return function(_De,_Df,_Dg,_Dh,_Di){return new F(function(){return _CU(function(_Dj,_Dk,_Dl,_Dm,_Dn){var _Do=E(_Dc),_Dp=E(_Dj),_Dq=E(_Dp[2]);return new F(function(){return _Bu(E(_Do[1])[1],_Do[2],function(_Dr){return new F(function(){return _BT(_Dr,_Dd);});},_Dp[1],_Dq[1],_Dq[2],_Dq[3],_Dp[3],_Dk,_Dn);});},[1,[1,_zy,new T(function(){return B(_Bo([1,_Dd,_f],_zz));})],_f],_De,_Df,_Dg,_Dh,_Di);});};},_Ds=[0,10],_Dt=new T(function(){return B(unCStr("lf new-line"));}),_Du=[1,_Dt,_f],_Dv=function(_Dw){return function(_Dx,_Dy,_Dz,_DA,_DB){return new F(function(){return _CU(new T(function(){return B(_Db(_Dw,_Ds));}),_Du,_Dx,_Dy,_Dz,_DA,_DB);});};},_DC=new T(function(){return B(_Dv(_Cr));}),_DD=new T(function(){return B(unCStr("digit"));}),_DE=[1,_DD,_f],_DF=function(_DG){return new F(function(){return _Ca(_C7,_DG);});},_DH=function(_DI){var _DJ=E(_DI)[1];return _DJ<48?false:_DJ<=57;},_DK=function(_DL,_DM,_DN,_DO,_DP){var _DQ=E(_DL),_DR=E(_DQ[2]);return new F(function(){return _Bu(_zv,_DF,_DH,_DQ[1],_DR[1],_DR[2],_DR[3],_DQ[3],_DM,_DP);});},_DS=function(_DT,_DU,_DV,_DW,_DX){return new F(function(){return _CU(_DK,_DE,_DT,_DU,_DV,_DW,_DX);});},_DY=function(_DZ,_E0,_E1,_E2,_E3){return new F(function(){return _xh(_DS,_DZ,_E0,_E1,_E2,_E3);});},_E4=new T(function(){return B(_Co(_C7));}),_E5=[0,44],_E6=new T(function(){return B(_Db(_E4,_E5));}),_E7=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_E8=new T(function(){return B(err(_E7));}),_E9=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_Ea=new T(function(){return B(err(_E9));}),_Eb=new T(function(){return B(_2x("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_Ec=function(_Ed,_Ee){while(1){var _Ef=(function(_Eg,_Eh){var _Ei=E(_Eg);switch(_Ei[0]){case 0:var _Ej=E(_Eh);if(!_Ej[0]){return [0];}else{_Ed=B(A(_Ei[1],[_Ej[1]]));_Ee=_Ej[2];return null;}break;case 1:var _Ek=B(A(_Ei[1],[_Eh])),_El=_Eh;_Ed=_Ek;_Ee=_El;return null;case 2:return [0];case 3:return [1,[0,_Ei[1],_Eh],new T(function(){return B(_Ec(_Ei[2],_Eh));})];default:return E(_Ei[1]);}})(_Ed,_Ee);if(_Ef!=null){return _Ef;}}},_Em=function(_En,_Eo){var _Ep=function(_Eq){var _Er=E(_Eo);if(_Er[0]==3){return [3,_Er[1],new T(function(){return B(_Em(_En,_Er[2]));})];}else{var _Es=E(_En);if(_Es[0]==2){return E(_Er);}else{var _Et=E(_Er);if(_Et[0]==2){return E(_Es);}else{var _Eu=function(_Ev){var _Ew=E(_Et);if(_Ew[0]==4){return [1,function(_Ex){return [4,new T(function(){return B(_1F(B(_Ec(_Es,_Ex)),_Ew[1]));})];}];}else{var _Ey=E(_Es);if(_Ey[0]==1){var _Ez=_Ey[1],_EA=E(_Ew);return _EA[0]==0?[1,function(_EB){return new F(function(){return _Em(B(A(_Ez,[_EB])),_EA);});}]:[1,function(_EC){return new F(function(){return _Em(B(A(_Ez,[_EC])),new T(function(){return B(A(_EA[1],[_EC]));}));});}];}else{var _ED=E(_Ew);return _ED[0]==0?E(_Eb):[1,function(_EE){return new F(function(){return _Em(_Ey,new T(function(){return B(A(_ED[1],[_EE]));}));});}];}}},_EF=E(_Es);switch(_EF[0]){case 1:var _EG=E(_Et);if(_EG[0]==4){return [1,function(_EH){return [4,new T(function(){return B(_1F(B(_Ec(B(A(_EF[1],[_EH])),_EH)),_EG[1]));})];}];}else{return new F(function(){return _Eu(_);});}break;case 4:var _EI=_EF[1],_EJ=E(_Et);switch(_EJ[0]){case 0:return [1,function(_EK){return [4,new T(function(){return B(_1F(_EI,new T(function(){return B(_Ec(_EJ,_EK));},1)));})];}];case 1:return [1,function(_EL){return [4,new T(function(){return B(_1F(_EI,new T(function(){return B(_Ec(B(A(_EJ[1],[_EL])),_EL));},1)));})];}];default:return [4,new T(function(){return B(_1F(_EI,_EJ[1]));})];}break;default:return new F(function(){return _Eu(_);});}}}}},_EM=E(_En);switch(_EM[0]){case 0:var _EN=E(_Eo);if(!_EN[0]){return [0,function(_EO){return new F(function(){return _Em(B(A(_EM[1],[_EO])),new T(function(){return B(A(_EN[1],[_EO]));}));});}];}else{return new F(function(){return _Ep(_);});}break;case 3:return [3,_EM[1],new T(function(){return B(_Em(_EM[2],_Eo));})];default:return new F(function(){return _Ep(_);});}},_EP=[0,41],_EQ=[1,_EP,_f],_ER=[0,40],_ES=[1,_ER,_f],_ET=function(_EU,_EV){var _EW=E(_EU);switch(_EW[0]){case 0:return [0,function(_EX){return new F(function(){return _ET(B(A(_EW[1],[_EX])),_EV);});}];case 1:return [1,function(_EY){return new F(function(){return _ET(B(A(_EW[1],[_EY])),_EV);});}];case 2:return [2];case 3:return new F(function(){return _Em(B(A(_EV,[_EW[1]])),new T(function(){return B(_ET(_EW[2],_EV));}));});break;default:var _EZ=function(_F0){var _F1=E(_F0);if(!_F1[0]){return [0];}else{var _F2=E(_F1[1]);return new F(function(){return _1F(B(_Ec(B(A(_EV,[_F2[1]])),_F2[2])),new T(function(){return B(_EZ(_F1[2]));},1));});}},_F3=B(_EZ(_EW[1]));return _F3[0]==0?[2]:[4,_F3];}},_F4=[2],_F5=function(_F6){return [3,_F6,_F4];},_F7=function(_F8,_F9){var _Fa=E(_F8);if(!_Fa){return new F(function(){return A(_F9,[_0]);});}else{return [0,function(_Fb){return E(new T(function(){return B(_F7(_Fa-1|0,_F9));}));}];}},_Fc=function(_Fd,_Fe,_Ff){return function(_Fg){return new F(function(){return A(function(_Fh,_Fi,_Fj){while(1){var _Fk=(function(_Fl,_Fm,_Fn){var _Fo=E(_Fl);switch(_Fo[0]){case 0:var _Fp=E(_Fm);if(!_Fp[0]){return E(_Fe);}else{_Fh=B(A(_Fo[1],[_Fp[1]]));_Fi=_Fp[2];var _Fq=_Fn+1|0;_Fj=_Fq;return null;}break;case 1:var _Fr=B(A(_Fo[1],[_Fm])),_Fs=_Fm,_Fq=_Fn;_Fh=_Fr;_Fi=_Fs;_Fj=_Fq;return null;case 2:return E(_Fe);case 3:return function(_Ft){return new F(function(){return _F7(_Fn,function(_Fu){return E(new T(function(){return B(_ET(_Fo,_Ft));}));});});};default:return function(_m0){return new F(function(){return _ET(_Fo,_m0);});};}})(_Fh,_Fi,_Fj);if(_Fk!=null){return _Fk;}}},[new T(function(){return B(A(_Fd,[_F5]));}),_Fg,0,_Ff]);});};},_Fv=function(_Fw){return new F(function(){return A(_Fw,[_f]);});},_Fx=function(_Fy,_Fz){var _FA=function(_FB){var _FC=E(_FB);if(!_FC[0]){return E(_Fv);}else{var _FD=_FC[1];return !B(A(_Fy,[_FD]))?E(_Fv):function(_FE){return [0,function(_FF){return E(new T(function(){return B(A(new T(function(){return B(_FA(_FC[2]));}),[function(_FG){return new F(function(){return A(_FE,[[1,_FD,_FG]]);});}]));}));}];};}};return function(_FH){return new F(function(){return A(_FA,[_FH,_Fz]);});};},_FI=[6],_FJ=new T(function(){return B(unCStr("valDig: Bad base"));}),_FK=new T(function(){return B(err(_FJ));}),_FL=function(_FM,_FN){var _FO=function(_FP,_FQ){var _FR=E(_FP);if(!_FR[0]){return function(_FS){return new F(function(){return A(_FS,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{var _FT=E(_FR[1])[1],_FU=function(_FV){return function(_FW){return [0,function(_FX){return E(new T(function(){return B(A(new T(function(){return B(_FO(_FR[2],function(_FY){return new F(function(){return A(_FQ,[[1,_FV,_FY]]);});}));}),[_FW]));}));}];};};switch(E(E(_FM)[1])){case 8:if(48>_FT){return function(_FZ){return new F(function(){return A(_FZ,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{if(_FT>55){return function(_G0){return new F(function(){return A(_G0,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{return new F(function(){return _FU([0,_FT-48|0]);});}}break;case 10:if(48>_FT){return function(_G1){return new F(function(){return A(_G1,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{if(_FT>57){return function(_G2){return new F(function(){return A(_G2,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{return new F(function(){return _FU([0,_FT-48|0]);});}}break;case 16:if(48>_FT){if(97>_FT){if(65>_FT){return function(_G3){return new F(function(){return A(_G3,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{if(_FT>70){return function(_G4){return new F(function(){return A(_G4,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{return new F(function(){return _FU([0,(_FT-65|0)+10|0]);});}}}else{if(_FT>102){if(65>_FT){return function(_G5){return new F(function(){return A(_G5,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{if(_FT>70){return function(_G6){return new F(function(){return A(_G6,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{return new F(function(){return _FU([0,(_FT-65|0)+10|0]);});}}}else{return new F(function(){return _FU([0,(_FT-97|0)+10|0]);});}}}else{if(_FT>57){if(97>_FT){if(65>_FT){return function(_G7){return new F(function(){return A(_G7,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{if(_FT>70){return function(_G8){return new F(function(){return A(_G8,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{return new F(function(){return _FU([0,(_FT-65|0)+10|0]);});}}}else{if(_FT>102){if(65>_FT){return function(_G9){return new F(function(){return A(_G9,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{if(_FT>70){return function(_Ga){return new F(function(){return A(_Ga,[new T(function(){return B(A(_FQ,[_f]));})]);});};}else{return new F(function(){return _FU([0,(_FT-65|0)+10|0]);});}}}else{return new F(function(){return _FU([0,(_FT-97|0)+10|0]);});}}}else{return new F(function(){return _FU([0,_FT-48|0]);});}}break;default:return E(_FK);}}};return function(_Gb){return new F(function(){return A(_FO,[_Gb,_4s,function(_Gc){var _Gd=E(_Gc);return _Gd[0]==0?[2]:B(A(_FN,[_Gd]));}]);});};},_Ge=[0,10],_Gf=[0,1],_Gg=[0,2147483647],_Gh=function(_Gi,_Gj){while(1){var _Gk=E(_Gi);if(!_Gk[0]){var _Gl=_Gk[1],_Gm=E(_Gj);if(!_Gm[0]){var _Gn=_Gm[1],_Go=addC(_Gl,_Gn);if(!E(_Go[2])){return [0,_Go[1]];}else{_Gi=[1,I_fromInt(_Gl)];_Gj=[1,I_fromInt(_Gn)];continue;}}else{_Gi=[1,I_fromInt(_Gl)];_Gj=_Gm;continue;}}else{var _Gp=E(_Gj);if(!_Gp[0]){_Gi=_Gk;_Gj=[1,I_fromInt(_Gp[1])];continue;}else{return [1,I_add(_Gk[1],_Gp[1])];}}}},_Gq=new T(function(){return B(_Gh(_Gg,_Gf));}),_Gr=function(_Gs){var _Gt=E(_Gs);if(!_Gt[0]){var _Gu=E(_Gt[1]);return _Gu==(-2147483648)?E(_Gq):[0, -_Gu];}else{return [1,I_negate(_Gt[1])];}},_Gv=[0,10],_Gw=[0,0],_Gx=function(_Gy){return [0,_Gy];},_Gz=function(_GA,_GB){while(1){var _GC=E(_GA);if(!_GC[0]){var _GD=_GC[1],_GE=E(_GB);if(!_GE[0]){var _GF=_GE[1];if(!(imul(_GD,_GF)|0)){return [0,imul(_GD,_GF)|0];}else{_GA=[1,I_fromInt(_GD)];_GB=[1,I_fromInt(_GF)];continue;}}else{_GA=[1,I_fromInt(_GD)];_GB=_GE;continue;}}else{var _GG=E(_GB);if(!_GG[0]){_GA=_GC;_GB=[1,I_fromInt(_GG[1])];continue;}else{return [1,I_mul(_GC[1],_GG[1])];}}}},_GH=function(_GI,_GJ,_GK){while(1){var _GL=E(_GK);if(!_GL[0]){return E(_GJ);}else{var _GM=B(_Gh(B(_Gz(_GJ,_GI)),B(_Gx(E(_GL[1])[1]))));_GK=_GL[2];_GJ=_GM;continue;}}},_GN=function(_GO){var _GP=new T(function(){return B(_Em(B(_Em([0,function(_GQ){return E(E(_GQ)[1])==45?[1,B(_FL(_Ge,function(_GR){return new F(function(){return A(_GO,[[1,new T(function(){return B(_Gr(B(_GH(_Gv,_Gw,_GR))));})]]);});}))]:[2];}],[0,function(_GS){return E(E(_GS)[1])==43?[1,B(_FL(_Ge,function(_GT){return new F(function(){return A(_GO,[[1,new T(function(){return B(_GH(_Gv,_Gw,_GT));})]]);});}))]:[2];}])),new T(function(){return [1,B(_FL(_Ge,function(_GU){return new F(function(){return A(_GO,[[1,new T(function(){return B(_GH(_Gv,_Gw,_GU));})]]);});}))];})));});return new F(function(){return _Em([0,function(_GV){return E(E(_GV)[1])==101?E(_GP):[2];}],[0,function(_GW){return E(E(_GW)[1])==69?E(_GP):[2];}]);});},_GX=function(_GY){return new F(function(){return A(_GY,[_10]);});},_GZ=function(_H0){return new F(function(){return A(_H0,[_10]);});},_H1=function(_H2){return function(_H3){return E(E(_H3)[1])==46?[1,B(_FL(_Ge,function(_H4){return new F(function(){return A(_H2,[[1,_H4]]);});}))]:[2];};},_H5=function(_H6){return [0,B(_H1(_H6))];},_H7=function(_H8){return new F(function(){return _FL(_Ge,function(_H9){return [1,B(_Fc(_H5,_GX,function(_Ha){return [1,B(_Fc(_GN,_GZ,function(_Hb){return new F(function(){return A(_H8,[[5,[1,_H9,_Ha,_Hb]]]);});}))];}))];});});},_Hc=function(_Hd){return [1,B(_H7(_Hd))];},_He=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_Hf=function(_Hg){return new F(function(){return _83(_BW,_Hg,_He);});},_Hh=[0,8],_Hi=[0,16],_Hj=function(_Hk){var _Hl=function(_Hm){return new F(function(){return A(_Hk,[[5,[0,_Hh,_Hm]]]);});},_Hn=function(_Ho){return new F(function(){return A(_Hk,[[5,[0,_Hi,_Ho]]]);});};return function(_Hp){return E(E(_Hp)[1])==48?E([0,function(_Hq){switch(E(E(_Hq)[1])){case 79:return [1,B(_FL(_Hh,_Hl))];case 88:return [1,B(_FL(_Hi,_Hn))];case 111:return [1,B(_FL(_Hh,_Hl))];case 120:return [1,B(_FL(_Hi,_Hn))];default:return [2];}}]):[2];};},_Hr=function(_Hs){return [0,B(_Hj(_Hs))];},_Ht=true,_Hu=function(_Hv){var _Hw=new T(function(){return B(A(_Hv,[_Hh]));}),_Hx=new T(function(){return B(A(_Hv,[_Hi]));});return function(_Hy){switch(E(E(_Hy)[1])){case 79:return E(_Hw);case 88:return E(_Hx);case 111:return E(_Hw);case 120:return E(_Hx);default:return [2];}};},_Hz=function(_HA){return [0,B(_Hu(_HA))];},_HB=[0,92],_HC=function(_HD){return new F(function(){return A(_HD,[_Ge]);});},_HE=function(_HF){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_4f(9,_HF,_f));}))));});},_HG=function(_HH){var _HI=E(_HH);return _HI[0]==0?E(_HI[1]):I_toInt(_HI[1]);},_HJ=function(_HK,_HL){var _HM=E(_HK);if(!_HM[0]){var _HN=_HM[1],_HO=E(_HL);return _HO[0]==0?_HN<=_HO[1]:I_compareInt(_HO[1],_HN)>=0;}else{var _HP=_HM[1],_HQ=E(_HL);return _HQ[0]==0?I_compareInt(_HP,_HQ[1])<=0:I_compare(_HP,_HQ[1])<=0;}},_HR=function(_HS){return [2];},_HT=function(_HU){var _HV=E(_HU);if(!_HV[0]){return E(_HR);}else{var _HW=_HV[1],_HX=E(_HV[2]);return _HX[0]==0?E(_HW):function(_HY){return new F(function(){return _Em(B(A(_HW,[_HY])),new T(function(){return B(A(new T(function(){return B(_HT(_HX));}),[_HY]));}));});};}},_HZ=function(_I0){return [2];},_I1=function(_I2,_I3){var _I4=function(_I5,_I6){var _I7=E(_I5);if(!_I7[0]){return function(_I8){return new F(function(){return A(_I8,[_I2]);});};}else{var _I9=E(_I6);return _I9[0]==0?E(_HZ):E(_I7[1])[1]!=E(_I9[1])[1]?E(_HZ):function(_Ia){return [0,function(_Ib){return E(new T(function(){return B(A(new T(function(){return B(_I4(_I7[2],_I9[2]));}),[_Ia]));}));}];};}};return function(_Ic){return new F(function(){return A(_I4,[_I2,_Ic,_I3]);});};},_Id=new T(function(){return B(unCStr("SOH"));}),_Ie=[0,1],_If=function(_Ig){return [1,B(_I1(_Id,function(_Ih){return E(new T(function(){return B(A(_Ig,[_Ie]));}));}))];},_Ii=new T(function(){return B(unCStr("SO"));}),_Ij=[0,14],_Ik=function(_Il){return [1,B(_I1(_Ii,function(_Im){return E(new T(function(){return B(A(_Il,[_Ij]));}));}))];},_In=function(_Io){return [1,B(_Fc(_If,_Ik,_Io))];},_Ip=new T(function(){return B(unCStr("NUL"));}),_Iq=[0,0],_Ir=function(_Is){return [1,B(_I1(_Ip,function(_It){return E(new T(function(){return B(A(_Is,[_Iq]));}));}))];},_Iu=new T(function(){return B(unCStr("STX"));}),_Iv=[0,2],_Iw=function(_Ix){return [1,B(_I1(_Iu,function(_Iy){return E(new T(function(){return B(A(_Ix,[_Iv]));}));}))];},_Iz=new T(function(){return B(unCStr("ETX"));}),_IA=[0,3],_IB=function(_IC){return [1,B(_I1(_Iz,function(_ID){return E(new T(function(){return B(A(_IC,[_IA]));}));}))];},_IE=new T(function(){return B(unCStr("EOT"));}),_IF=[0,4],_IG=function(_IH){return [1,B(_I1(_IE,function(_II){return E(new T(function(){return B(A(_IH,[_IF]));}));}))];},_IJ=new T(function(){return B(unCStr("ENQ"));}),_IK=[0,5],_IL=function(_IM){return [1,B(_I1(_IJ,function(_IN){return E(new T(function(){return B(A(_IM,[_IK]));}));}))];},_IO=new T(function(){return B(unCStr("ACK"));}),_IP=[0,6],_IQ=function(_IR){return [1,B(_I1(_IO,function(_IS){return E(new T(function(){return B(A(_IR,[_IP]));}));}))];},_IT=new T(function(){return B(unCStr("BEL"));}),_IU=[0,7],_IV=function(_IW){return [1,B(_I1(_IT,function(_IX){return E(new T(function(){return B(A(_IW,[_IU]));}));}))];},_IY=new T(function(){return B(unCStr("BS"));}),_IZ=[0,8],_J0=function(_J1){return [1,B(_I1(_IY,function(_J2){return E(new T(function(){return B(A(_J1,[_IZ]));}));}))];},_J3=new T(function(){return B(unCStr("HT"));}),_J4=[0,9],_J5=function(_J6){return [1,B(_I1(_J3,function(_J7){return E(new T(function(){return B(A(_J6,[_J4]));}));}))];},_J8=new T(function(){return B(unCStr("LF"));}),_J9=[0,10],_Ja=function(_Jb){return [1,B(_I1(_J8,function(_Jc){return E(new T(function(){return B(A(_Jb,[_J9]));}));}))];},_Jd=new T(function(){return B(unCStr("VT"));}),_Je=[0,11],_Jf=function(_Jg){return [1,B(_I1(_Jd,function(_Jh){return E(new T(function(){return B(A(_Jg,[_Je]));}));}))];},_Ji=new T(function(){return B(unCStr("FF"));}),_Jj=[0,12],_Jk=function(_Jl){return [1,B(_I1(_Ji,function(_Jm){return E(new T(function(){return B(A(_Jl,[_Jj]));}));}))];},_Jn=new T(function(){return B(unCStr("CR"));}),_Jo=[0,13],_Jp=function(_Jq){return [1,B(_I1(_Jn,function(_Jr){return E(new T(function(){return B(A(_Jq,[_Jo]));}));}))];},_Js=new T(function(){return B(unCStr("SI"));}),_Jt=[0,15],_Ju=function(_Jv){return [1,B(_I1(_Js,function(_Jw){return E(new T(function(){return B(A(_Jv,[_Jt]));}));}))];},_Jx=new T(function(){return B(unCStr("DLE"));}),_Jy=[0,16],_Jz=function(_JA){return [1,B(_I1(_Jx,function(_JB){return E(new T(function(){return B(A(_JA,[_Jy]));}));}))];},_JC=new T(function(){return B(unCStr("DC1"));}),_JD=[0,17],_JE=function(_JF){return [1,B(_I1(_JC,function(_JG){return E(new T(function(){return B(A(_JF,[_JD]));}));}))];},_JH=new T(function(){return B(unCStr("DC2"));}),_JI=[0,18],_JJ=function(_JK){return [1,B(_I1(_JH,function(_JL){return E(new T(function(){return B(A(_JK,[_JI]));}));}))];},_JM=new T(function(){return B(unCStr("DC3"));}),_JN=[0,19],_JO=function(_JP){return [1,B(_I1(_JM,function(_JQ){return E(new T(function(){return B(A(_JP,[_JN]));}));}))];},_JR=new T(function(){return B(unCStr("DC4"));}),_JS=[0,20],_JT=function(_JU){return [1,B(_I1(_JR,function(_JV){return E(new T(function(){return B(A(_JU,[_JS]));}));}))];},_JW=new T(function(){return B(unCStr("NAK"));}),_JX=[0,21],_JY=function(_JZ){return [1,B(_I1(_JW,function(_K0){return E(new T(function(){return B(A(_JZ,[_JX]));}));}))];},_K1=new T(function(){return B(unCStr("SYN"));}),_K2=[0,22],_K3=function(_K4){return [1,B(_I1(_K1,function(_K5){return E(new T(function(){return B(A(_K4,[_K2]));}));}))];},_K6=new T(function(){return B(unCStr("ETB"));}),_K7=[0,23],_K8=function(_K9){return [1,B(_I1(_K6,function(_Ka){return E(new T(function(){return B(A(_K9,[_K7]));}));}))];},_Kb=new T(function(){return B(unCStr("CAN"));}),_Kc=[0,24],_Kd=function(_Ke){return [1,B(_I1(_Kb,function(_Kf){return E(new T(function(){return B(A(_Ke,[_Kc]));}));}))];},_Kg=new T(function(){return B(unCStr("EM"));}),_Kh=[0,25],_Ki=function(_Kj){return [1,B(_I1(_Kg,function(_Kk){return E(new T(function(){return B(A(_Kj,[_Kh]));}));}))];},_Kl=new T(function(){return B(unCStr("SUB"));}),_Km=[0,26],_Kn=function(_Ko){return [1,B(_I1(_Kl,function(_Kp){return E(new T(function(){return B(A(_Ko,[_Km]));}));}))];},_Kq=new T(function(){return B(unCStr("ESC"));}),_Kr=[0,27],_Ks=function(_Kt){return [1,B(_I1(_Kq,function(_Ku){return E(new T(function(){return B(A(_Kt,[_Kr]));}));}))];},_Kv=new T(function(){return B(unCStr("FS"));}),_Kw=[0,28],_Kx=function(_Ky){return [1,B(_I1(_Kv,function(_Kz){return E(new T(function(){return B(A(_Ky,[_Kw]));}));}))];},_KA=new T(function(){return B(unCStr("GS"));}),_KB=[0,29],_KC=function(_KD){return [1,B(_I1(_KA,function(_KE){return E(new T(function(){return B(A(_KD,[_KB]));}));}))];},_KF=new T(function(){return B(unCStr("RS"));}),_KG=[0,30],_KH=function(_KI){return [1,B(_I1(_KF,function(_KJ){return E(new T(function(){return B(A(_KI,[_KG]));}));}))];},_KK=new T(function(){return B(unCStr("US"));}),_KL=[0,31],_KM=function(_KN){return [1,B(_I1(_KK,function(_KO){return E(new T(function(){return B(A(_KN,[_KL]));}));}))];},_KP=new T(function(){return B(unCStr("SP"));}),_KQ=[0,32],_KR=function(_KS){return [1,B(_I1(_KP,function(_KT){return E(new T(function(){return B(A(_KS,[_KQ]));}));}))];},_KU=new T(function(){return B(unCStr("DEL"));}),_KV=[0,127],_KW=function(_KX){return [1,B(_I1(_KU,function(_KY){return E(new T(function(){return B(A(_KX,[_KV]));}));}))];},_KZ=[1,_KW,_f],_L0=[1,_KR,_KZ],_L1=[1,_KM,_L0],_L2=[1,_KH,_L1],_L3=[1,_KC,_L2],_L4=[1,_Kx,_L3],_L5=[1,_Ks,_L4],_L6=[1,_Kn,_L5],_L7=[1,_Ki,_L6],_L8=[1,_Kd,_L7],_L9=[1,_K8,_L8],_La=[1,_K3,_L9],_Lb=[1,_JY,_La],_Lc=[1,_JT,_Lb],_Ld=[1,_JO,_Lc],_Le=[1,_JJ,_Ld],_Lf=[1,_JE,_Le],_Lg=[1,_Jz,_Lf],_Lh=[1,_Ju,_Lg],_Li=[1,_Jp,_Lh],_Lj=[1,_Jk,_Li],_Lk=[1,_Jf,_Lj],_Ll=[1,_Ja,_Lk],_Lm=[1,_J5,_Ll],_Ln=[1,_J0,_Lm],_Lo=[1,_IV,_Ln],_Lp=[1,_IQ,_Lo],_Lq=[1,_IL,_Lp],_Lr=[1,_IG,_Lq],_Ls=[1,_IB,_Lr],_Lt=[1,_Iw,_Ls],_Lu=[1,_Ir,_Lt],_Lv=[1,_In,_Lu],_Lw=new T(function(){return B(_HT(_Lv));}),_Lx=[0,1114111],_Ly=[0,34],_Lz=[0,39],_LA=function(_LB){var _LC=new T(function(){return B(A(_LB,[_IU]));}),_LD=new T(function(){return B(A(_LB,[_IZ]));}),_LE=new T(function(){return B(A(_LB,[_J4]));}),_LF=new T(function(){return B(A(_LB,[_J9]));}),_LG=new T(function(){return B(A(_LB,[_Je]));}),_LH=new T(function(){return B(A(_LB,[_Jj]));}),_LI=new T(function(){return B(A(_LB,[_Jo]));});return new F(function(){return _Em([0,function(_LJ){switch(E(E(_LJ)[1])){case 34:return E(new T(function(){return B(A(_LB,[_Ly]));}));case 39:return E(new T(function(){return B(A(_LB,[_Lz]));}));case 92:return E(new T(function(){return B(A(_LB,[_HB]));}));case 97:return E(_LC);case 98:return E(_LD);case 102:return E(_LH);case 110:return E(_LF);case 114:return E(_LI);case 116:return E(_LE);case 118:return E(_LG);default:return [2];}}],new T(function(){return B(_Em([1,B(_Fc(_Hz,_HC,function(_LK){return [1,B(_FL(_LK,function(_LL){var _LM=B(_GH(new T(function(){return B(_Gx(E(_LK)[1]));}),_Gw,_LL));return !B(_HJ(_LM,_Lx))?[2]:B(A(_LB,[new T(function(){var _LN=B(_HG(_LM));if(_LN>>>0>1114111){var _LO=B(_HE(_LN));}else{var _LO=[0,_LN];}var _LP=_LO,_LQ=_LP,_LR=_LQ;return _LR;})]));}))];}))],new T(function(){return B(_Em([0,function(_LS){return E(E(_LS)[1])==94?E([0,function(_LT){switch(E(E(_LT)[1])){case 64:return E(new T(function(){return B(A(_LB,[_Iq]));}));case 65:return E(new T(function(){return B(A(_LB,[_Ie]));}));case 66:return E(new T(function(){return B(A(_LB,[_Iv]));}));case 67:return E(new T(function(){return B(A(_LB,[_IA]));}));case 68:return E(new T(function(){return B(A(_LB,[_IF]));}));case 69:return E(new T(function(){return B(A(_LB,[_IK]));}));case 70:return E(new T(function(){return B(A(_LB,[_IP]));}));case 71:return E(_LC);case 72:return E(_LD);case 73:return E(_LE);case 74:return E(_LF);case 75:return E(_LG);case 76:return E(_LH);case 77:return E(_LI);case 78:return E(new T(function(){return B(A(_LB,[_Ij]));}));case 79:return E(new T(function(){return B(A(_LB,[_Jt]));}));case 80:return E(new T(function(){return B(A(_LB,[_Jy]));}));case 81:return E(new T(function(){return B(A(_LB,[_JD]));}));case 82:return E(new T(function(){return B(A(_LB,[_JI]));}));case 83:return E(new T(function(){return B(A(_LB,[_JN]));}));case 84:return E(new T(function(){return B(A(_LB,[_JS]));}));case 85:return E(new T(function(){return B(A(_LB,[_JX]));}));case 86:return E(new T(function(){return B(A(_LB,[_K2]));}));case 87:return E(new T(function(){return B(A(_LB,[_K7]));}));case 88:return E(new T(function(){return B(A(_LB,[_Kc]));}));case 89:return E(new T(function(){return B(A(_LB,[_Kh]));}));case 90:return E(new T(function(){return B(A(_LB,[_Km]));}));case 91:return E(new T(function(){return B(A(_LB,[_Kr]));}));case 92:return E(new T(function(){return B(A(_LB,[_Kw]));}));case 93:return E(new T(function(){return B(A(_LB,[_KB]));}));case 94:return E(new T(function(){return B(A(_LB,[_KG]));}));case 95:return E(new T(function(){return B(A(_LB,[_KL]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_Lw,[_LB]));})));})));}));});},_LU=function(_LV){return new F(function(){return A(_LV,[_0]);});},_LW=function(_LX){var _LY=E(_LX);if(!_LY[0]){return E(_LU);}else{var _LZ=_LY[2],_M0=E(E(_LY[1])[1]);switch(_M0){case 9:return function(_M1){return [0,function(_M2){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_M1]));}));}];};case 10:return function(_M3){return [0,function(_M4){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_M3]));}));}];};case 11:return function(_M5){return [0,function(_M6){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_M5]));}));}];};case 12:return function(_M7){return [0,function(_M8){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_M7]));}));}];};case 13:return function(_M9){return [0,function(_Ma){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_M9]));}));}];};case 32:return function(_Mb){return [0,function(_Mc){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_Mb]));}));}];};case 160:return function(_Md){return [0,function(_Me){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_Md]));}));}];};default:var _Mf=u_iswspace(_M0),_Mg=_Mf;return E(_Mg)==0?E(_LU):function(_Mh){return [0,function(_Mi){return E(new T(function(){return B(A(new T(function(){return B(_LW(_LZ));}),[_Mh]));}));}];};}}},_Mj=function(_Mk){var _Ml=new T(function(){return B(_Mj(_Mk));}),_Mm=[1,function(_Mn){return new F(function(){return A(_LW,[_Mn,function(_Mo){return E([0,function(_Mp){return E(E(_Mp)[1])==92?E(_Ml):[2];}]);}]);});}];return new F(function(){return _Em([0,function(_Mq){return E(E(_Mq)[1])==92?E([0,function(_Mr){var _Ms=E(E(_Mr)[1]);switch(_Ms){case 9:return E(_Mm);case 10:return E(_Mm);case 11:return E(_Mm);case 12:return E(_Mm);case 13:return E(_Mm);case 32:return E(_Mm);case 38:return E(_Ml);case 160:return E(_Mm);default:var _Mt=u_iswspace(_Ms),_Mu=_Mt;return E(_Mu)==0?[2]:E(_Mm);}}]):[2];}],[0,function(_Mv){var _Mw=E(_Mv);return E(_Mw[1])==92?E(new T(function(){return B(_LA(function(_Mx){return new F(function(){return A(_Mk,[[0,_Mx,_Ht]]);});}));})):B(A(_Mk,[[0,_Mw,_K]]));}]);});},_My=function(_Mz,_MA){return new F(function(){return _Mj(function(_MB){var _MC=E(_MB),_MD=E(_MC[1]);if(E(_MD[1])==34){if(!E(_MC[2])){return E(new T(function(){return B(A(_MA,[[1,new T(function(){return B(A(_Mz,[_f]));})]]));}));}else{return new F(function(){return _My(function(_ME){return new F(function(){return A(_Mz,[[1,_MD,_ME]]);});},_MA);});}}else{return new F(function(){return _My(function(_MF){return new F(function(){return A(_Mz,[[1,_MD,_MF]]);});},_MA);});}});});},_MG=new T(function(){return B(unCStr("_\'"));}),_MH=function(_MI){var _MJ=u_iswalnum(_MI),_MK=_MJ;return E(_MK)==0?B(_83(_BW,[0,_MI],_MG)):true;},_ML=function(_MM){return new F(function(){return _MH(E(_MM)[1]);});},_MN=new T(function(){return B(unCStr(",;()[]{}`"));}),_MO=new T(function(){return B(unCStr(".."));}),_MP=new T(function(){return B(unCStr("::"));}),_MQ=new T(function(){return B(unCStr("->"));}),_MR=[0,64],_MS=[1,_MR,_f],_MT=[0,126],_MU=[1,_MT,_f],_MV=new T(function(){return B(unCStr("=>"));}),_MW=[1,_MV,_f],_MX=[1,_MU,_MW],_MY=[1,_MS,_MX],_MZ=[1,_MQ,_MY],_N0=new T(function(){return B(unCStr("<-"));}),_N1=[1,_N0,_MZ],_N2=[0,124],_N3=[1,_N2,_f],_N4=[1,_N3,_N1],_N5=[1,_HB,_f],_N6=[1,_N5,_N4],_N7=[0,61],_N8=[1,_N7,_f],_N9=[1,_N8,_N6],_Na=[1,_MP,_N9],_Nb=[1,_MO,_Na],_Nc=function(_Nd){return new F(function(){return _Em([1,function(_Ne){return E(_Ne)[0]==0?E(new T(function(){return B(A(_Nd,[_FI]));})):[2];}],new T(function(){return B(_Em([0,function(_Nf){return E(E(_Nf)[1])==39?E([0,function(_Ng){var _Nh=E(_Ng);switch(E(_Nh[1])){case 39:return [2];case 92:return E(new T(function(){return B(_LA(function(_Ni){return [0,function(_Nj){return E(E(_Nj)[1])==39?E(new T(function(){return B(A(_Nd,[[0,_Ni]]));})):[2];}];}));}));default:return [0,function(_Nk){return E(E(_Nk)[1])==39?E(new T(function(){return B(A(_Nd,[[0,_Nh]]));})):[2];}];}}]):[2];}],new T(function(){return B(_Em([0,function(_Nl){return E(E(_Nl)[1])==34?E(new T(function(){return B(_My(_4s,_Nd));})):[2];}],new T(function(){return B(_Em([0,function(_Nm){return !B(_83(_BW,_Nm,_MN))?[2]:B(A(_Nd,[[2,[1,_Nm,_f]]]));}],new T(function(){return B(_Em([0,function(_Nn){return !B(_83(_BW,_Nn,_He))?[2]:[1,B(_Fx(_Hf,function(_No){var _Np=[1,_Nn,_No];return !B(_83(_7f,_Np,_Nb))?B(A(_Nd,[[4,_Np]])):B(A(_Nd,[[2,_Np]]));}))];}],new T(function(){return B(_Em([0,function(_Nq){var _Nr=E(_Nq),_Ns=_Nr[1],_Nt=u_iswalpha(_Ns),_Nu=_Nt;return E(_Nu)==0?E(_Ns)==95?[1,B(_Fx(_ML,function(_Nv){return new F(function(){return A(_Nd,[[3,[1,_Nr,_Nv]]]);});}))]:[2]:[1,B(_Fx(_ML,function(_Nw){return new F(function(){return A(_Nd,[[3,[1,_Nr,_Nw]]]);});}))];}],new T(function(){return [1,B(_Fc(_Hr,_Hc,_Nd))];})));})));})));})));})));}));});},_Nx=[0,0],_Ny=function(_Nz,_NA){return function(_NB){return new F(function(){return A(_LW,[_NB,function(_NC){return E(new T(function(){return B(_Nc(function(_ND){var _NE=E(_ND);return _NE[0]==2?!B(_bw(_NE[1],_ES))?[2]:E(new T(function(){return B(A(_Nz,[_Nx,function(_NF){return [1,function(_NG){return new F(function(){return A(_LW,[_NG,function(_NH){return E(new T(function(){return B(_Nc(function(_NI){var _NJ=E(_NI);return _NJ[0]==2?!B(_bw(_NJ[1],_EQ))?[2]:E(new T(function(){return B(A(_NA,[_NF]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_NK=function(_NL,_NM,_NN){var _NO=function(_NP,_NQ){return new F(function(){return _Em([1,function(_NR){return new F(function(){return A(_LW,[_NR,function(_NS){return E(new T(function(){return B(_Nc(function(_NT){var _NU=E(_NT);if(_NU[0]==4){var _NV=E(_NU[1]);if(!_NV[0]){return new F(function(){return A(_NL,[_NU,_NP,_NQ]);});}else{return E(E(_NV[1])[1])==45?E(_NV[2])[0]==0?E([1,function(_NW){return new F(function(){return A(_LW,[_NW,function(_NX){return E(new T(function(){return B(_Nc(function(_NY){return new F(function(){return A(_NL,[_NY,_NP,function(_NZ){return new F(function(){return A(_NQ,[new T(function(){return [0, -E(_NZ)[1]];})]);});}]);});}));}));}]);});}]):B(A(_NL,[_NU,_NP,_NQ])):B(A(_NL,[_NU,_NP,_NQ]));}}else{return new F(function(){return A(_NL,[_NU,_NP,_NQ]);});}}));}));}]);});}],new T(function(){return [1,B(_Ny(_NO,_NQ))];}));});};return new F(function(){return _NO(_NM,_NN);});},_O0=function(_O1,_O2){return [2];},_O3=function(_O4){var _O5=E(_O4);return _O5[0]==0?[1,new T(function(){return B(_GH(new T(function(){return B(_Gx(E(_O5[1])[1]));}),_Gw,_O5[2]));})]:E(_O5[2])[0]==0?E(_O5[3])[0]==0?[1,new T(function(){return B(_GH(_Gv,_Gw,_O5[1]));})]:[0]:[0];},_O6=function(_O7){var _O8=E(_O7);if(_O8[0]==5){var _O9=B(_O3(_O8[1]));return _O9[0]==0?E(_O0):function(_Oa,_Ob){return new F(function(){return A(_Ob,[new T(function(){return [0,B(_HG(_O9[1]))];})]);});};}else{return E(_O0);}},_Oc=function(_Od){return [1,function(_Oe){return new F(function(){return A(_LW,[_Oe,function(_Of){return E([3,_Od,_F4]);}]);});}];},_Og=new T(function(){return B(_NK(_O6,_Nx,_Oc));}),_Oh=function(_Oi){while(1){var _Oj=(function(_Ok){var _Ol=E(_Ok);if(!_Ol[0]){return [0];}else{var _Om=_Ol[2],_On=E(_Ol[1]);if(!E(_On[2])[0]){return [1,_On[1],new T(function(){return B(_Oh(_Om));})];}else{_Oi=_Om;return null;}}})(_Oi);if(_Oj!=null){return _Oj;}}},_Oo=function(_Op){var _Oq=B(_Oh(B(_Ec(_Og,_Op))));return _Oq[0]==0?E(_E8):E(_Oq[2])[0]==0?E(_Oq[1]):E(_Ea);},_Or=function(_Os,_Ot,_Ou,_Ov,_Ow,_Ox){var _Oy=function(_Oz){var _OA=[0,_Os,new T(function(){return B(_7U(_Oo,_Oz));})];return function(_OB,_OC,_OD,_OE,_OF){return new F(function(){return A(_DC,[_OB,function(_OG,_OH,_OI){return new F(function(){return A(_OC,[_OA,_OH,new T(function(){var _OJ=E(E(_OH)[2]),_OK=E(_OI),_OL=E(_OK[1]),_OM=B(_wk(_OL[1],_OL[2],_OL[3],_OK[2],_OJ[1],_OJ[2],_OJ[3],_f));return [0,E(_OM[1]),_OM[2]];})]);});},_OF,function(_ON,_OO,_OP){return new F(function(){return A(_OE,[_OA,_OO,new T(function(){var _OQ=E(E(_OO)[2]),_OR=E(_OP),_OS=E(_OR[1]),_OT=B(_wk(_OS[1],_OS[2],_OS[3],_OR[2],_OQ[1],_OQ[2],_OQ[3],_f));return [0,E(_OT[1]),_OT[2]];})]);});},_OF]);});};},_OU=function(_OV,_OW,_OX,_OY,_OZ){var _P0=function(_P1,_P2,_P3){return new F(function(){return A(_Oy,[_P1,_P2,_OW,_OX,function(_P4,_P5,_P6){return new F(function(){return A(_OY,[_P4,_P5,new T(function(){return B(_x9(_P3,_P6));})]);});},function(_P7){return new F(function(){return A(_OZ,[new T(function(){return B(_x9(_P3,_P7));})]);});}]);});},_P8=function(_P9){return new F(function(){return _P0(_f,_OV,new T(function(){var _Pa=E(E(_OV)[2]),_Pb=E(_P9),_Pc=E(_Pb[1]),_Pd=B(_wk(_Pc[1],_Pc[2],_Pc[3],_Pb[2],_Pa[1],_Pa[2],_Pa[3],_f));return [0,E(_Pd[1]),_Pd[2]];}));});};return new F(function(){return _yk(_DY,_E6,_OV,function(_Pe,_Pf,_Pg){return new F(function(){return A(_Oy,[_Pe,_Pf,_OW,_OX,function(_Ph,_Pi,_Pj){return new F(function(){return A(_OW,[_Ph,_Pi,new T(function(){return B(_x9(_Pg,_Pj));})]);});},function(_Pk){return new F(function(){return A(_OX,[new T(function(){return B(_x9(_Pg,_Pk));})]);});}]);});},_P8,_P0,_P8);});};return new F(function(){return _xU(_Cg,_Ot,function(_Pl,_Pm,_Pn){return new F(function(){return _OU(_Pm,_Ou,_Ov,function(_Po,_Pp,_Pq){return new F(function(){return A(_Ou,[_Po,_Pp,new T(function(){return B(_x9(_Pn,_Pq));})]);});},function(_Pr){return new F(function(){return A(_Ov,[new T(function(){return B(_x9(_Pn,_Pr));})]);});});});},_Ov,function(_Ps,_Pt,_Pu){return new F(function(){return _OU(_Pt,_Ou,_Ov,function(_Pv,_Pw,_Px){return new F(function(){return A(_Ow,[_Pv,_Pw,new T(function(){return B(_x9(_Pu,_Px));})]);});},function(_Py){return new F(function(){return A(_Ox,[new T(function(){return B(_x9(_Pu,_Py));})]);});});});});});},_Pz=new T(function(){return B(unCStr("letter or digit"));}),_PA=[1,_Pz,_f],_PB=function(_PC){var _PD=u_iswalnum(E(_PC)[1]),_PE=_PD;return E(_PE)==0?false:true;},_PF=function(_PG,_PH,_PI,_PJ,_PK){var _PL=E(_PG),_PM=E(_PL[2]);return new F(function(){return _Bu(_zv,_DF,_PB,_PL[1],_PM[1],_PM[2],_PM[3],_PL[3],_PH,_PK);});},_PN=function(_PO,_PP,_PQ,_PR,_PS){return new F(function(){return _CU(_PF,_PA,_PO,_PP,_PQ,_PR,_PS);});},_PT=function(_PU,_PV,_PW,_PX,_PY){return new F(function(){return _xh(_PN,_PU,function(_PZ,_Q0,_Q1){return new F(function(){return _Or(_PZ,_Q0,_PV,_PW,function(_Q2,_Q3,_Q4){return new F(function(){return A(_PV,[_Q2,_Q3,new T(function(){return B(_x9(_Q1,_Q4));})]);});},function(_Q5){return new F(function(){return A(_PW,[new T(function(){return B(_x9(_Q1,_Q5));})]);});});});},_PY,function(_Q6,_Q7,_Q8){return new F(function(){return _Or(_Q6,_Q7,_PV,_PW,function(_Q9,_Qa,_Qb){return new F(function(){return A(_PX,[_Q9,_Qa,new T(function(){return B(_x9(_Q8,_Qb));})]);});},function(_Qc){return new F(function(){return A(_PY,[new T(function(){return B(_x9(_Q8,_Qc));})]);});});});},_PY);});},_Qd=new T(function(){return B(unCStr("SHOW"));}),_Qe=[0,_Qd,_f],_Qf=function(_Qg,_Qh,_Qi,_Qj){var _Qk=function(_Ql){return new F(function(){return A(_Qj,[[0,_Qg,_Qe],_Qh,new T(function(){var _Qm=E(E(_Qh)[2]),_Qn=_Qm[1],_Qo=_Qm[2],_Qp=_Qm[3],_Qq=E(_Ql),_Qr=E(_Qq[1]),_Qs=B(_wk(_Qr[1],_Qr[2],_Qr[3],_Qq[2],_Qn,_Qo,_Qp,_f)),_Qt=E(_Qs[1]),_Qu=B(_wk(_Qt[1],_Qt[2],_Qt[3],_Qs[2],_Qn,_Qo,_Qp,_f));return [0,E(_Qu[1]),_Qu[2]];})]);});};return new F(function(){return _PT(_Qh,function(_Qv,_Qw,_Qx){return new F(function(){return A(_Qi,[[0,_Qg,_Qv],_Qw,new T(function(){var _Qy=E(E(_Qw)[2]),_Qz=E(_Qx),_QA=E(_Qz[1]),_QB=B(_wk(_QA[1],_QA[2],_QA[3],_Qz[2],_Qy[1],_Qy[2],_Qy[3],_f));return [0,E(_QB[1]),_QB[2]];})]);});},_Qk,function(_QC,_QD,_QE){return new F(function(){return A(_Qj,[[0,_Qg,_QC],_QD,new T(function(){var _QF=E(E(_QD)[2]),_QG=E(_QE),_QH=E(_QG[1]),_QI=B(_wk(_QH[1],_QH[2],_QH[3],_QG[2],_QF[1],_QF[2],_QF[3],_f));return [0,E(_QI[1]),_QI[2]];})]);});},_Qk);});},_QJ=new T(function(){return B(unCStr("sS"));}),_QK=[0,58],_QL=new T(function(){return B(_Db(_Cr,_QK));}),_QM=[1,_Pz,_f],_QN=function(_QO,_QP,_QQ,_QR,_QS,_QT,_QU,_QV,_QW){var _QX=function(_QY,_QZ){var _R0=new T(function(){var _R1=B(_Cz(_QY,_QZ,_QM));return [0,E(_R1[1]),_R1[2]];});return new F(function(){return A(_QL,[[0,_QO,E([0,_QP,_QQ,_QR]),E(_QS)],_QT,_QU,function(_R2,_R3,_R4){return new F(function(){return A(_QV,[_R2,_R3,new T(function(){return B(_x9(_R0,_R4));})]);});},function(_R5){return new F(function(){return A(_QW,[new T(function(){return B(_x9(_R0,_R5));})]);});}]);});},_R6=E(_QO);if(!_R6[0]){return new F(function(){return _QX([0,_QP,_QQ,_QR],_zB);});}else{var _R7=_R6[2],_R8=E(_R6[1]),_R9=_R8[1],_Ra=u_iswalnum(_R9),_Rb=_Ra;if(!E(_Rb)){return new F(function(){return _QX([0,_QP,_QQ,_QR],[1,[0,E([1,_zy,new T(function(){return B(_Bo([1,_R8,_f],_zz));})])],_f]);});}else{switch(E(_R9)){case 9:var _Rc=[0,_QP,_QQ,(_QR+8|0)-B(_zC(_QR-1|0,8))|0];break;case 10:var _Rc=[0,_QP,_QQ+1|0,1];break;default:var _Rc=[0,_QP,_QQ,_QR+1|0];}var _Rd=_Rc,_Re=[0,E(_Rd),_f],_Rf=[0,_R7,E(_Rd),E(_QS)];return new F(function(){return A(_QT,[_R8,_Rf,_Re]);});}}},_Rg=function(_Rh,_Ri,_Rj,_Rk,_Rl){var _Rm=E(_Rh),_Rn=E(_Rm[2]);return new F(function(){return _QN(_Rm[1],_Rn[1],_Rn[2],_Rn[3],_Rm[3],_Ri,_Rj,_Rk,_Rl);});},_Ro=function(_Rp,_Rq,_Rr,_Rs,_Rt,_Ru,_Rv){var _Rw=function(_Rx,_Ry,_Rz,_RA,_RB,_RC){return new F(function(){return _RD(_Ry,function(_RE,_RF,_RG){return new F(function(){return A(_Rz,[[1,_Rx,_RE],_RF,new T(function(){var _RH=E(E(_RF)[2]),_RI=E(_RG),_RJ=E(_RI[1]),_RK=B(_wk(_RJ[1],_RJ[2],_RJ[3],_RI[2],_RH[1],_RH[2],_RH[3],_f));return [0,E(_RK[1]),_RK[2]];})]);});},_RA,function(_RL,_RM,_RN){return new F(function(){return A(_RB,[[1,_Rx,_RL],_RM,new T(function(){var _RO=E(E(_RM)[2]),_RP=E(_RN),_RQ=E(_RP[1]),_RR=B(_wk(_RQ[1],_RQ[2],_RQ[3],_RP[2],_RO[1],_RO[2],_RO[3],_f));return [0,E(_RR[1]),_RR[2]];})]);});},_RC);});},_RD=function(_RS,_RT,_RU,_RV,_RW){return new F(function(){return A(_Rq,[_RS,function(_RX,_RY,_RZ){return new F(function(){return A(_RT,[_f,_RY,new T(function(){var _S0=E(E(_RY)[2]),_S1=E(_RZ),_S2=E(_S1[1]),_S3=B(_wk(_S2[1],_S2[2],_S2[3],_S1[2],_S0[1],_S0[2],_S0[3],_f));return [0,E(_S3[1]),_S3[2]];})]);});},_RU,function(_S4,_S5,_S6){return new F(function(){return A(_RV,[_f,_S5,new T(function(){var _S7=E(E(_S5)[2]),_S8=E(_S6),_S9=E(_S8[1]),_Sa=B(_wk(_S9[1],_S9[2],_S9[3],_S8[2],_S7[1],_S7[2],_S7[3],_f));return [0,E(_Sa[1]),_Sa[2]];})]);});},function(_Sb){return new F(function(){return A(_Rp,[_RS,function(_Sc,_Sd,_Se){return new F(function(){return _Rw(_Sc,_Sd,_RT,_RU,function(_Sf,_Sg,_Sh){return new F(function(){return A(_RT,[_Sf,_Sg,new T(function(){return B(_x9(_Se,_Sh));})]);});},function(_Si){return new F(function(){return A(_RU,[new T(function(){return B(_x9(_Se,_Si));})]);});});});},_RU,function(_Sj,_Sk,_Sl){return new F(function(){return _Rw(_Sj,_Sk,_RT,_RU,function(_Sm,_Sn,_So){return new F(function(){return A(_RV,[_Sm,_Sn,new T(function(){var _Sp=E(_Sb),_Sq=E(_Sp[1]),_Sr=E(_Sl),_Ss=E(_Sr[1]),_St=E(_So),_Su=E(_St[1]),_Sv=B(_wk(_Ss[1],_Ss[2],_Ss[3],_Sr[2],_Su[1],_Su[2],_Su[3],_St[2])),_Sw=E(_Sv[1]),_Sx=B(_wk(_Sq[1],_Sq[2],_Sq[3],_Sp[2],_Sw[1],_Sw[2],_Sw[3],_Sv[2]));return [0,E(_Sx[1]),_Sx[2]];})]);});},function(_Sy){return new F(function(){return A(_RW,[new T(function(){var _Sz=E(_Sb),_SA=E(_Sz[1]),_SB=E(_Sl),_SC=E(_SB[1]),_SD=E(_Sy),_SE=E(_SD[1]),_SF=B(_wk(_SC[1],_SC[2],_SC[3],_SB[2],_SE[1],_SE[2],_SE[3],_SD[2])),_SG=E(_SF[1]),_SH=B(_wk(_SA[1],_SA[2],_SA[3],_Sz[2],_SG[1],_SG[2],_SG[3],_SF[2]));return [0,E(_SH[1]),_SH[2]];})]);});});});},function(_SI){return new F(function(){return A(_RW,[new T(function(){return B(_x9(_Sb,_SI));})]);});}]);});}]);});};return new F(function(){return _RD(_Rr,_Rs,_Rt,_Ru,_Rv);});},_SJ=new T(function(){return B(unCStr("tab"));}),_SK=[1,_SJ,_f],_SL=[0,9],_SM=function(_SN){return function(_SO,_SP,_SQ,_SR,_SS){return new F(function(){return _CU(new T(function(){return B(_Db(_SN,_SL));}),_SK,_SO,_SP,_SQ,_SR,_SS);});};},_ST=new T(function(){return B(_SM(_Cr));}),_SU=[0,39],_SV=[1,_SU,_f],_SW=new T(function(){return B(unCStr("\'\\\'\'"));}),_SX=function(_SY){var _SZ=E(E(_SY)[1]);return _SZ==39?E(_SW):[1,_SU,new T(function(){return B(_B7(_SZ,_SV));})];},_T0=function(_T1,_T2){return [1,_zy,new T(function(){return B(_Bo(_T1,[1,_zy,_T2]));})];},_T3=function(_T4){return new F(function(){return _1F(_SW,_T4);});},_T5=function(_T6,_T7){var _T8=E(E(_T7)[1]);return _T8==39?E(_T3):function(_T9){return [1,_SU,new T(function(){return B(_B7(_T8,[1,_SU,_T9]));})];};},_Ta=[0,_T5,_SX,_T0],_Tb=function(_Tc){return E(E(_Tc)[2]);},_Td=function(_Te,_Tf,_Tg,_Th,_Ti){var _Tj=new T(function(){return B(_Tb(_Te));}),_Tk=function(_Tl){return new F(function(){return A(_Th,[_0,_Tg,new T(function(){var _Tm=E(E(_Tg)[2]),_Tn=E(_Tl),_To=E(_Tn[1]),_Tp=B(_wk(_To[1],_To[2],_To[3],_Tn[2],_Tm[1],_Tm[2],_Tm[3],_f));return [0,E(_Tp[1]),_Tp[2]];})]);});};return new F(function(){return A(_Tf,[_Tg,function(_Tq,_Tr,_Ts){return new F(function(){return A(_Ti,[new T(function(){var _Tt=E(E(_Tr)[2]),_Tu=E(_Ts),_Tv=E(_Tu[1]),_Tw=B(_wk(_Tv[1],_Tv[2],_Tv[3],_Tu[2],_Tt[1],_Tt[2],_Tt[3],[1,new T(function(){return [1,E(B(A(_Tj,[_Tq])))];}),_f]));return [0,E(_Tw[1]),_Tw[2]];})]);});},_Tk,function(_Tx,_Ty,_Tz){return new F(function(){return A(_Th,[_0,_Tg,new T(function(){var _TA=E(E(_Tg)[2]),_TB=E(E(_Ty)[2]),_TC=E(_Tz),_TD=E(_TC[1]),_TE=B(_wk(_TD[1],_TD[2],_TD[3],_TC[2],_TB[1],_TB[2],_TB[3],[1,new T(function(){return [1,E(B(A(_Tj,[_Tx])))];}),_f])),_TF=E(_TE[1]),_TG=B(_wk(_TF[1],_TF[2],_TF[3],_TE[2],_TA[1],_TA[2],_TA[3],_f));return [0,E(_TG[1]),_TG[2]];})]);});},_Tk]);});},_TH=function(_TI,_TJ,_TK,_TL){return new F(function(){return _Td(_Ta,_ST,_TJ,function(_TM,_TN,_TO){return new F(function(){return A(_TK,[_TI,_TN,new T(function(){var _TP=E(E(_TN)[2]),_TQ=E(_TO),_TR=E(_TQ[1]),_TS=B(_wk(_TR[1],_TR[2],_TR[3],_TQ[2],_TP[1],_TP[2],_TP[3],_f));return [0,E(_TS[1]),_TS[2]];})]);});},_TL);});},_TT=function(_TU,_TV,_TW,_TX,_TY){return new F(function(){return A(_DC,[_TU,function(_TZ,_U0,_U1){return new F(function(){return _TH(_TZ,_U0,function(_U2,_U3,_U4){return new F(function(){return A(_TV,[_U2,_U3,new T(function(){return B(_x9(_U1,_U4));})]);});},function(_U5){return new F(function(){return A(_TW,[new T(function(){return B(_x9(_U1,_U5));})]);});});});},_TW,function(_U6,_U7,_U8){return new F(function(){return _TH(_U6,_U7,function(_U9,_Ua,_Ub){return new F(function(){return A(_TX,[_U9,_Ua,new T(function(){return B(_x9(_U8,_Ub));})]);});},function(_Uc){return new F(function(){return A(_TY,[new T(function(){return B(_x9(_U8,_Uc));})]);});});});},_TY]);});},_Ud=[0,E(_f)],_Ue=[1,_Ud,_f],_Uf=function(_Ug,_Uh,_Ui,_Uj,_Uk,_Ul,_Um){return new F(function(){return A(_Ug,[new T(function(){return B(A(_Uh,[_Ui]));}),function(_Un){var _Uo=E(_Un);if(!_Uo[0]){return E(new T(function(){return B(A(_Um,[[0,E(_Uj),_Ue]]));}));}else{var _Up=E(_Uo[1]);return new F(function(){return A(_Ul,[_Up[1],[0,_Up[2],E(_Uj),E(_Uk)],[0,E(_Uj),_f]]);});}}]);});},_Uq=new T(function(){return B(unCStr("end of input"));}),_Ur=[1,_Uq,_f],_Us=function(_Ut,_Uu,_Uv,_Uw,_Ux,_Uy,_Uz,_UA){return new F(function(){return _CU(function(_UB,_UC,_UD,_UE,_UF){return new F(function(){return _Td(_Uv,function(_UG,_UH,_UI,_UJ,_UK){var _UL=E(_UG);return new F(function(){return _Uf(_Ut,_Uu,_UL[1],_UL[2],_UL[3],_UH,_UK);});},_UB,_UE,_UF);});},_Ur,_Uw,_Ux,_Uy,_Uz,_UA);});},_UM=function(_UN,_UO,_UP,_UQ,_UR,_US){return new F(function(){return _Us(_zv,_Ce,_Ta,_UO,function(_UT,_UU,_UV){return new F(function(){return A(_UP,[_UN,_UU,new T(function(){var _UW=E(E(_UU)[2]),_UX=E(_UV),_UY=E(_UX[1]),_UZ=B(_wk(_UY[1],_UY[2],_UY[3],_UX[2],_UW[1],_UW[2],_UW[3],_f));return [0,E(_UZ[1]),_UZ[2]];})]);});},_UQ,function(_V0,_V1,_V2){return new F(function(){return A(_UR,[_UN,_V1,new T(function(){var _V3=E(E(_V1)[2]),_V4=E(_V2),_V5=E(_V4[1]),_V6=B(_wk(_V5[1],_V5[2],_V5[3],_V4[2],_V3[1],_V3[2],_V3[3],_f));return [0,E(_V6[1]),_V6[2]];})]);});},_US);});},_V7=function(_V8,_V9,_Va,_Vb,_Vc){return new F(function(){return A(_DC,[_V8,function(_Vd,_Ve,_Vf){return new F(function(){return _UM(_Vd,_Ve,_V9,_Va,function(_Vg,_Vh,_Vi){return new F(function(){return A(_V9,[_Vg,_Vh,new T(function(){return B(_x9(_Vf,_Vi));})]);});},function(_Vj){return new F(function(){return A(_Va,[new T(function(){return B(_x9(_Vf,_Vj));})]);});});});},_Va,function(_Vk,_Vl,_Vm){return new F(function(){return _UM(_Vk,_Vl,_V9,_Va,function(_Vn,_Vo,_Vp){return new F(function(){return A(_Vb,[_Vn,_Vo,new T(function(){return B(_x9(_Vm,_Vp));})]);});},function(_Vq){return new F(function(){return A(_Vc,[new T(function(){return B(_x9(_Vm,_Vq));})]);});});});},_Vc]);});},_Vr=function(_Vs,_Vt,_Vu,_Vv){var _Vw=function(_Vx){var _Vy=function(_Vz){return new F(function(){return A(_Vv,[new T(function(){return B(_x9(_Vx,_Vz));})]);});};return new F(function(){return _TT(_Vs,_Vt,_Vy,function(_VA,_VB,_VC){return new F(function(){return A(_Vu,[_VA,_VB,new T(function(){return B(_x9(_Vx,_VC));})]);});},_Vy);});};return new F(function(){return _V7(_Vs,_Vt,_Vw,_Vu,_Vw);});},_VD=function(_VE,_VF,_VG,_VH,_VI){return new F(function(){return _Vr(_VE,_VF,_VH,_VI);});},_VJ=function(_VK){return true;},_VL=function(_VM,_VN,_VO,_VP,_VQ){var _VR=E(_VM),_VS=E(_VR[2]);return new F(function(){return _Bu(_zv,_Ce,_VJ,_VR[1],_VS[1],_VS[2],_VS[3],_VR[3],_VN,_VQ);});},_VT=function(_VU,_VV,_VW,_VX,_VY){return new F(function(){return A(_ST,[_VU,function(_VZ,_W0,_W1){return new F(function(){return _Ro(_VL,_VD,_W0,_VV,_VW,function(_W2,_W3,_W4){return new F(function(){return A(_VV,[_W2,_W3,new T(function(){return B(_x9(_W1,_W4));})]);});},function(_W5){return new F(function(){return A(_VW,[new T(function(){return B(_x9(_W1,_W5));})]);});});});},_VW,function(_W6,_W7,_W8){return new F(function(){return _Ro(_VL,_VD,_W7,_VV,_VW,function(_W9,_Wa,_Wb){return new F(function(){return A(_VX,[_W9,_Wa,new T(function(){return B(_x9(_W8,_Wb));})]);});},function(_Wc){return new F(function(){return A(_VY,[new T(function(){return B(_x9(_W8,_Wc));})]);});});});},_VY]);});},_Wd=[0,_Qd,_f],_We=[0,_f,1,1],_Wf=function(_Wg){return E(_Wg);},_Wh=new T(function(){return B(_il("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_Wi=new T(function(){return B(_il("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_Wj=[0,_zv,_Wi,_Wf,_Wh],_Wk=[0,10],_Wl=[1,_Wk,_f],_Wm=function(_Wn){return new F(function(){return unAppCStr("string error",new T(function(){var _Wo=E(_Wn),_Wp=E(_Wo[1]);return B(_1F(B(_9O(_Wp[1],_Wp[2],_Wp[3],_Wo[2])),_Wl));}));});},_Wq=function(_Wr,_Ws,_Wt,_Wu,_Wv){return new F(function(){return A(_ST,[_Ws,function(_Ww,_Wx,_Wy){return new F(function(){return A(_Wt,[_Wr,_Wx,new T(function(){var _Wz=E(E(_Wx)[2]),_WA=E(_Wy),_WB=E(_WA[1]),_WC=B(_wk(_WB[1],_WB[2],_WB[3],_WA[2],_Wz[1],_Wz[2],_Wz[3],_f));return [0,E(_WC[1]),_WC[2]];})]);});},_Wv,function(_WD,_WE,_WF){return new F(function(){return A(_Wu,[_Wr,_WE,new T(function(){var _WG=E(E(_WE)[2]),_WH=E(_WF),_WI=E(_WH[1]),_WJ=B(_wk(_WI[1],_WI[2],_WI[3],_WH[2],_WG[1],_WG[2],_WG[3],_f));return [0,E(_WJ[1]),_WJ[2]];})]);});},_Wv]);});},_WK=function(_WL,_WM,_WN,_WO,_WP){return new F(function(){return A(_DC,[_WL,function(_WQ,_WR,_WS){return new F(function(){return _Wq(_WQ,_WR,_WM,function(_WT,_WU,_WV){return new F(function(){return A(_WM,[_WT,_WU,new T(function(){return B(_x9(_WS,_WV));})]);});},function(_WW){return new F(function(){return A(_WN,[new T(function(){return B(_x9(_WS,_WW));})]);});});});},_WN,function(_WX,_WY,_WZ){return new F(function(){return _Wq(_WX,_WY,_WM,function(_X0,_X1,_X2){return new F(function(){return A(_WO,[_X0,_X1,new T(function(){return B(_x9(_WZ,_X2));})]);});},function(_X3){return new F(function(){return A(_WP,[new T(function(){return B(_x9(_WZ,_X3));})]);});});});},_WP]);});},_X4=function(_X5,_X6,_X7,_X8,_X9){return new F(function(){return _WK(_X5,_X6,_X7,_X8,function(_Xa){var _Xb=E(_X5),_Xc=E(_Xb[2]),_Xd=E(_Xb[1]);return _Xd[0]==0?B(A(_X9,[new T(function(){var _Xe=E(_Xa),_Xf=E(_Xe[1]),_Xg=B(_wk(_Xf[1],_Xf[2],_Xf[3],_Xe[2],_Xc[1],_Xc[2],_Xc[3],_Ue));return [0,E(_Xg[1]),_Xg[2]];})])):B(A(_X6,[_Xd[1],[0,_Xd[2],E(_Xc),E(_Xb[3])],[0,E(_Xc),_f]]));});});},_Xh=function(_Xi,_Xj,_Xk,_Xl,_Xm){return new F(function(){return _wH(_X4,_Xi,_Xj,_Xk,_Xl);});},_Xn=function(_Xo,_Xp,_Xq){return [0,_Xo,E(E(_Xp)),_Xq];},_Xr=function(_Xs,_Xt,_Xu){var _Xv=new T(function(){return B(_C8(_Xs));}),_Xw=new T(function(){return B(_C8(_Xs));});return new F(function(){return A(_Xt,[_Xu,function(_Xx,_Xy,_Xz){return new F(function(){return A(_Xv,[[0,new T(function(){return B(A(_Xw,[new T(function(){return B(_Xn(_Xx,_Xy,_Xz));})]));})]]);});},function(_XA){return new F(function(){return A(_Xv,[[0,new T(function(){return B(A(_Xw,[[1,_XA]]));})]]);});},function(_XB,_XC,_XD){return new F(function(){return A(_Xv,[new T(function(){return [1,E(B(A(_Xw,[new T(function(){return B(_Xn(_XB,_XC,_XD));})])))];})]);});},function(_XE){return new F(function(){return A(_Xv,[new T(function(){return [1,E(B(A(_Xw,[[1,_XE]])))];})]);});}]);});},_XF=function(_XG){return function(_XH,_XI,_XJ,_XK,_XL){return new F(function(){return A(_XK,[new T(function(){var _XM=B(_Xr(_Wj,_XN,[0,new T(function(){var _XO=B(_Xr(_Wj,_Xh,[0,_XG,E(_We),E(_0)]));if(!_XO[0]){var _XP=E(_XO[1]),_XQ=_XP[0]==0?B(_1F(_XP[1],_Wl)):B(_Wm(_XP[1]));}else{var _XR=E(_XO[1]),_XQ=_XR[0]==0?B(_1F(_XR[1],_Wl)):B(_Wm(_XR[1]));}return _XQ;}),E(_We),E(_0)]));if(!_XM[0]){var _XS=E(_XM[1]),_XT=_XS[0]==0?E(_XS[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9T(_XS[1]));})));})],_f],_f],_Wd];}else{var _XU=E(_XM[1]),_XT=_XU[0]==0?E(_XU[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9T(_XU[1]));})));})],_f],_f],_Wd];}return _XT;}),_XH,new T(function(){return [0,E(E(_XH)[2]),_f];})]);});};},_XV=function(_XW,_XX,_XY,_XZ,_Y0){return new F(function(){return _VT(_XW,function(_Y1,_Y2,_Y3){return new F(function(){return A(_XF,[_Y1,_Y2,_XX,_XY,function(_Y4,_Y5,_Y6){return new F(function(){return A(_XX,[_Y4,_Y5,new T(function(){return B(_x9(_Y3,_Y6));})]);});},function(_Y7){return new F(function(){return A(_XY,[new T(function(){return B(_x9(_Y3,_Y7));})]);});}]);});},_XY,function(_Y8,_Y9,_Ya){return new F(function(){return A(_XF,[_Y8,_Y9,_XX,_XY,function(_Yb,_Yc,_Yd){return new F(function(){return A(_XZ,[_Yb,_Yc,new T(function(){return B(_x9(_Ya,_Yd));})]);});},function(_Ye){return new F(function(){return A(_Y0,[new T(function(){return B(_x9(_Ya,_Ye));})]);});}]);});},_Y0);});},_Yf=function(_Yg,_Yh,_Yi,_Yj,_Yk,_Yl){var _Ym=function(_Yn,_Yo,_Yp,_Yq,_Yr){var _Ys=function(_Yt,_Yu,_Yv,_Yw,_Yx){return new F(function(){return A(_Yq,[[0,[1,[0,_Yg,_Yu,_Yv]],_Yt],_Yw,new T(function(){var _Yy=E(_Yx),_Yz=E(_Yy[1]),_YA=E(E(_Yw)[2]),_YB=B(_wk(_Yz[1],_Yz[2],_Yz[3],_Yy[2],_YA[1],_YA[2],_YA[3],_f));return [0,E(_YB[1]),_YB[2]];})]);});},_YC=function(_YD){return new F(function(){return _Ys(_f,_Qd,_f,_Yn,new T(function(){var _YE=E(E(_Yn)[2]),_YF=E(_YD),_YG=E(_YF[1]),_YH=B(_wk(_YG[1],_YG[2],_YG[3],_YF[2],_YE[1],_YE[2],_YE[3],_f));return [0,E(_YH[1]),_YH[2]];}));});};return new F(function(){return _XV(_Yn,function(_YI,_YJ,_YK){var _YL=E(_YI),_YM=E(_YL[2]);return new F(function(){return A(_Yo,[[0,[1,[0,_Yg,_YM[1],_YM[2]]],_YL[1]],_YJ,new T(function(){var _YN=E(_YK),_YO=E(_YN[1]),_YP=E(E(_YJ)[2]),_YQ=B(_wk(_YO[1],_YO[2],_YO[3],_YN[2],_YP[1],_YP[2],_YP[3],_f));return [0,E(_YQ[1]),_YQ[2]];})]);});},_YC,function(_YR,_YS,_YT){var _YU=E(_YR),_YV=E(_YU[2]);return new F(function(){return _Ys(_YU[1],_YV[1],_YV[2],_YS,_YT);});},_YC);});};return new F(function(){return A(_DC,[_Yh,function(_YW,_YX,_YY){return new F(function(){return _Ym(_YX,_Yi,_Yj,function(_YZ,_Z0,_Z1){return new F(function(){return A(_Yi,[_YZ,_Z0,new T(function(){return B(_x9(_YY,_Z1));})]);});},function(_Z2){return new F(function(){return A(_Yj,[new T(function(){return B(_x9(_YY,_Z2));})]);});});});},_Yl,function(_Z3,_Z4,_Z5){return new F(function(){return _Ym(_Z4,_Yi,_Yj,function(_Z6,_Z7,_Z8){return new F(function(){return A(_Yk,[_Z6,_Z7,new T(function(){return B(_x9(_Z5,_Z8));})]);});},function(_Z9){return new F(function(){return A(_Yl,[new T(function(){return B(_x9(_Z5,_Z9));})]);});});});},_Yl]);});},_Za=new T(function(){return B(unCStr(" associative operator"));}),_Zb=function(_Zc,_Zd){var _Ze=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_1F(_Zc,_Za));}))))];}),_f];return function(_Zf,_Zg,_Zh,_Zi,_Zj){return new F(function(){return A(_Zd,[_Zf,function(_Zk,_Zl,_Zm){return new F(function(){return A(_Zj,[new T(function(){var _Zn=E(E(_Zl)[2]),_Zo=E(_Zm),_Zp=E(_Zo[1]),_Zq=B(_wk(_Zp[1],_Zp[2],_Zp[3],_Zo[2],_Zn[1],_Zn[2],_Zn[3],_Ze));return [0,E(_Zq[1]),_Zq[2]];})]);});},_Zj,function(_Zr,_Zs,_Zt){return new F(function(){return A(_Zj,[new T(function(){var _Zu=E(E(_Zs)[2]),_Zv=E(_Zt),_Zw=E(_Zv[1]),_Zx=B(_wk(_Zw[1],_Zw[2],_Zw[3],_Zv[2],_Zu[1],_Zu[2],_Zu[3],_Ze));return [0,E(_Zx[1]),_Zx[2]];})]);});},_Zj]);});};},_Zy=function(_Zz,_ZA,_ZB,_ZC,_ZD,_ZE){var _ZF=E(_Zz);if(!_ZF[0]){return new F(function(){return A(_ZE,[new T(function(){return [0,E(E(_ZA)[2]),_f];})]);});}else{return new F(function(){return A(_ZF[1],[_ZA,_ZB,_ZC,_ZD,function(_ZG){return new F(function(){return _Zy(_ZF[2],_ZA,_ZB,_ZC,function(_ZH,_ZI,_ZJ){return new F(function(){return A(_ZD,[_ZH,_ZI,new T(function(){return B(_x9(_ZG,_ZJ));})]);});},function(_ZK){return new F(function(){return A(_ZE,[new T(function(){return B(_x9(_ZG,_ZK));})]);});});});}]);});}},_ZL=new T(function(){return B(unCStr("right"));}),_ZM=new T(function(){return B(unCStr("left"));}),_ZN=new T(function(){return B(unCStr("non"));}),_ZO=new T(function(){return B(unCStr("operator"));}),_ZP=[1,_ZO,_f],_ZQ=[1,_f,_f],_ZR=function(_ZS){var _ZT=E(_ZS);if(!_ZT[0]){return [0,_f,_f,_f,_f,_f];}else{var _ZU=_ZT[2],_ZV=E(_ZT[1]);switch(_ZV[0]){case 0:var _ZW=_ZV[1],_ZX=B(_ZR(_ZU)),_ZY=_ZX[1],_ZZ=_ZX[2],_100=_ZX[3],_101=_ZX[4],_102=_ZX[5];switch(E(_ZV[2])){case 0:return [0,_ZY,_ZZ,[1,_ZW,_100],_101,_102];case 1:return [0,_ZY,[1,_ZW,_ZZ],_100,_101,_102];default:return [0,[1,_ZW,_ZY],_ZZ,_100,_101,_102];}break;case 1:var _103=B(_ZR(_ZU));return [0,_103[1],_103[2],_103[3],[1,_ZV[1],_103[4]],_103[5]];default:var _104=B(_ZR(_ZU));return [0,_104[1],_104[2],_104[3],_104[4],[1,_ZV[1],_104[5]]];}}},_105=function(_106,_107){while(1){var _108=(function(_109,_10a){var _10b=E(_10a);if(!_10b[0]){return E(_109);}else{var _10c=new T(function(){var _10d=B(_ZR(_10b[1]));return [0,_10d[1],_10d[2],_10d[3],_10d[4],_10d[5]];}),_10e=new T(function(){return E(E(_10c)[2]);}),_10f=new T(function(){return B(_Zb(_ZM,function(_10g,_10h,_10i,_10j,_10k){return new F(function(){return _Zy(_10e,_10g,_10h,_10i,_10j,_10k);});}));}),_10l=new T(function(){return E(E(_10c)[1]);}),_10m=new T(function(){return E(E(_10c)[3]);}),_10n=new T(function(){return B(_Zb(_ZN,function(_10o,_10p,_10q,_10r,_10s){return new F(function(){return _Zy(_10m,_10o,_10p,_10q,_10r,_10s);});}));}),_10t=function(_10u,_10v,_10w,_10x,_10y,_10z){var _10A=function(_10B,_10C,_10D,_10E,_10F){var _10G=new T(function(){return B(A(_10u,[_10B]));});return new F(function(){return _Zy(new T(function(){return E(E(_10c)[5]);}),_10C,function(_10H,_10I,_10J){return new F(function(){return A(_10D,[new T(function(){return B(A(_10H,[_10G]));}),_10I,new T(function(){var _10K=E(E(_10I)[2]),_10L=E(_10J),_10M=E(_10L[1]),_10N=B(_wk(_10M[1],_10M[2],_10M[3],_10L[2],_10K[1],_10K[2],_10K[3],_f));return [0,E(_10N[1]),_10N[2]];})]);});},_10E,function(_10O,_10P,_10Q){return new F(function(){return A(_10F,[new T(function(){return B(A(_10O,[_10G]));}),_10P,new T(function(){var _10R=E(E(_10P)[2]),_10S=_10R[1],_10T=_10R[2],_10U=_10R[3],_10V=E(_10Q),_10W=E(_10V[1]),_10X=_10W[2],_10Y=_10W[3],_10Z=E(_10V[2]);if(!_10Z[0]){switch(B(_wc(_10W[1],_10S))){case 0:var _110=[0,E(_10R),_f];break;case 1:if(_10X>=_10T){if(_10X!=_10T){var _111=[0,E(_10W),_f];}else{if(_10Y>=_10U){var _112=_10Y!=_10U?[0,E(_10W),_f]:[0,E(_10W),_wj];}else{var _112=[0,E(_10R),_f];}var _113=_112,_111=_113;}var _114=_111,_115=_114;}else{var _115=[0,E(_10R),_f];}var _116=_115,_110=_116;break;default:var _110=[0,E(_10W),_f];}var _117=_110;}else{var _118=B(_Cz(_10W,_10Z,_ZQ)),_119=E(_118[1]),_11a=B(_wk(_119[1],_119[2],_119[3],_118[2],_10S,_10T,_10U,_f)),_117=[0,E(_11a[1]),_11a[2]];}var _11b=_117,_11c=_11b,_11d=_11c,_11e=_11d;return _11e;})]);});},function(_11f){return new F(function(){return A(_10F,[_10G,_10C,new T(function(){var _11g=E(E(_10C)[2]),_11h=_11g[1],_11i=_11g[2],_11j=_11g[3],_11k=E(_11f),_11l=B(_Cz(_11k[1],_11k[2],_ZQ)),_11m=E(_11l[1]),_11n=B(_wk(_11m[1],_11m[2],_11m[3],_11l[2],_11h,_11i,_11j,_f)),_11o=E(_11n[1]),_11p=B(_wk(_11o[1],_11o[2],_11o[3],_11n[2],_11h,_11i,_11j,_f));return [0,E(_11p[1]),_11p[2]];})]);});});});};return new F(function(){return A(_109,[_10v,function(_11q,_11r,_11s){return new F(function(){return _10A(_11q,_11r,_10w,_10x,function(_11t,_11u,_11v){return new F(function(){return A(_10w,[_11t,_11u,new T(function(){return B(_x9(_11s,_11v));})]);});});});},_10x,function(_11w,_11x,_11y){return new F(function(){return _10A(_11w,_11x,_10w,_10x,function(_11z,_11A,_11B){return new F(function(){return A(_10y,[_11z,_11A,new T(function(){return B(_x9(_11y,_11B));})]);});});});},_10z]);});},_11C=function(_11D,_11E,_11F,_11G,_11H){var _11I=function(_11J,_11K,_11L){return new F(function(){return _10t(_11J,_11K,_11E,_11F,function(_11M,_11N,_11O){return new F(function(){return A(_11G,[_11M,_11N,new T(function(){return B(_x9(_11L,_11O));})]);});},function(_11P){return new F(function(){return A(_11H,[new T(function(){return B(_x9(_11L,_11P));})]);});});});};return new F(function(){return _Zy(new T(function(){return E(E(_10c)[4]);}),_11D,function(_11Q,_11R,_11S){return new F(function(){return _10t(_11Q,_11R,_11E,_11F,function(_11T,_11U,_11V){return new F(function(){return A(_11E,[_11T,_11U,new T(function(){return B(_x9(_11S,_11V));})]);});},function(_11W){return new F(function(){return A(_11F,[new T(function(){return B(_x9(_11S,_11W));})]);});});});},_11F,function(_11X,_11Y,_11Z){return new F(function(){return _11I(_11X,_11Y,new T(function(){var _120=E(_11Z),_121=E(_120[2]);if(!_121[0]){var _122=E(_120);}else{var _123=B(_Cz(_120[1],_121,_ZQ)),_122=[0,E(_123[1]),_123[2]];}var _124=_122;return _124;}));});},function(_125){return new F(function(){return _11I(_4s,_11D,new T(function(){var _126=E(E(_11D)[2]),_127=E(_125),_128=B(_Cz(_127[1],_127[2],_ZQ)),_129=E(_128[1]),_12a=B(_wk(_129[1],_129[2],_129[3],_128[2],_126[1],_126[2],_126[3],_f));return [0,E(_12a[1]),_12a[2]];}));});});});},_12b=function(_12c,_12d,_12e,_12f,_12g,_12h){var _12i=function(_12j){return new F(function(){return A(_10f,[_12d,_12e,_12f,function(_12k,_12l,_12m){return new F(function(){return A(_12g,[_12k,_12l,new T(function(){return B(_x9(_12j,_12m));})]);});},function(_12n){return new F(function(){return A(_10n,[_12d,_12e,_12f,function(_12o,_12p,_12q){return new F(function(){return A(_12g,[_12o,_12p,new T(function(){var _12r=E(_12j),_12s=E(_12r[1]),_12t=E(_12n),_12u=E(_12t[1]),_12v=E(_12q),_12w=E(_12v[1]),_12x=B(_wk(_12u[1],_12u[2],_12u[3],_12t[2],_12w[1],_12w[2],_12w[3],_12v[2])),_12y=E(_12x[1]),_12z=B(_wk(_12s[1],_12s[2],_12s[3],_12r[2],_12y[1],_12y[2],_12y[3],_12x[2]));return [0,E(_12z[1]),_12z[2]];})]);});},function(_12A){return new F(function(){return A(_12h,[new T(function(){var _12B=E(_12j),_12C=E(_12B[1]),_12D=E(_12n),_12E=E(_12D[1]),_12F=E(_12A),_12G=E(_12F[1]),_12H=B(_wk(_12E[1],_12E[2],_12E[3],_12D[2],_12G[1],_12G[2],_12G[3],_12F[2])),_12I=E(_12H[1]),_12J=B(_wk(_12C[1],_12C[2],_12C[3],_12B[2],_12I[1],_12I[2],_12I[3],_12H[2]));return [0,E(_12J[1]),_12J[2]];})]);});}]);});}]);});},_12K=function(_12L,_12M,_12N,_12O,_12P,_12Q){var _12R=function(_12S,_12T,_12U){return new F(function(){return A(_12N,[new T(function(){return B(A(_12L,[_12c,_12S]));}),_12T,new T(function(){var _12V=E(E(_12T)[2]),_12W=E(_12U),_12X=E(_12W[1]),_12Y=B(_wk(_12X[1],_12X[2],_12X[3],_12W[2],_12V[1],_12V[2],_12V[3],_f));return [0,E(_12Y[1]),_12Y[2]];})]);});};return new F(function(){return _11C(_12M,function(_12Z,_130,_131){return new F(function(){return _12b(_12Z,_130,_12R,_12O,function(_132,_133,_134){return new F(function(){return _12R(_132,_133,new T(function(){var _135=E(_131),_136=E(_135[1]),_137=E(_134),_138=E(_137[1]),_139=B(_wk(_136[1],_136[2],_136[3],_135[2],_138[1],_138[2],_138[3],_137[2]));return [0,E(_139[1]),_139[2]];},1));});},function(_13a){return new F(function(){return _12R(_12Z,_130,new T(function(){var _13b=E(E(_130)[2]),_13c=E(_131),_13d=E(_13c[1]),_13e=E(_13a),_13f=E(_13e[1]),_13g=B(_wk(_13f[1],_13f[2],_13f[3],_13e[2],_13b[1],_13b[2],_13b[3],_f)),_13h=E(_13g[1]),_13i=B(_wk(_13d[1],_13d[2],_13d[3],_13c[2],_13h[1],_13h[2],_13h[3],_13g[2]));return [0,E(_13i[1]),_13i[2]];},1));});});});},_12O,function(_13j,_13k,_13l){var _13m=function(_13n,_13o,_13p){return new F(function(){return A(_12P,[new T(function(){return B(A(_12L,[_12c,_13n]));}),_13o,new T(function(){var _13q=E(E(_13o)[2]),_13r=E(_13l),_13s=E(_13r[1]),_13t=E(_13p),_13u=E(_13t[1]),_13v=B(_wk(_13s[1],_13s[2],_13s[3],_13r[2],_13u[1],_13u[2],_13u[3],_13t[2])),_13w=E(_13v[1]),_13x=B(_wk(_13w[1],_13w[2],_13w[3],_13v[2],_13q[1],_13q[2],_13q[3],_f));return [0,E(_13x[1]),_13x[2]];})]);});};return new F(function(){return _12b(_13j,_13k,_12R,_12O,_13m,function(_13y){return new F(function(){return _13m(_13j,_13k,new T(function(){var _13z=E(E(_13k)[2]),_13A=E(_13y),_13B=E(_13A[1]),_13C=B(_wk(_13B[1],_13B[2],_13B[3],_13A[2],_13z[1],_13z[2],_13z[3],_f));return [0,E(_13C[1]),_13C[2]];},1));});});});},_12Q);});};return new F(function(){return _Zy(_10l,_12d,function(_13D,_13E,_13F){return new F(function(){return _12K(_13D,_13E,_12e,_12f,function(_13G,_13H,_13I){return new F(function(){return A(_12e,[_13G,_13H,new T(function(){return B(_x9(_13F,_13I));})]);});},function(_13J){return new F(function(){return A(_12f,[new T(function(){return B(_x9(_13F,_13J));})]);});});});},_12f,function(_13K,_13L,_13M){return new F(function(){return _12K(_13K,_13L,_12e,_12f,function(_13N,_13O,_13P){return new F(function(){return A(_12g,[_13N,_13O,new T(function(){return B(_x9(_13M,_13P));})]);});},function(_13Q){return new F(function(){return _12i(new T(function(){return B(_x9(_13M,_13Q));}));});});});},_12i);});},_13R=new T(function(){return B(_Zb(_ZL,function(_13S,_13T,_13U,_13V,_13W){return new F(function(){return _Zy(_10l,_13S,_13T,_13U,_13V,_13W);});}));}),_13X=function(_13Y,_13Z,_140,_141,_142,_143){var _144=function(_145){return new F(function(){return A(_13R,[_13Z,_140,_141,function(_146,_147,_148){return new F(function(){return A(_142,[_146,_147,new T(function(){return B(_x9(_145,_148));})]);});},function(_149){return new F(function(){return A(_10n,[_13Z,_140,_141,function(_14a,_14b,_14c){return new F(function(){return A(_142,[_14a,_14b,new T(function(){var _14d=E(_145),_14e=E(_14d[1]),_14f=E(_149),_14g=E(_14f[1]),_14h=E(_14c),_14i=E(_14h[1]),_14j=B(_wk(_14g[1],_14g[2],_14g[3],_14f[2],_14i[1],_14i[2],_14i[3],_14h[2])),_14k=E(_14j[1]),_14l=B(_wk(_14e[1],_14e[2],_14e[3],_14d[2],_14k[1],_14k[2],_14k[3],_14j[2]));return [0,E(_14l[1]),_14l[2]];})]);});},function(_14m){return new F(function(){return A(_143,[new T(function(){var _14n=E(_145),_14o=E(_14n[1]),_14p=E(_149),_14q=E(_14p[1]),_14r=E(_14m),_14s=E(_14r[1]),_14t=B(_wk(_14q[1],_14q[2],_14q[3],_14p[2],_14s[1],_14s[2],_14s[3],_14r[2])),_14u=E(_14t[1]),_14v=B(_wk(_14o[1],_14o[2],_14o[3],_14n[2],_14u[1],_14u[2],_14u[3],_14t[2]));return [0,E(_14v[1]),_14v[2]];})]);});}]);});}]);});},_14w=function(_14x,_14y,_14z,_14A,_14B,_14C){var _14D=function(_14E){var _14F=new T(function(){return B(A(_14x,[_13Y,_14E]));});return function(_14G,_14H,_14I,_14J,_14K){return new F(function(){return _13X(_14F,_14G,_14H,_14I,_14J,function(_14L){return new F(function(){return A(_14J,[_14F,_14G,new T(function(){var _14M=E(E(_14G)[2]),_14N=E(_14L),_14O=E(_14N[1]),_14P=B(_wk(_14O[1],_14O[2],_14O[3],_14N[2],_14M[1],_14M[2],_14M[3],_f));return [0,E(_14P[1]),_14P[2]];})]);});});});};};return new F(function(){return _11C(_14y,function(_14Q,_14R,_14S){return new F(function(){return A(_14D,[_14Q,_14R,_14z,_14A,function(_14T,_14U,_14V){return new F(function(){return A(_14z,[_14T,_14U,new T(function(){return B(_x9(_14S,_14V));})]);});},function(_14W){return new F(function(){return A(_14A,[new T(function(){return B(_x9(_14S,_14W));})]);});}]);});},_14A,function(_14X,_14Y,_14Z){return new F(function(){return A(_14D,[_14X,_14Y,_14z,_14A,function(_150,_151,_152){return new F(function(){return A(_14B,[_150,_151,new T(function(){return B(_x9(_14Z,_152));})]);});},function(_153){return new F(function(){return A(_14C,[new T(function(){return B(_x9(_14Z,_153));})]);});}]);});},_14C);});};return new F(function(){return _Zy(_10e,_13Z,function(_154,_155,_156){return new F(function(){return _14w(_154,_155,_140,_141,function(_157,_158,_159){return new F(function(){return A(_140,[_157,_158,new T(function(){return B(_x9(_156,_159));})]);});},function(_15a){return new F(function(){return A(_141,[new T(function(){return B(_x9(_156,_15a));})]);});});});},_141,function(_15b,_15c,_15d){return new F(function(){return _14w(_15b,_15c,_140,_141,function(_15e,_15f,_15g){return new F(function(){return A(_142,[_15e,_15f,new T(function(){return B(_x9(_15d,_15g));})]);});},function(_15h){return new F(function(){return _144(new T(function(){return B(_x9(_15d,_15h));}));});});});},_144);});},_15i=function(_15j,_15k,_15l,_15m,_15n,_15o){var _15p=function(_15q,_15r,_15s,_15t,_15u,_15v){var _15w=function(_15x){return function(_15y,_15z,_15A,_15B,_15C){return new F(function(){return A(_13R,[_15y,_15z,_15A,_15B,function(_15D){return new F(function(){return A(_10f,[_15y,_15z,_15A,function(_15E,_15F,_15G){return new F(function(){return A(_15B,[_15E,_15F,new T(function(){return B(_x9(_15D,_15G));})]);});},function(_15H){return new F(function(){return A(_10n,[_15y,_15z,_15A,function(_15I,_15J,_15K){return new F(function(){return A(_15B,[_15I,_15J,new T(function(){var _15L=E(_15D),_15M=E(_15L[1]),_15N=E(_15H),_15O=E(_15N[1]),_15P=E(_15K),_15Q=E(_15P[1]),_15R=B(_wk(_15O[1],_15O[2],_15O[3],_15N[2],_15Q[1],_15Q[2],_15Q[3],_15P[2])),_15S=E(_15R[1]),_15T=B(_wk(_15M[1],_15M[2],_15M[3],_15L[2],_15S[1],_15S[2],_15S[3],_15R[2]));return [0,E(_15T[1]),_15T[2]];})]);});},function(_15U){return new F(function(){return A(_15B,[new T(function(){return B(A(_15q,[_15j,_15x]));}),_15y,new T(function(){var _15V=E(E(_15y)[2]),_15W=E(_15D),_15X=E(_15W[1]),_15Y=E(_15H),_15Z=E(_15Y[1]),_160=E(_15U),_161=E(_160[1]),_162=B(_wk(_161[1],_161[2],_161[3],_160[2],_15V[1],_15V[2],_15V[3],_f)),_163=E(_162[1]),_164=B(_wk(_15Z[1],_15Z[2],_15Z[3],_15Y[2],_163[1],_163[2],_163[3],_162[2])),_165=E(_164[1]),_166=B(_wk(_15X[1],_15X[2],_15X[3],_15W[2],_165[1],_165[2],_165[3],_164[2]));return [0,E(_166[1]),_166[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _11C(_15r,function(_167,_168,_169){return new F(function(){return A(_15w,[_167,_168,_15s,_15t,function(_16a,_16b,_16c){return new F(function(){return A(_15s,[_16a,_16b,new T(function(){return B(_x9(_169,_16c));})]);});},function(_16d){return new F(function(){return A(_15t,[new T(function(){return B(_x9(_169,_16d));})]);});}]);});},_15t,function(_16e,_16f,_16g){return new F(function(){return A(_15w,[_16e,_16f,_15s,_15t,function(_16h,_16i,_16j){return new F(function(){return A(_15u,[_16h,_16i,new T(function(){return B(_x9(_16g,_16j));})]);});},function(_16k){return new F(function(){return A(_15v,[new T(function(){return B(_x9(_16g,_16k));})]);});}]);});},_15v);});};return new F(function(){return _CU(function(_16l,_16m,_16n,_16o,_16p){return new F(function(){return _12b(_15j,_16l,_16m,_16n,_16o,function(_16q){return new F(function(){return _13X(_15j,_16l,_16m,_16n,function(_16r,_16s,_16t){return new F(function(){return A(_16o,[_16r,_16s,new T(function(){return B(_x9(_16q,_16t));})]);});},function(_16u){var _16v=function(_16w){return new F(function(){return A(_16o,[_15j,_16l,new T(function(){var _16x=E(E(_16l)[2]),_16y=E(_16q),_16z=E(_16y[1]),_16A=E(_16u),_16B=E(_16A[1]),_16C=E(_16w),_16D=E(_16C[1]),_16E=B(_wk(_16D[1],_16D[2],_16D[3],_16C[2],_16x[1],_16x[2],_16x[3],_f)),_16F=E(_16E[1]),_16G=B(_wk(_16B[1],_16B[2],_16B[3],_16A[2],_16F[1],_16F[2],_16F[3],_16E[2])),_16H=E(_16G[1]),_16I=B(_wk(_16z[1],_16z[2],_16z[3],_16y[2],_16H[1],_16H[2],_16H[3],_16G[2]));return [0,E(_16I[1]),_16I[2]];})]);});};return new F(function(){return _Zy(_10m,_16l,function(_16J,_16K,_16L){return new F(function(){return _15p(_16J,_16K,_16m,_16n,function(_16M,_16N,_16O){return new F(function(){return A(_16m,[_16M,_16N,new T(function(){return B(_x9(_16L,_16O));})]);});},function(_16P){return new F(function(){return A(_16n,[new T(function(){return B(_x9(_16L,_16P));})]);});});});},_16n,function(_16Q,_16R,_16S){return new F(function(){return _15p(_16Q,_16R,_16m,_16n,function(_16T,_16U,_16V){return new F(function(){return A(_16o,[_16T,_16U,new T(function(){var _16W=E(_16q),_16X=E(_16W[1]),_16Y=E(_16u),_16Z=E(_16Y[1]),_170=E(_16S),_171=E(_170[1]),_172=E(_16V),_173=E(_172[1]),_174=B(_wk(_171[1],_171[2],_171[3],_170[2],_173[1],_173[2],_173[3],_172[2])),_175=E(_174[1]),_176=B(_wk(_16Z[1],_16Z[2],_16Z[3],_16Y[2],_175[1],_175[2],_175[3],_174[2])),_177=E(_176[1]),_178=B(_wk(_16X[1],_16X[2],_16X[3],_16W[2],_177[1],_177[2],_177[3],_176[2]));return [0,E(_178[1]),_178[2]];})]);});},function(_179){return new F(function(){return _16v(new T(function(){var _17a=E(_16S),_17b=E(_17a[1]),_17c=E(_179),_17d=E(_17c[1]),_17e=B(_wk(_17b[1],_17b[2],_17b[3],_17a[2],_17d[1],_17d[2],_17d[3],_17c[2]));return [0,E(_17e[1]),_17e[2]];},1));});});});},_16v);});});});});});},_ZP,_15k,_15l,_15m,_15n,_15o);});};_106=function(_17f,_17g,_17h,_17i,_17j){return new F(function(){return _11C(_17f,function(_17k,_17l,_17m){return new F(function(){return _15i(_17k,_17l,_17g,_17h,function(_17n,_17o,_17p){return new F(function(){return A(_17g,[_17n,_17o,new T(function(){return B(_x9(_17m,_17p));})]);});},function(_17q){return new F(function(){return A(_17h,[new T(function(){return B(_x9(_17m,_17q));})]);});});});},_17h,function(_17r,_17s,_17t){return new F(function(){return _15i(_17r,_17s,_17g,_17h,function(_17u,_17v,_17w){return new F(function(){return A(_17i,[_17u,_17v,new T(function(){return B(_x9(_17t,_17w));})]);});},function(_17x){return new F(function(){return A(_17j,[new T(function(){return B(_x9(_17t,_17x));})]);});});});},_17j);});};_107=_10b[2];return null;}})(_106,_107);if(_108!=null){return _108;}}},_17y=0,_17z=[3,_],_17A=function(_17B,_17C){return [5,_17z,_17B,_17C];},_17D=new T(function(){return B(unCStr("=>"));}),_17E=function(_17F){return E(E(_17F)[1]);},_17G=function(_17H,_17I,_17J,_17K){while(1){var _17L=E(_17K);if(!_17L[0]){return [0,_17H,_17I,_17J];}else{var _17M=_17L[2];switch(E(E(_17L[1])[1])){case 9:var _17N=(_17J+8|0)-B(_zC(_17J-1|0,8))|0;_17K=_17M;_17J=_17N;continue;case 10:var _17O=_17I+1|0;_17J=1;_17K=_17M;_17I=_17O;continue;default:var _17N=_17J+1|0;_17K=_17M;_17J=_17N;continue;}}}},_17P=function(_17Q){return E(E(_17Q)[1]);},_17R=function(_17S){return E(E(_17S)[2]);},_17T=function(_17U){return [0,E(E(_17U)[2]),_f];},_17V=function(_17W,_17X,_17Y,_17Z,_180,_181,_182){var _183=E(_17X);if(!_183[0]){return new F(function(){return A(_181,[_f,_17Y,new T(function(){return B(_17T(_17Y));})]);});}else{var _184=E(_17Y),_185=E(_184[2]),_186=new T(function(){return B(_17E(_17W));}),_187=[0,E(_185),[1,[2,E([1,_zy,new T(function(){return B(_Bo(_183,_zz));})])],_zB]],_188=[2,E([1,_zy,new T(function(){return B(_Bo(_183,_zz));})])],_189=new T(function(){var _18a=B(_17G(_185[1],_185[2],_185[3],_183));return [0,_18a[1],_18a[2],_18a[3]];}),_18b=function(_18c,_18d){var _18e=E(_18c);if(!_18e[0]){return new F(function(){return A(_17Z,[_183,new T(function(){return [0,_18d,E(E(_189)),E(_184[3])];}),new T(function(){return [0,E(E(_189)),_f];})]);});}else{return new F(function(){return A(new T(function(){return B(_17P(_186));}),[new T(function(){return B(A(new T(function(){return B(_17R(_17W));}),[_18d]));}),function(_18f){var _18g=E(_18f);if(!_18g[0]){return E(new T(function(){return B(A(_180,[_187]));}));}else{var _18h=E(_18g[1]),_18i=E(_18h[1]);return E(_18e[1])[1]!=_18i[1]?B(A(_180,[[0,E(_185),[1,_188,[1,[0,E([1,_zy,new T(function(){return B(_Bo([1,_18i,_f],_zz));})])],_f]]]])):B(_18b(_18e[2],_18h[2]));}}]);});}};return new F(function(){return A(_17P,[_186,new T(function(){return B(A(_17R,[_17W,_184[1]]));}),function(_18j){var _18k=E(_18j);if(!_18k[0]){return E(new T(function(){return B(A(_182,[_187]));}));}else{var _18l=E(_18k[1]),_18m=E(_18l[1]);return E(_183[1])[1]!=_18m[1]?B(A(_182,[[0,E(_185),[1,_188,[1,[0,E([1,_zy,new T(function(){return B(_Bo([1,_18m,_f],_zz));})])],_f]]]])):B(_18b(_183[2],_18l[2]));}}]);});}},_18n=function(_18o,_18p,_18q,_18r,_18s){return new F(function(){return _17V(_E4,_17D,_18o,function(_18t,_18u,_18v){return new F(function(){return A(_18p,[_17A,_18u,new T(function(){var _18w=E(E(_18u)[2]),_18x=E(_18v),_18y=E(_18x[1]),_18z=B(_wk(_18y[1],_18y[2],_18y[3],_18x[2],_18w[1],_18w[2],_18w[3],_f));return [0,E(_18z[1]),_18z[2]];})]);});},_18q,function(_18A,_18B,_18C){return new F(function(){return A(_18r,[_17A,_18B,new T(function(){var _18D=E(E(_18B)[2]),_18E=E(_18C),_18F=E(_18E[1]),_18G=B(_wk(_18F[1],_18F[2],_18F[3],_18E[2],_18D[1],_18D[2],_18D[3],_f));return [0,E(_18G[1]),_18G[2]];})]);});},_18s);});},_18H=[0,_18n,_17y],_18I=[1,_18H,_f],_18J=[1,_18I,_f],_18K=1,_18L=[2,_],_18M=function(_17B,_17C){return [5,_18L,_17B,_17C];},_18N=new T(function(){return B(unCStr("\\/"));}),_18O=function(_18P,_18Q,_18R,_18S,_18T){return new F(function(){return _17V(_E4,_18N,_18P,function(_18U,_18V,_18W){return new F(function(){return A(_18Q,[_18M,_18V,new T(function(){var _18X=E(E(_18V)[2]),_18Y=E(_18W),_18Z=E(_18Y[1]),_190=B(_wk(_18Z[1],_18Z[2],_18Z[3],_18Y[2],_18X[1],_18X[2],_18X[3],_f));return [0,E(_190[1]),_190[2]];})]);});},_18R,function(_191,_192,_193){return new F(function(){return A(_18S,[_18M,_192,new T(function(){var _194=E(E(_192)[2]),_195=E(_193),_196=E(_195[1]),_197=B(_wk(_196[1],_196[2],_196[3],_195[2],_194[1],_194[2],_194[3],_f));return [0,E(_197[1]),_197[2]];})]);});},_18T);});},_198=[0,_18O,_18K],_199=[1,_],_19a=function(_17B,_17C){return [5,_199,_17B,_17C];},_19b=new T(function(){return B(unCStr("/\\"));}),_19c=function(_19d,_19e,_19f,_19g,_19h){return new F(function(){return _17V(_E4,_19b,_19d,function(_19i,_19j,_19k){return new F(function(){return A(_19e,[_19a,_19j,new T(function(){var _19l=E(E(_19j)[2]),_19m=E(_19k),_19n=E(_19m[1]),_19o=B(_wk(_19n[1],_19n[2],_19n[3],_19m[2],_19l[1],_19l[2],_19l[3],_f));return [0,E(_19o[1]),_19o[2]];})]);});},_19f,function(_19p,_19q,_19r){return new F(function(){return A(_19g,[_19a,_19q,new T(function(){var _19s=E(E(_19q)[2]),_19t=E(_19r),_19u=E(_19t[1]),_19v=B(_wk(_19u[1],_19u[2],_19u[3],_19t[2],_19s[1],_19s[2],_19s[3],_f));return [0,E(_19v[1]),_19v[2]];})]);});},_19h);});},_19w=[0,_19c,_18K],_19x=[1,_19w,_f],_19y=[1,_198,_19x],_19z=[1,_19y,_18J],_19A=[0,_],_19B=function(_17C){return [4,_19A,_17C];},_19C=[0,45],_19D=[1,_19C,_f],_19E=function(_19F,_19G,_19H,_19I,_19J){return new F(function(){return _17V(_E4,_19D,_19F,function(_19K,_19L,_19M){return new F(function(){return A(_19G,[_19B,_19L,new T(function(){var _19N=E(E(_19L)[2]),_19O=E(_19M),_19P=E(_19O[1]),_19Q=B(_wk(_19P[1],_19P[2],_19P[3],_19O[2],_19N[1],_19N[2],_19N[3],_f));return [0,E(_19Q[1]),_19Q[2]];})]);});},_19H,function(_19R,_19S,_19T){return new F(function(){return A(_19I,[_19B,_19S,new T(function(){var _19U=E(E(_19S)[2]),_19V=E(_19T),_19W=E(_19V[1]),_19X=B(_wk(_19W[1],_19W[2],_19W[3],_19V[2],_19U[1],_19U[2],_19U[3],_f));return [0,E(_19X[1]),_19X[2]];})]);});},_19J);});},_19Y=[1,_19E],_19Z=[1,_19Y,_f],_1a0=[1,_19Z,_19z],_1a1=new T(function(){return B(unCStr("number"));}),_1a2=[1,_1a1,_f],_1a3=new T(function(){return B(err(_E9));}),_1a4=new T(function(){return B(err(_E7));}),_1a5=new T(function(){return B(_NK(_O6,_Nx,_Oc));}),_1a6=function(_1a7){return function(_1a8,_1a9,_1aa,_1ab,_1ac){return new F(function(){return A(_1ab,[new T(function(){var _1ad=B(_Oh(B(_Ec(_1a5,_1a7))));return _1ad[0]==0?E(_1a4):E(_1ad[2])[0]==0?E(_1ad[1]):E(_1a3);}),_1a8,new T(function(){return [0,E(E(_1a8)[2]),_f];})]);});};},_1ae=function(_1af,_1ag,_1ah,_1ai,_1aj){return new F(function(){return _xh(_DS,_1af,function(_1ak,_1al,_1am){return new F(function(){return A(_1a6,[_1ak,_1al,_1ag,_1ah,function(_1an,_1ao,_1ap){return new F(function(){return A(_1ag,[_1an,_1ao,new T(function(){return B(_x9(_1am,_1ap));})]);});},function(_1aq){return new F(function(){return A(_1ah,[new T(function(){return B(_x9(_1am,_1aq));})]);});}]);});},_1ah,function(_1ar,_1as,_1at){return new F(function(){return A(_1a6,[_1ar,_1as,_1ag,_1ah,function(_1au,_1av,_1aw){return new F(function(){return A(_1ai,[_1au,_1av,new T(function(){return B(_x9(_1at,_1aw));})]);});},function(_1ax){return new F(function(){return A(_1aj,[new T(function(){return B(_x9(_1at,_1ax));})]);});}]);});},_1aj);});},_1ay=function(_1az,_1aA,_1aB,_1aC,_1aD){return new F(function(){return _1ae(_1az,function(_1aE,_1aF,_1aG){return new F(function(){return A(_1aA,[[1,[0,_,_1aE]],_1aF,new T(function(){var _1aH=E(E(_1aF)[2]),_1aI=E(_1aG),_1aJ=E(_1aI[1]),_1aK=B(_wk(_1aJ[1],_1aJ[2],_1aJ[3],_1aI[2],_1aH[1],_1aH[2],_1aH[3],_f));return [0,E(_1aK[1]),_1aK[2]];})]);});},_1aB,function(_1aL,_1aM,_1aN){return new F(function(){return A(_1aC,[[1,[0,_,_1aL]],_1aM,new T(function(){var _1aO=E(E(_1aM)[2]),_1aP=_1aO[1],_1aQ=_1aO[2],_1aR=_1aO[3],_1aS=E(_1aN),_1aT=E(_1aS[1]),_1aU=_1aT[2],_1aV=_1aT[3],_1aW=E(_1aS[2]);if(!_1aW[0]){switch(B(_wc(_1aT[1],_1aP))){case 0:var _1aX=[0,E(_1aO),_f];break;case 1:if(_1aU>=_1aQ){if(_1aU!=_1aQ){var _1aY=[0,E(_1aT),_f];}else{if(_1aV>=_1aR){var _1aZ=_1aV!=_1aR?[0,E(_1aT),_f]:[0,E(_1aT),_wj];}else{var _1aZ=[0,E(_1aO),_f];}var _1b0=_1aZ,_1aY=_1b0;}var _1b1=_1aY,_1b2=_1b1;}else{var _1b2=[0,E(_1aO),_f];}var _1b3=_1b2,_1aX=_1b3;break;default:var _1aX=[0,E(_1aT),_f];}var _1b4=_1aX;}else{var _1b5=B(_Cz(_1aT,_1aW,_1a2)),_1b6=E(_1b5[1]),_1b7=B(_wk(_1b6[1],_1b6[2],_1b6[3],_1b5[2],_1aP,_1aQ,_1aR,_f)),_1b4=[0,E(_1b7[1]),_1b7[2]];}var _1b8=_1b4,_1b9=_1b8,_1ba=_1b9,_1bb=_1ba;return _1bb;})]);});},function(_1bc){return new F(function(){return A(_1aD,[new T(function(){var _1bd=E(_1bc),_1be=B(_Cz(_1bd[1],_1bd[2],_1a2));return [0,E(_1be[1]),_1be[2]];})]);});});});},_1bf=new T(function(){return B(unCStr("P_"));}),_1bg=function(_1bh,_1bi,_1bj,_1bk,_1bl){return new F(function(){return _17V(_E4,_1bf,_1bh,function(_1bm,_1bn,_1bo){return new F(function(){return _1ay(_1bn,_1bi,_1bj,function(_1bp,_1bq,_1br){return new F(function(){return A(_1bi,[_1bp,_1bq,new T(function(){return B(_x9(_1bo,_1br));})]);});},function(_1bs){return new F(function(){return A(_1bj,[new T(function(){return B(_x9(_1bo,_1bs));})]);});});});},_1bj,function(_1bt,_1bu,_1bv){return new F(function(){return _1ay(_1bu,_1bi,_1bj,function(_1bw,_1bx,_1by){return new F(function(){return A(_1bk,[_1bw,_1bx,new T(function(){return B(_x9(_1bv,_1by));})]);});},function(_1bz){return new F(function(){return A(_1bl,[new T(function(){return B(_x9(_1bv,_1bz));})]);});});});},_1bl);});},_1bA=[0,41],_1bB=new T(function(){return B(_Db(_E4,_1bA));}),_1bC=function(_1bD,_1bE,_1bF,_1bG,_1bH,_1bI){return new F(function(){return A(_1bB,[_1bE,function(_1bJ,_1bK,_1bL){return new F(function(){return A(_1bF,[_1bD,_1bK,new T(function(){var _1bM=E(E(_1bK)[2]),_1bN=E(_1bL),_1bO=E(_1bN[1]),_1bP=B(_wk(_1bO[1],_1bO[2],_1bO[3],_1bN[2],_1bM[1],_1bM[2],_1bM[3],_f));return [0,E(_1bP[1]),_1bP[2]];})]);});},_1bG,function(_1bQ,_1bR,_1bS){return new F(function(){return A(_1bH,[_1bD,_1bR,new T(function(){var _1bT=E(E(_1bR)[2]),_1bU=E(_1bS),_1bV=E(_1bU[1]),_1bW=B(_wk(_1bV[1],_1bV[2],_1bV[3],_1bU[2],_1bT[1],_1bT[2],_1bT[3],_f));return [0,E(_1bW[1]),_1bW[2]];})]);});},_1bI]);});},_1bX=function(_1bY,_1bZ,_1c0,_1c1,_1c2){return new F(function(){return A(_1c3,[_1bY,function(_1c4,_1c5,_1c6){return new F(function(){return _1bC(_1c4,_1c5,_1bZ,_1c0,function(_1c7,_1c8,_1c9){return new F(function(){return A(_1bZ,[_1c7,_1c8,new T(function(){return B(_x9(_1c6,_1c9));})]);});},function(_1ca){return new F(function(){return A(_1c0,[new T(function(){return B(_x9(_1c6,_1ca));})]);});});});},_1c0,function(_1cb,_1cc,_1cd){return new F(function(){return _1bC(_1cb,_1cc,_1bZ,_1c0,function(_1ce,_1cf,_1cg){return new F(function(){return A(_1c1,[_1ce,_1cf,new T(function(){return B(_x9(_1cd,_1cg));})]);});},function(_1ch){return new F(function(){return A(_1c2,[new T(function(){return B(_x9(_1cd,_1ch));})]);});});});},_1c2]);});},_1ci=[0,40],_1cj=new T(function(){return B(_Db(_E4,_1ci));}),_1ck=function(_1cl,_1cm,_1cn,_1co,_1cp){var _1cq=function(_1cr){return new F(function(){return _1bg(_1cl,_1cm,_1cn,function(_1cs,_1ct,_1cu){return new F(function(){return A(_1co,[_1cs,_1ct,new T(function(){return B(_x9(_1cr,_1cu));})]);});},function(_1cv){return new F(function(){return A(_1cp,[new T(function(){return B(_x9(_1cr,_1cv));})]);});});});};return new F(function(){return A(_1cj,[_1cl,function(_1cw,_1cx,_1cy){return new F(function(){return _1bX(_1cx,_1cm,_1cn,function(_1cz,_1cA,_1cB){return new F(function(){return A(_1cm,[_1cz,_1cA,new T(function(){return B(_x9(_1cy,_1cB));})]);});},function(_1cC){return new F(function(){return A(_1cn,[new T(function(){return B(_x9(_1cy,_1cC));})]);});});});},_1cn,function(_1cD,_1cE,_1cF){return new F(function(){return _1bX(_1cE,_1cm,_1cn,function(_1cG,_1cH,_1cI){return new F(function(){return A(_1co,[_1cG,_1cH,new T(function(){return B(_x9(_1cF,_1cI));})]);});},function(_1cJ){return new F(function(){return _1cq(new T(function(){return B(_x9(_1cF,_1cJ));}));});});});},_1cq]);});},_1c3=new T(function(){return B(_105(_1ck,_1a0));}),_1cK=function(_1cL,_1cM,_1cN,_1cO,_1cP){return new F(function(){return A(_1c3,[_1cL,function(_1cQ,_1cR,_1cS){return new F(function(){return _Yf(_1cQ,_1cR,_1cM,_1cN,function(_1cT,_1cU,_1cV){return new F(function(){return A(_1cM,[_1cT,_1cU,new T(function(){return B(_x9(_1cS,_1cV));})]);});},function(_1cW){return new F(function(){return A(_1cN,[new T(function(){return B(_x9(_1cS,_1cW));})]);});});});},_1cN,function(_1cX,_1cY,_1cZ){return new F(function(){return _Yf(_1cX,_1cY,_1cM,_1cN,function(_1d0,_1d1,_1d2){return new F(function(){return A(_1cO,[_1d0,_1d1,new T(function(){return B(_x9(_1cZ,_1d2));})]);});},function(_1d3){return new F(function(){return A(_1cP,[new T(function(){return B(_x9(_1cZ,_1d3));})]);});});});},_1cP]);});},_1d4=function(_1d5,_1d6,_1d7,_1d8,_1d9){return new F(function(){return _xU(_Cg,_1d5,function(_1da,_1db,_1dc){return new F(function(){return _1cK(_1db,_1d6,_1d7,function(_1dd,_1de,_1df){return new F(function(){return A(_1d6,[_1dd,_1de,new T(function(){return B(_x9(_1dc,_1df));})]);});},function(_1dg){return new F(function(){return A(_1d7,[new T(function(){return B(_x9(_1dc,_1dg));})]);});});});},_1d7,function(_1dh,_1di,_1dj){return new F(function(){return _1cK(_1di,_1d6,_1d7,function(_1dk,_1dl,_1dm){return new F(function(){return A(_1d8,[_1dk,_1dl,new T(function(){return B(_x9(_1dj,_1dm));})]);});},function(_1dn){return new F(function(){return A(_1d9,[new T(function(){return B(_x9(_1dj,_1dn));})]);});});});});});},_1do=function(_1dp,_1dq,_1dr,_1ds,_1dt,_1du,_1dv,_1dw){var _1dx=E(_1dp);if(!_1dx[0]){return new F(function(){return A(_1dw,[[0,E([0,_1dq,_1dr,_1ds]),_zB]]);});}else{var _1dy=_1dx[1];if(!B(_83(_BW,_1dy,_QJ))){return new F(function(){return A(_1dw,[[0,E([0,_1dq,_1dr,_1ds]),[1,[0,E([1,_zy,new T(function(){return B(_Bo([1,_1dy,_f],_zz));})])],_f]]]);});}else{var _1dz=function(_1dA,_1dB,_1dC,_1dD){var _1dE=[0,E([0,_1dA,_1dB,_1dC]),_f],_1dF=[0,E([0,_1dA,_1dB,_1dC]),_wj];return new F(function(){return _xU(_Rg,[0,_1dx[2],E(_1dD),E(_1dt)],function(_1dG,_1dH,_1dI){return new F(function(){return _1d4(_1dH,_1du,_1dv,function(_1dJ,_1dK,_1dL){return new F(function(){return A(_1du,[_1dJ,_1dK,new T(function(){return B(_x9(_1dI,_1dL));})]);});},function(_1dM){return new F(function(){return A(_1dv,[new T(function(){return B(_x9(_1dI,_1dM));})]);});});});},_1dv,function(_1dN,_1dO,_1dP){return new F(function(){return _1d4(_1dO,_1du,_1dv,function(_1dQ,_1dR,_1dS){return new F(function(){return A(_1du,[_1dQ,_1dR,new T(function(){var _1dT=E(_1dP),_1dU=E(_1dT[1]),_1dV=E(_1dS),_1dW=E(_1dV[1]),_1dX=B(_wk(_1dU[1],_1dU[2],_1dU[3],_1dT[2],_1dW[1],_1dW[2],_1dW[3],_1dV[2])),_1dY=E(_1dX[1]),_1dZ=_1dY[2],_1e0=_1dY[3],_1e1=E(_1dX[2]);if(!_1e1[0]){switch(B(_wc(_1dA,_1dY[1]))){case 0:var _1e2=[0,E(_1dY),_f];break;case 1:if(_1dB>=_1dZ){if(_1dB!=_1dZ){var _1e3=E(_1dE);}else{if(_1dC>=_1e0){var _1e4=_1dC!=_1e0?E(_1dE):E(_1dF);}else{var _1e4=[0,E(_1dY),_f];}var _1e5=_1e4,_1e3=_1e5;}var _1e6=_1e3,_1e7=_1e6;}else{var _1e7=[0,E(_1dY),_f];}var _1e8=_1e7,_1e2=_1e8;break;default:var _1e2=E(_1dE);}var _1e9=_1e2;}else{var _1e9=[0,E(_1dY),_1e1];}var _1ea=_1e9,_1eb=_1ea,_1ec=_1eb,_1ed=_1ec,_1ee=_1ed,_1ef=_1ee;return _1ef;})]);});},function(_1eg){return new F(function(){return A(_1dv,[new T(function(){var _1eh=E(_1dP),_1ei=E(_1eh[1]),_1ej=E(_1eg),_1ek=E(_1ej[1]),_1el=B(_wk(_1ei[1],_1ei[2],_1ei[3],_1eh[2],_1ek[1],_1ek[2],_1ek[3],_1ej[2])),_1em=E(_1el[1]),_1en=_1em[2],_1eo=_1em[3],_1ep=E(_1el[2]);if(!_1ep[0]){switch(B(_wc(_1dA,_1em[1]))){case 0:var _1eq=[0,E(_1em),_f];break;case 1:if(_1dB>=_1en){if(_1dB!=_1en){var _1er=E(_1dE);}else{if(_1dC>=_1eo){var _1es=_1dC!=_1eo?E(_1dE):E(_1dF);}else{var _1es=[0,E(_1em),_f];}var _1et=_1es,_1er=_1et;}var _1eu=_1er,_1ev=_1eu;}else{var _1ev=[0,E(_1em),_f];}var _1ew=_1ev,_1eq=_1ew;break;default:var _1eq=E(_1dE);}var _1ex=_1eq;}else{var _1ex=[0,E(_1em),_1ep];}var _1ey=_1ex,_1ez=_1ey,_1eA=_1ez,_1eB=_1eA,_1eC=_1eB,_1eD=_1eC;return _1eD;})]);});});});});});};switch(E(E(_1dy)[1])){case 9:var _1eE=(_1ds+8|0)-B(_zC(_1ds-1|0,8))|0;return new F(function(){return _1dz(_1dq,_1dr,_1eE,[0,_1dq,_1dr,_1eE]);});break;case 10:var _1eF=_1dr+1|0;return new F(function(){return _1dz(_1dq,_1eF,1,[0,_1dq,_1eF,1]);});break;default:var _1eG=_1ds+1|0;return new F(function(){return _1dz(_1dq,_1dr,_1eG,[0,_1dq,_1dr,_1eG]);});}}}},_1eH=function(_1eI,_1eJ,_1eK,_1eL,_1eM,_1eN){var _1eO=function(_1eP,_1eQ,_1eR,_1eS,_1eT,_1eU){var _1eV=function(_1eW){var _1eX=[0,[1,[0,_1eI,_1eP,new T(function(){return B(_7U(_Oo,_1eW));})]],_f];return function(_1eY,_1eZ,_1f0,_1f1,_1f2){return new F(function(){return A(_DC,[_1eY,function(_1f3,_1f4,_1f5){return new F(function(){return A(_1eZ,[_1eX,_1f4,new T(function(){var _1f6=E(E(_1f4)[2]),_1f7=E(_1f5),_1f8=E(_1f7[1]),_1f9=B(_wk(_1f8[1],_1f8[2],_1f8[3],_1f7[2],_1f6[1],_1f6[2],_1f6[3],_f));return [0,E(_1f9[1]),_1f9[2]];})]);});},_1f2,function(_1fa,_1fb,_1fc){return new F(function(){return A(_1f1,[_1eX,_1fb,new T(function(){var _1fd=E(E(_1fb)[2]),_1fe=E(_1fc),_1ff=E(_1fe[1]),_1fg=B(_wk(_1ff[1],_1ff[2],_1ff[3],_1fe[2],_1fd[1],_1fd[2],_1fd[3],_f));return [0,E(_1fg[1]),_1fg[2]];})]);});},_1f2]);});};},_1fh=function(_1fi,_1fj,_1fk,_1fl,_1fm){var _1fn=function(_1fo,_1fp,_1fq){return new F(function(){return A(_1eV,[_1fo,_1fp,_1fj,_1fk,function(_1fr,_1fs,_1ft){return new F(function(){return A(_1fl,[_1fr,_1fs,new T(function(){return B(_x9(_1fq,_1ft));})]);});},function(_1fu){return new F(function(){return A(_1fm,[new T(function(){return B(_x9(_1fq,_1fu));})]);});}]);});},_1fv=function(_1fw){return new F(function(){return _1fn(_f,_1fi,new T(function(){var _1fx=E(E(_1fi)[2]),_1fy=E(_1fw),_1fz=E(_1fy[1]),_1fA=B(_wk(_1fz[1],_1fz[2],_1fz[3],_1fy[2],_1fx[1],_1fx[2],_1fx[3],_f));return [0,E(_1fA[1]),_1fA[2]];}));});};return new F(function(){return _yk(_DY,_E6,_1fi,function(_1fB,_1fC,_1fD){return new F(function(){return A(_1eV,[_1fB,_1fC,_1fj,_1fk,function(_1fE,_1fF,_1fG){return new F(function(){return A(_1fj,[_1fE,_1fF,new T(function(){return B(_x9(_1fD,_1fG));})]);});},function(_1fH){return new F(function(){return A(_1fk,[new T(function(){return B(_x9(_1fD,_1fH));})]);});}]);});},_1fv,_1fn,_1fv);});};return new F(function(){return _xU(_Cg,_1eQ,function(_1fI,_1fJ,_1fK){return new F(function(){return _1fh(_1fJ,_1eR,_1eS,function(_1fL,_1fM,_1fN){return new F(function(){return A(_1eR,[_1fL,_1fM,new T(function(){return B(_x9(_1fK,_1fN));})]);});},function(_1fO){return new F(function(){return A(_1eS,[new T(function(){return B(_x9(_1fK,_1fO));})]);});});});},_1eS,function(_1fP,_1fQ,_1fR){return new F(function(){return _1fh(_1fQ,_1eR,_1eS,function(_1fS,_1fT,_1fU){return new F(function(){return A(_1eT,[_1fS,_1fT,new T(function(){return B(_x9(_1fR,_1fU));})]);});},function(_1fV){return new F(function(){return A(_1eU,[new T(function(){return B(_x9(_1fR,_1fV));})]);});});});});});},_1fW=function(_1fX,_1fY,_1fZ,_1g0,_1g1){return new F(function(){return _xh(_PN,_1fX,function(_1g2,_1g3,_1g4){return new F(function(){return _1eO(_1g2,_1g3,_1fY,_1fZ,function(_1g5,_1g6,_1g7){return new F(function(){return A(_1fY,[_1g5,_1g6,new T(function(){return B(_x9(_1g4,_1g7));})]);});},function(_1g8){return new F(function(){return A(_1fZ,[new T(function(){return B(_x9(_1g4,_1g8));})]);});});});},_1g1,function(_1g9,_1ga,_1gb){return new F(function(){return _1eO(_1g9,_1ga,_1fY,_1fZ,function(_1gc,_1gd,_1ge){return new F(function(){return A(_1g0,[_1gc,_1gd,new T(function(){return B(_x9(_1gb,_1ge));})]);});},function(_1gf){return new F(function(){return A(_1g1,[new T(function(){return B(_x9(_1gb,_1gf));})]);});});});},_1g1);});};return new F(function(){return _xU(_Cg,_1eJ,function(_1gg,_1gh,_1gi){return new F(function(){return _1fW(_1gh,_1eK,_1eL,function(_1gj,_1gk,_1gl){return new F(function(){return A(_1eK,[_1gj,_1gk,new T(function(){return B(_x9(_1gi,_1gl));})]);});},function(_1gm){return new F(function(){return A(_1eL,[new T(function(){return B(_x9(_1gi,_1gm));})]);});});});},_1eL,function(_1gn,_1go,_1gp){return new F(function(){return _1fW(_1go,_1eK,_1eL,function(_1gq,_1gr,_1gs){return new F(function(){return A(_1eM,[_1gq,_1gr,new T(function(){return B(_x9(_1gp,_1gs));})]);});},function(_1gt){return new F(function(){return A(_1eN,[new T(function(){return B(_x9(_1gp,_1gt));})]);});});});});});},_1gu=function(_1gv,_1gw,_1gx,_1gy,_1gz){return new F(function(){return A(_1c3,[_1gv,function(_1gA,_1gB,_1gC){return new F(function(){return _1eH(_1gA,_1gB,_1gw,_1gx,function(_1gD,_1gE,_1gF){return new F(function(){return A(_1gw,[_1gD,_1gE,new T(function(){return B(_x9(_1gC,_1gF));})]);});},function(_1gG){return new F(function(){return A(_1gx,[new T(function(){return B(_x9(_1gC,_1gG));})]);});});});},_1gx,function(_1gH,_1gI,_1gJ){return new F(function(){return _1eH(_1gH,_1gI,_1gw,_1gx,function(_1gK,_1gL,_1gM){return new F(function(){return A(_1gy,[_1gK,_1gL,new T(function(){return B(_x9(_1gJ,_1gM));})]);});},function(_1gN){return new F(function(){return A(_1gz,[new T(function(){return B(_x9(_1gJ,_1gN));})]);});});});},_1gz]);});},_1gO=function(_1gP,_1gQ,_1gR,_1gS,_1gT){return new F(function(){return _1gu(_1gP,_1gQ,_1gR,_1gS,function(_1gU){var _1gV=E(_1gP),_1gW=E(_1gV[2]);return new F(function(){return _1do(_1gV[1],_1gW[1],_1gW[2],_1gW[3],_1gV[3],_1gQ,_1gR,function(_1gX){return new F(function(){return A(_1gT,[new T(function(){return B(_x9(_1gU,_1gX));})]);});});});});});},_XN=function(_1gY,_1gZ,_1h0,_1h1,_1h2){return new F(function(){return _xh(_1gO,_1gY,function(_1h3,_1h4,_1h5){return new F(function(){return _Qf(_1h3,_1h4,_1gZ,function(_1h6,_1h7,_1h8){return new F(function(){return A(_1gZ,[_1h6,_1h7,new T(function(){return B(_x9(_1h5,_1h8));})]);});});});},_1h0,function(_1h9,_1ha,_1hb){return new F(function(){return _Qf(_1h9,_1ha,_1gZ,function(_1hc,_1hd,_1he){return new F(function(){return A(_1h1,[_1hc,_1hd,new T(function(){return B(_x9(_1hb,_1he));})]);});});});},_1h2);});},_1hf=new T(function(){return B(unCStr("ADD"));}),_1hg=new T(function(){return B(unCStr("ADJ"));}),_1hh=[0,1],_1hi=[1,_1hh],_1hj=[1,_1hi],_1hk=[0,_1hh],_1hl=[1,_1hk],_1hm=new T(function(){return B(unCStr("DN"));}),_1hn=new T(function(){return B(_bw(_f,_1hm));}),_1ho=new T(function(){return B(unCStr("MTP"));}),_1hp=new T(function(){return B(unCStr("MP"));}),_1hq=new T(function(){return B(unCStr("ID"));}),_1hr=new T(function(){return B(unCStr("CD"));}),_1hs=[0,2],_1ht=[1,_1hs],_1hu=[1,_1ht],_1hv=[0,_1hs],_1hw=[1,_1hv],_1hx=function(_1hy){if(!B(_bw(_1hy,_1hf))){if(!B(_bw(_1hy,_1hg))){if(!B(_bw(_1hy,_1hr))){if(!B(_bw(_1hy,_1hq))){if(!B(_bw(_1hy,_1hp))){if(!B(_bw(_1hy,_1ho))){var _1hz=E(_1hy);return _1hz[0]==0?!E(_1hn)?[0]:E(_1hl):E(E(_1hz[1])[1])==83?E(_1hz[2])[0]==0?E(_1hl):!B(_bw(_1hz,_1hm))?[0]:E(_1hl):!B(_bw(_1hz,_1hm))?[0]:E(_1hl);}else{return E(_1hw);}}else{return E(_1hw);}}else{return E(_1hu);}}else{return E(_1hj);}}else{return E(_1hw);}}else{return E(_1hl);}},_1hA=function(_1hB){return E(E(_1hB)[2]);},_1hC=function(_1hD,_1hE,_1hF){while(1){var _1hG=E(_1hE);if(!_1hG[0]){return E(_1hF)[0]==0?1:0;}else{var _1hH=E(_1hF);if(!_1hH[0]){return 2;}else{var _1hI=B(A(_1hA,[_1hD,_1hG[1],_1hH[1]]));if(_1hI==1){_1hE=_1hG[2];_1hF=_1hH[2];continue;}else{return E(_1hI);}}}}},_1hJ=function(_1hK){return E(E(_1hK)[3]);},_1hL=function(_1hM,_1hN,_1hO,_1hP,_1hQ){switch(B(_1hC(_1hM,_1hN,_1hP))){case 0:return true;case 1:return new F(function(){return A(_1hJ,[_1hM,_1hO,_1hQ]);});break;default:return false;}},_1hR=function(_1hS,_1hT,_1hU,_1hV){var _1hW=E(_1hU),_1hX=E(_1hV);return new F(function(){return _1hL(_1hT,_1hW[1],_1hW[2],_1hX[1],_1hX[2]);});},_1hY=function(_1hZ){return E(E(_1hZ)[6]);},_1i0=function(_1i1,_1i2,_1i3,_1i4,_1i5){switch(B(_1hC(_1i1,_1i2,_1i4))){case 0:return true;case 1:return new F(function(){return A(_1hY,[_1i1,_1i3,_1i5]);});break;default:return false;}},_1i6=function(_1i7,_1i8,_1i9,_1ia){var _1ib=E(_1i9),_1ic=E(_1ia);return new F(function(){return _1i0(_1i8,_1ib[1],_1ib[2],_1ic[1],_1ic[2]);});},_1id=function(_1ie){return E(E(_1ie)[5]);},_1if=function(_1ig,_1ih,_1ii,_1ij,_1ik){switch(B(_1hC(_1ig,_1ih,_1ij))){case 0:return false;case 1:return new F(function(){return A(_1id,[_1ig,_1ii,_1ik]);});break;default:return true;}},_1il=function(_1im,_1in,_1io,_1ip){var _1iq=E(_1io),_1ir=E(_1ip);return new F(function(){return _1if(_1in,_1iq[1],_1iq[2],_1ir[1],_1ir[2]);});},_1is=function(_1it){return E(E(_1it)[4]);},_1iu=function(_1iv,_1iw,_1ix,_1iy,_1iz){switch(B(_1hC(_1iv,_1iw,_1iy))){case 0:return false;case 1:return new F(function(){return A(_1is,[_1iv,_1ix,_1iz]);});break;default:return true;}},_1iA=function(_1iB,_1iC,_1iD,_1iE){var _1iF=E(_1iD),_1iG=E(_1iE);return new F(function(){return _1iu(_1iC,_1iF[1],_1iF[2],_1iG[1],_1iG[2]);});},_1iH=function(_1iI,_1iJ,_1iK,_1iL,_1iM){switch(B(_1hC(_1iI,_1iJ,_1iL))){case 0:return 0;case 1:return new F(function(){return A(_1hA,[_1iI,_1iK,_1iM]);});break;default:return 2;}},_1iN=function(_1iO,_1iP,_1iQ,_1iR){var _1iS=E(_1iQ),_1iT=E(_1iR);return new F(function(){return _1iH(_1iP,_1iS[1],_1iS[2],_1iT[1],_1iT[2]);});},_1iU=function(_1iV,_1iW,_1iX,_1iY){var _1iZ=E(_1iX),_1j0=_1iZ[1],_1j1=_1iZ[2],_1j2=E(_1iY),_1j3=_1j2[1],_1j4=_1j2[2];switch(B(_1hC(_1iW,_1j0,_1j3))){case 0:return [0,_1j3,_1j4];case 1:return !B(A(_1hY,[_1iW,_1j1,_1j4]))?[0,_1j0,_1j1]:[0,_1j3,_1j4];default:return [0,_1j0,_1j1];}},_1j5=function(_1j6,_1j7,_1j8,_1j9){var _1ja=E(_1j8),_1jb=_1ja[1],_1jc=_1ja[2],_1jd=E(_1j9),_1je=_1jd[1],_1jf=_1jd[2];switch(B(_1hC(_1j7,_1jb,_1je))){case 0:return [0,_1jb,_1jc];case 1:return !B(A(_1hY,[_1j7,_1jc,_1jf]))?[0,_1je,_1jf]:[0,_1jb,_1jc];default:return [0,_1je,_1jf];}},_1jg=function(_1jh,_1ji){return [0,_1jh,function(_bu,_bv){return new F(function(){return _1iN(_1jh,_1ji,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1hR(_1jh,_1ji,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1iA(_1jh,_1ji,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1il(_1jh,_1ji,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1i6(_1jh,_1ji,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1iU(_1jh,_1ji,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1j5(_1jh,_1ji,_bu,_bv);});}];},_1jj=function(_1jk,_1jl,_1jm,_1jn){return !B(A(_1jk,[_1jm,_1jn]))?B(_wc(B(A(_1jl,[_1jm,_j4])),B(A(_1jl,[_1jn,_j4]))))==2?false:true:false;},_1jo=function(_1jp,_1jq,_1jr,_1js){return new F(function(){return _1jj(E(_1jp)[1],_1jq,_1jr,_1js);});},_1jt=function(_1ju,_1jv,_1jw,_1jx){return B(_wc(B(A(_1jv,[_1jw,_j4])),B(A(_1jv,[_1jx,_j4]))))==2?false:true;},_1jy=function(_1jz,_1jA,_1jB,_1jC){return !B(A(_1jz,[_1jB,_1jC]))?B(_wc(B(A(_1jA,[_1jB,_j4])),B(A(_1jA,[_1jC,_j4]))))==2?true:false:false;},_1jD=function(_1jE,_1jF,_1jG,_1jH){return new F(function(){return _1jy(E(_1jE)[1],_1jF,_1jG,_1jH);});},_1jI=function(_1jJ,_1jK,_1jL,_1jM){return !B(A(_1jJ,[_1jL,_1jM]))?B(_wc(B(A(_1jK,[_1jL,_j4])),B(A(_1jK,[_1jM,_j4]))))==2?true:false:true;},_1jN=function(_1jO,_1jP,_1jQ,_1jR){return new F(function(){return _1jI(E(_1jO)[1],_1jP,_1jQ,_1jR);});},_1jS=function(_1jT,_1jU,_1jV,_1jW){return !B(A(_1jT,[_1jV,_1jW]))?B(_wc(B(A(_1jU,[_1jV,_j4])),B(A(_1jU,[_1jW,_j4]))))==2?2:0:1;},_1jX=function(_1jY,_1jZ,_1k0,_1k1){return new F(function(){return _1jS(E(_1jY)[1],_1jZ,_1k0,_1k1);});},_1k2=function(_1k3,_1k4,_1k5,_1k6){return B(_wc(B(A(_1k4,[_1k5,_j4])),B(A(_1k4,[_1k6,_j4]))))==2?E(_1k5):E(_1k6);},_1k7=function(_1k8,_1k9,_1ka,_1kb){return B(_wc(B(A(_1k9,[_1ka,_j4])),B(A(_1k9,[_1kb,_j4]))))==2?E(_1kb):E(_1ka);},_1kc=function(_1kd,_1ke){return [0,_1kd,function(_c3,_c4){return new F(function(){return _1jX(_1kd,_1ke,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1jo(_1kd,_1ke,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1jN(_1kd,_1ke,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1jD(_1kd,_1ke,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1jt(_1kd,_1ke,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1k2(_1kd,_1ke,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1k7(_1kd,_1ke,_c3,_c4);});}];},_1kf=function(_1kg,_1kh,_1ki,_1kj,_1kk,_1kl,_1km){var _1kn=function(_1ko,_1kp){return new F(function(){return _ao(_1kg,_1kh,_1ki,_1kk,_1kj,_1km,_1kl,_1ko);});};return function(_1kq,_1kr){var _1ks=E(_1kq);if(!_1ks[0]){var _1kt=E(_1kr);return _1kt[0]==0?B(_wc(B(_aa(_1ks[1])),B(_aa(_1kt[1]))))==2?false:true:true;}else{var _1ku=E(_1kr);return _1ku[0]==0?false:B(_1hC(new T(function(){return B(_1kc(new T(function(){return B(_j9(_1kn));}),_1kn));}),_1ks[1],_1ku[1]))==2?false:true;}};},_1kv=function(_1kw,_1kx,_1ky,_1kz,_1kA,_1kB,_1kC,_1kD,_1kE,_1kF){return !B(A(_1kf,[_1kx,_1ky,_1kz,_1kA,_1kB,_1kC,_1kD,_1kE,_1kF]))?E(_1kE):E(_1kF);},_1kG=function(_1kH,_1kI,_1kJ,_1kK,_1kL,_1kM,_1kN,_1kO,_1kP,_1kQ){return !B(A(_1kf,[_1kI,_1kJ,_1kK,_1kL,_1kM,_1kN,_1kO,_1kP,_1kQ]))?E(_1kQ):E(_1kP);},_1kR=function(_1kS,_1kT,_1kU,_1kV,_1kW,_1kX,_1kY){var _1kZ=function(_1l0,_1l1){return new F(function(){return _ao(_1kS,_1kT,_1kU,_1kW,_1kV,_1kY,_1kX,_1l0);});};return function(_1l2,_1l3){var _1l4=E(_1l2);if(!_1l4[0]){var _1l5=_1l4[1],_1l6=E(_1l3);if(!_1l6[0]){var _1l7=_1l6[1];return B(_cj(_1l5,_1l7,_61))[0]==0?B(_wc(B(_aa(_1l5)),B(_aa(_1l7))))==2?false:true:false;}else{return true;}}else{var _1l8=E(_1l3);return _1l8[0]==0?false:B(_1hC(new T(function(){return B(_1kc(new T(function(){return B(_j9(_1kZ));}),_1kZ));}),_1l4[1],_1l8[1]))==0?true:false;}};},_1l9=function(_1la,_1lb,_1lc,_1ld,_1le,_1lf,_1lg){var _1lh=function(_1li,_1lj){return new F(function(){return _ao(_1la,_1lb,_1lc,_1le,_1ld,_1lg,_1lf,_1li);});};return function(_1lk,_1ll){var _1lm=E(_1lk);if(!_1lm[0]){var _1ln=_1lm[1],_1lo=E(_1ll);if(!_1lo[0]){var _1lp=_1lo[1];return B(_cj(_1ln,_1lp,_61))[0]==0?B(_wc(B(_aa(_1ln)),B(_aa(_1lp))))==2?true:false:false;}else{return false;}}else{var _1lq=E(_1ll);return _1lq[0]==0?true:B(_1hC(new T(function(){return B(_1kc(new T(function(){return B(_j9(_1lh));}),_1lh));}),_1lm[1],_1lq[1]))==2?true:false;}};},_1lr=function(_1ls,_1lt,_1lu,_1lv,_1lw,_1lx,_1ly){var _1lz=function(_1lA,_1lB){return new F(function(){return _ao(_1ls,_1lt,_1lu,_1lw,_1lv,_1ly,_1lx,_1lA);});};return function(_1lC,_1lD){var _1lE=E(_1lC);if(!_1lE[0]){var _1lF=_1lE[1],_1lG=E(_1lD);if(!_1lG[0]){var _1lH=_1lG[1];return B(_cj(_1lF,_1lH,_61))[0]==0?B(_wc(B(_aa(_1lF)),B(_aa(_1lH))))==2?true:false:true;}else{return false;}}else{var _1lI=E(_1lD);return _1lI[0]==0?true:B(_1hC(new T(function(){return B(_1kc(new T(function(){return B(_j9(_1lz));}),_1lz));}),_1lE[1],_1lI[1]))==0?false:true;}};},_1lJ=function(_1lK,_1lL,_1lM,_1lN,_1lO,_1lP,_1lQ){var _1lR=function(_1lS,_1lT){return new F(function(){return _ao(_1lK,_1lL,_1lM,_1lO,_1lN,_1lQ,_1lP,_1lS);});};return function(_1lU,_1lV){var _1lW=E(_1lU);if(!_1lW[0]){var _1lX=_1lW[1],_1lY=E(_1lV);if(!_1lY[0]){var _1lZ=_1lY[1];return B(_cj(_1lX,_1lZ,_61))[0]==0?B(_wc(B(_aa(_1lX)),B(_aa(_1lZ))))==2?2:0:1;}else{return 0;}}else{var _1m0=E(_1lV);return _1m0[0]==0?2:B(_1hC(new T(function(){return B(_1kc(new T(function(){return B(_j9(_1lR));}),_1lR));}),_1lW[1],_1m0[1]));}};},_1m1=function(_1m2,_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9){return [0,_1m2,new T(function(){return B(_1lJ(_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9));}),new T(function(){return B(_1kR(_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9));}),new T(function(){return B(_1lr(_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9));}),new T(function(){return B(_1l9(_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9));}),new T(function(){return B(_1kf(_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9));}),function(_c3,_c4){return new F(function(){return _1kv(_1m2,_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9,_c3,_c4);});},function(_c3,_c4){return new F(function(){return _1kG(_1m2,_1m3,_1m4,_1m5,_1m6,_1m7,_1m8,_1m9,_c3,_c4);});}];},_1ma=new T(function(){return B(_bV(_6y,_6p,_6y,_6y,_6v,_62,_6N));}),_1mb=new T(function(){return B(_1m1(_1ma,_6y,_6p,_6y,_6y,_6v,_6N,_62));}),_1mc=new T(function(){return B(_ch(_1ma));}),_1md=new T(function(){return B(_1jg(_1mc,_1mb));}),_1me=function(_1mf,_1mg,_1mh,_1mi){var _1mj=E(_1mh),_1mk=E(_1mi);return new F(function(){return _1hL(_1mg,_1mj[1],_1mj[2],_1mk[1],_1mk[2]);});},_1ml=function(_1mm,_1mn,_1mo,_1mp){var _1mq=E(_1mo),_1mr=E(_1mp);return new F(function(){return _1i0(_1mn,_1mq[1],_1mq[2],_1mr[1],_1mr[2]);});},_1ms=function(_1mt,_1mu,_1mv,_1mw){var _1mx=E(_1mv),_1my=E(_1mw);return new F(function(){return _1if(_1mu,_1mx[1],_1mx[2],_1my[1],_1my[2]);});},_1mz=function(_1mA,_1mB,_1mC,_1mD){var _1mE=E(_1mC),_1mF=E(_1mD);return new F(function(){return _1iu(_1mB,_1mE[1],_1mE[2],_1mF[1],_1mF[2]);});},_1mG=function(_1mH,_1mI,_1mJ,_1mK){var _1mL=E(_1mJ),_1mM=E(_1mK);return new F(function(){return _1iH(_1mI,_1mL[1],_1mL[2],_1mM[1],_1mM[2]);});},_1mN=function(_1mO,_1mP,_1mQ,_1mR){var _1mS=E(_1mQ),_1mT=_1mS[1],_1mU=_1mS[2],_1mV=E(_1mR),_1mW=_1mV[1],_1mX=_1mV[2];switch(B(_1hC(_1mP,_1mT,_1mW))){case 0:return [0,_1mW,_1mX];case 1:return !B(A(_1hY,[_1mP,_1mU,_1mX]))?[0,_1mT,_1mU]:[0,_1mW,_1mX];default:return [0,_1mT,_1mU];}},_1mY=function(_1mZ,_1n0,_1n1,_1n2){var _1n3=E(_1n1),_1n4=_1n3[1],_1n5=_1n3[2],_1n6=E(_1n2),_1n7=_1n6[1],_1n8=_1n6[2];switch(B(_1hC(_1n0,_1n4,_1n7))){case 0:return [0,_1n4,_1n5];case 1:return !B(A(_1hY,[_1n0,_1n5,_1n8]))?[0,_1n7,_1n8]:[0,_1n4,_1n5];default:return [0,_1n7,_1n8];}},_1n9=function(_1na,_1nb){return [0,_1na,function(_bu,_bv){return new F(function(){return _1mG(_1na,_1nb,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1me(_1na,_1nb,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1mz(_1na,_1nb,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1ms(_1na,_1nb,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1ml(_1na,_1nb,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1mN(_1na,_1nb,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1mY(_1na,_1nb,_bu,_bv);});}];},_1nc=function(_1nd,_1ne){return B(_wc(_1nd,_1ne))==0?false:true;},_1nf=function(_1ng){return E(E(_1ng)[1]);},_1nh=function(_1ni,_1nj){while(1){var _1nk=(function(_1nl,_1nm){var _1nn=E(_1nm);if(!_1nn[0]){_1ni=[1,_1nn[2],new T(function(){return B(_1nh(_1nl,_1nn[4]));})];_1nj=_1nn[3];return null;}else{return E(_1nl);}})(_1ni,_1nj);if(_1nk!=null){return _1nk;}}},_1no=function(_1np){return new F(function(){return _1nh(_f,_1np);});},_1nq=function(_1nr){return function(_1ns,_1nt){var _1nu=E(_1ns),_1nv=E(_1nt);switch(B(_1hC(new T(function(){return B(_1n9(new T(function(){return B(_bs(new T(function(){return B(_1nf(_1nr));})));}),_1nr));}),B(_1no(_1nu[1])),B(_1no(_1nv[1]))))){case 0:return false;case 1:return new F(function(){return _1nc(_1nu[2],_1nv[2]);});break;default:return true;}};},_1nw=new T(function(){return B(_1nq(_1md));}),_1nx=function(_1ny,_1nz,_1nA){var _1nB=E(_1ny);if(_1nB==1){var _1nC=E(_1nA);return _1nC[0]==0?[0,new T(function(){return [0,1,E(E(_1nz)),E(_qi),E(_qi)];}),_f,_f]:!B(A(_1nw,[_1nz,_1nC[1]]))?[0,new T(function(){return [0,1,E(E(_1nz)),E(_qi),E(_qi)];}),_1nC,_f]:[0,new T(function(){return [0,1,E(E(_1nz)),E(_qi),E(_qi)];}),_f,_1nC];}else{var _1nD=B(_1nx(_1nB>>1,_1nz,_1nA)),_1nE=_1nD[1],_1nF=_1nD[3],_1nG=E(_1nD[2]);if(!_1nG[0]){return [0,_1nE,_f,_1nF];}else{var _1nH=_1nG[1],_1nI=E(_1nG[2]);if(!_1nI[0]){return [0,new T(function(){return B(_rF(_1nH,_1nE));}),_f,_1nF];}else{var _1nJ=_1nI[1];if(!B(A(_1nw,[_1nH,_1nJ]))){var _1nK=B(_1nx(_1nB>>1,_1nJ,_1nI[2]));return [0,new T(function(){return B(_sj(_1nH,_1nE,_1nK[1]));}),_1nK[2],_1nK[3]];}else{return [0,_1nE,_f,_1nG];}}}}},_1nL=function(_1nM,_1nN){return B(_wc(_1nM,_1nN))==2?false:true;},_1nO=function(_1nP){return function(_1nQ,_1nR){var _1nS=E(_1nQ),_1nT=E(_1nR);switch(B(_1hC(new T(function(){return B(_1n9(new T(function(){return B(_bs(new T(function(){return B(_1nf(_1nP));})));}),_1nP));}),B(_1no(_1nS[1])),B(_1no(_1nT[1]))))){case 0:return true;case 1:return new F(function(){return _1nL(_1nS[2],_1nT[2]);});break;default:return false;}};},_1nU=function(_1nV,_1nW,_1nX,_1nY){return !B(A(_1nO,[_1nW,_1nX,_1nY]))?E(_1nX):E(_1nY);},_1nZ=function(_1o0,_1o1,_1o2,_1o3){return !B(A(_1nO,[_1o1,_1o2,_1o3]))?E(_1o3):E(_1o2);},_1o4=function(_1o5,_1o6){return B(_wc(_1o5,_1o6))==0?true:false;},_1o7=function(_1o8){return function(_1o9,_1oa){var _1ob=E(_1o9),_1oc=E(_1oa);switch(B(_1hC(new T(function(){return B(_1n9(new T(function(){return B(_bs(new T(function(){return B(_1nf(_1o8));})));}),_1o8));}),B(_1no(_1ob[1])),B(_1no(_1oc[1]))))){case 0:return true;case 1:return new F(function(){return _1o4(_1ob[2],_1oc[2]);});break;default:return false;}};},_1od=function(_1oe,_1of){return B(_wc(_1oe,_1of))==2?true:false;},_1og=function(_1oh){return function(_1oi,_1oj){var _1ok=E(_1oi),_1ol=E(_1oj);switch(B(_1hC(new T(function(){return B(_1n9(new T(function(){return B(_bs(new T(function(){return B(_1nf(_1oh));})));}),_1oh));}),B(_1no(_1ok[1])),B(_1no(_1ol[1]))))){case 0:return false;case 1:return new F(function(){return _1od(_1ok[2],_1ol[2]);});break;default:return true;}};},_1om=function(_1on){return function(_1oo,_1op){var _1oq=E(_1oo),_1or=E(_1op);switch(B(_1hC(new T(function(){return B(_1n9(new T(function(){return B(_bs(new T(function(){return B(_1nf(_1on));})));}),_1on));}),B(_1no(_1oq[1])),B(_1no(_1or[1]))))){case 0:return 0;case 1:return new F(function(){return _wc(_1oq[2],_1or[2]);});break;default:return 2;}};},_1os=function(_1ot,_1ou){return [0,_1ot,new T(function(){return B(_1om(_1ou));}),new T(function(){return B(_1o7(_1ou));}),new T(function(){return B(_1nq(_1ou));}),new T(function(){return B(_1og(_1ou));}),new T(function(){return B(_1nO(_1ou));}),function(_bu,_bv){return new F(function(){return _1nU(_1ot,_1ou,_bu,_bv);});},function(_bu,_bv){return new F(function(){return _1nZ(_1ot,_1ou,_bu,_bv);});}];},_1ov=function(_1ow,_1ox,_1oy){var _1oz=function(_1oA){var _1oB=function(_1oC){if(_1oA!=_1oC){return false;}else{return new F(function(){return _b4(_1ow,B(_1nh(_f,_1ox)),B(_1nh(_f,_1oy)));});}},_1oD=E(_1oy);return _1oD[0]==0?B(_1oB(_1oD[1])):B(_1oB(0));},_1oE=E(_1ox);return _1oE[0]==0?B(_1oz(_1oE[1])):B(_1oz(0));},_1oF=function(_1oG,_1oH,_1oI,_1oJ,_1oK){return !B(_1ov(new T(function(){return B(_bs(_1oG));}),_1oH,_1oJ))?true:!B(_bw(_1oI,_1oK))?true:false;},_1oL=function(_1oM,_1oN,_1oO){var _1oP=E(_1oN),_1oQ=E(_1oO);return new F(function(){return _1oF(_1oM,_1oP[1],_1oP[2],_1oQ[1],_1oQ[2]);});},_1oR=function(_1oS){return function(_1oT,_1oU){var _1oV=E(_1oT),_1oW=E(_1oU);return !B(_1ov(new T(function(){return B(_bs(_1oS));}),_1oV[1],_1oW[1]))?false:B(_bw(_1oV[2],_1oW[2]));};},_1oX=function(_1oY){return [0,new T(function(){return B(_1oR(_1oY));}),function(_bu,_bv){return new F(function(){return _1oL(_1oY,_bu,_bv);});}];},_1oZ=new T(function(){return B(_1oX(_1mc));}),_1p0=new T(function(){return B(_1os(_1oZ,_1md));}),_1p1=function(_1p2,_1p3,_1p4){var _1p5=E(_1p3),_1p6=E(_1p4);if(!_1p6[0]){var _1p7=_1p6[2],_1p8=_1p6[3],_1p9=_1p6[4];switch(B(A(_1hA,[_1p2,_1p5,_1p7]))){case 0:return new F(function(){return _qn(_1p7,B(_1p1(_1p2,_1p5,_1p8)),_1p9);});break;case 1:return [0,_1p6[1],E(_1p5),E(_1p8),E(_1p9)];default:return new F(function(){return _qZ(_1p7,_1p8,B(_1p1(_1p2,_1p5,_1p9)));});}}else{return [0,1,E(_1p5),E(_qi),E(_qi)];}},_1pa=function(_1pb,_1pc){while(1){var _1pd=E(_1pc);if(!_1pd[0]){return E(_1pb);}else{var _1pe=B(_1p1(_1p0,_1pd[1],_1pb));_1pc=_1pd[2];_1pb=_1pe;continue;}}},_1pf=function(_1pg,_1ph,_1pi){return new F(function(){return _1pa(B(_1p1(_1p0,_1ph,_1pg)),_1pi);});},_1pj=function(_1pk,_1pl,_1pm){while(1){var _1pn=E(_1pm);if(!_1pn[0]){return E(_1pl);}else{var _1po=_1pn[1],_1pp=E(_1pn[2]);if(!_1pp[0]){return new F(function(){return _rF(_1po,_1pl);});}else{var _1pq=_1pp[1];if(!B(A(_1nw,[_1po,_1pq]))){var _1pr=B(_1nx(_1pk,_1pq,_1pp[2])),_1ps=_1pr[1],_1pt=E(_1pr[3]);if(!_1pt[0]){var _1pu=_1pk<<1,_1pv=B(_sj(_1po,_1pl,_1ps));_1pm=_1pr[2];_1pk=_1pu;_1pl=_1pv;continue;}else{return new F(function(){return _1pf(B(_sj(_1po,_1pl,_1ps)),_1pt[1],_1pt[2]);});}}else{return new F(function(){return _1pf(_1pl,_1po,_1pp);});}}}}},_1pw=function(_1px,_1py,_1pz,_1pA){var _1pB=E(_1pA);if(!_1pB[0]){return new F(function(){return _rF(_1pz,_1py);});}else{var _1pC=_1pB[1];if(!B(A(_1nw,[_1pz,_1pC]))){var _1pD=B(_1nx(_1px,_1pC,_1pB[2])),_1pE=_1pD[1],_1pF=E(_1pD[3]);if(!_1pF[0]){return new F(function(){return _1pj(_1px<<1,B(_sj(_1pz,_1py,_1pE)),_1pD[2]);});}else{return new F(function(){return _1pf(B(_sj(_1pz,_1py,_1pE)),_1pF[1],_1pF[2]);});}}else{return new F(function(){return _1pf(_1py,_1pz,_1pB);});}}},_1pG=function(_1pH){var _1pI=E(_1pH);if(!_1pI[0]){return [1];}else{var _1pJ=_1pI[1],_1pK=E(_1pI[2]);if(!_1pK[0]){return [0,1,E(E(_1pJ)),E(_qi),E(_qi)];}else{var _1pL=_1pK[1],_1pM=_1pK[2];if(!B(A(_1nw,[_1pJ,_1pL]))){return new F(function(){return _1pw(1,[0,1,E(E(_1pJ)),E(_qi),E(_qi)],_1pL,_1pM);});}else{return new F(function(){return _1pf([0,1,E(E(_1pJ)),E(_qi),E(_qi)],_1pL,_1pM);});}}}},_1pN=new T(function(){return B(_1lr(_6y,_6p,_6y,_6y,_6v,_6N,_62));}),_1pO=function(_1pP,_1pQ,_1pR,_1pS,_1pT){var _1pU=E(_1pP);if(_1pU==1){var _1pV=E(_1pT);if(!_1pV[0]){return [0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_f,_f];}else{var _1pW=E(_1pV[1]);switch(B(_1hC(_1md,_1pQ,_1pW[1]))){case 0:return [0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_1pV,_f];case 1:var _1pX=E(_1pW[2]);switch(B(_1hC(_1mb,_1pR,_1pX[1]))){case 0:return [0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_1pV,_f];case 1:return !B(A(_1pN,[_1pS,_1pX[2]]))?[0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_1pV,_f]:[0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_f,_1pV];default:return [0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_f,_1pV];}break;default:return [0,[0,1,E([0,_1pQ,[0,_1pR,_1pS]]),E(_qi),E(_qi)],_f,_1pV];}}}else{var _1pY=B(_1pO(_1pU>>1,_1pQ,_1pR,_1pS,_1pT)),_1pZ=_1pY[1],_1q0=_1pY[3],_1q1=E(_1pY[2]);if(!_1q1[0]){return [0,_1pZ,_f,_1q0];}else{var _1q2=_1q1[1],_1q3=E(_1q1[2]);if(!_1q3[0]){return [0,new T(function(){return B(_rF(_1q2,_1pZ));}),_f,_1q0];}else{var _1q4=_1q3[2],_1q5=E(_1q2),_1q6=E(_1q3[1]),_1q7=_1q6[1],_1q8=_1q6[2];switch(B(_1hC(_1md,_1q5[1],_1q7))){case 0:var _1q9=B(_1qa(_1pU>>1,_1q7,_1q8,_1q4));return [0,new T(function(){return B(_sj(_1q5,_1pZ,_1q9[1]));}),_1q9[2],_1q9[3]];case 1:var _1qb=E(_1q5[2]),_1qc=E(_1q8),_1qd=_1qc[1],_1qe=_1qc[2];switch(B(_1hC(_1mb,_1qb[1],_1qd))){case 0:var _1qf=B(_1pO(_1pU>>1,_1q7,_1qd,_1qe,_1q4));return [0,new T(function(){return B(_sj(_1q5,_1pZ,_1qf[1]));}),_1qf[2],_1qf[3]];case 1:if(!B(A(_1pN,[_1qb[2],_1qe]))){var _1qg=B(_1pO(_1pU>>1,_1q7,_1qd,_1qe,_1q4));return [0,new T(function(){return B(_sj(_1q5,_1pZ,_1qg[1]));}),_1qg[2],_1qg[3]];}else{return [0,_1pZ,_f,_1q1];}break;default:return [0,_1pZ,_f,_1q1];}break;default:return [0,_1pZ,_f,_1q1];}}}}},_1qa=function(_1qh,_1qi,_1qj,_1qk){var _1ql=E(_1qh);if(_1ql==1){var _1qm=E(_1qk);if(!_1qm[0]){return [0,[0,1,E([0,_1qi,_1qj]),E(_qi),E(_qi)],_f,_f];}else{var _1qn=E(_1qm[1]);switch(B(_1hC(_1md,_1qi,_1qn[1]))){case 0:return [0,[0,1,E([0,_1qi,_1qj]),E(_qi),E(_qi)],_1qm,_f];case 1:var _1qo=E(_1qj),_1qp=E(_1qn[2]);switch(B(_1hC(_1mb,_1qo[1],_1qp[1]))){case 0:return [0,[0,1,E([0,_1qi,_1qo]),E(_qi),E(_qi)],_1qm,_f];case 1:return !B(A(_1pN,[_1qo[2],_1qp[2]]))?[0,[0,1,E([0,_1qi,_1qo]),E(_qi),E(_qi)],_1qm,_f]:[0,[0,1,E([0,_1qi,_1qo]),E(_qi),E(_qi)],_f,_1qm];default:return [0,[0,1,E([0,_1qi,_1qo]),E(_qi),E(_qi)],_f,_1qm];}break;default:return [0,[0,1,E([0,_1qi,_1qj]),E(_qi),E(_qi)],_f,_1qm];}}}else{var _1qq=B(_1qa(_1ql>>1,_1qi,_1qj,_1qk)),_1qr=_1qq[1],_1qs=_1qq[3],_1qt=E(_1qq[2]);if(!_1qt[0]){return [0,_1qr,_f,_1qs];}else{var _1qu=_1qt[1],_1qv=E(_1qt[2]);if(!_1qv[0]){return [0,new T(function(){return B(_rF(_1qu,_1qr));}),_f,_1qs];}else{var _1qw=_1qv[2],_1qx=E(_1qu),_1qy=E(_1qv[1]),_1qz=_1qy[1],_1qA=_1qy[2];switch(B(_1hC(_1md,_1qx[1],_1qz))){case 0:var _1qB=B(_1qa(_1ql>>1,_1qz,_1qA,_1qw));return [0,new T(function(){return B(_sj(_1qx,_1qr,_1qB[1]));}),_1qB[2],_1qB[3]];case 1:var _1qC=E(_1qx[2]),_1qD=E(_1qA),_1qE=_1qD[1],_1qF=_1qD[2];switch(B(_1hC(_1mb,_1qC[1],_1qE))){case 0:var _1qG=B(_1pO(_1ql>>1,_1qz,_1qE,_1qF,_1qw));return [0,new T(function(){return B(_sj(_1qx,_1qr,_1qG[1]));}),_1qG[2],_1qG[3]];case 1:if(!B(A(_1pN,[_1qC[2],_1qF]))){var _1qH=B(_1pO(_1ql>>1,_1qz,_1qE,_1qF,_1qw));return [0,new T(function(){return B(_sj(_1qx,_1qr,_1qH[1]));}),_1qH[2],_1qH[3]];}else{return [0,_1qr,_f,_1qt];}break;default:return [0,_1qr,_f,_1qt];}break;default:return [0,_1qr,_f,_1qt];}}}}},_1qI=new T(function(){return B(_1lJ(_6y,_6p,_6y,_6y,_6v,_6N,_62));}),_1qJ=function(_1qK,_1qL,_1qM,_1qN){var _1qO=E(_1qN);if(!_1qO[0]){var _1qP=_1qO[3],_1qQ=_1qO[4],_1qR=E(_1qO[2]);switch(B(_1hC(_1md,_1qK,_1qR[1]))){case 0:return new F(function(){return _qn(_1qR,B(_1qJ(_1qK,_1qL,_1qM,_1qP)),_1qQ);});break;case 1:var _1qS=E(_1qR[2]);switch(B(_1hC(_1mb,_1qL,_1qS[1]))){case 0:return new F(function(){return _qn(_1qR,B(_1qJ(_1qK,_1qL,_1qM,_1qP)),_1qQ);});break;case 1:switch(B(A(_1qI,[_1qM,_1qS[2]]))){case 0:return new F(function(){return _qn(_1qR,B(_1qJ(_1qK,_1qL,_1qM,_1qP)),_1qQ);});break;case 1:return [0,_1qO[1],E([0,_1qK,[0,_1qL,_1qM]]),E(_1qP),E(_1qQ)];default:return new F(function(){return _qZ(_1qR,_1qP,B(_1qJ(_1qK,_1qL,_1qM,_1qQ)));});}break;default:return new F(function(){return _qZ(_1qR,_1qP,B(_1qJ(_1qK,_1qL,_1qM,_1qQ)));});}break;default:return new F(function(){return _qZ(_1qR,_1qP,B(_1qJ(_1qK,_1qL,_1qM,_1qQ)));});}}else{return [0,1,E([0,_1qK,[0,_1qL,_1qM]]),E(_qi),E(_qi)];}},_1qT=function(_1qU,_1qV,_1qW){var _1qX=E(_1qW);if(!_1qX[0]){var _1qY=_1qX[3],_1qZ=_1qX[4],_1r0=E(_1qX[2]);switch(B(_1hC(_1md,_1qU,_1r0[1]))){case 0:return new F(function(){return _qn(_1r0,B(_1qT(_1qU,_1qV,_1qY)),_1qZ);});break;case 1:var _1r1=E(_1qV),_1r2=_1r1[1],_1r3=_1r1[2],_1r4=E(_1r0[2]);switch(B(_1hC(_1mb,_1r2,_1r4[1]))){case 0:return new F(function(){return _qn(_1r0,B(_1qJ(_1qU,_1r2,_1r3,_1qY)),_1qZ);});break;case 1:switch(B(A(_1qI,[_1r3,_1r4[2]]))){case 0:return new F(function(){return _qn(_1r0,B(_1qJ(_1qU,_1r2,_1r3,_1qY)),_1qZ);});break;case 1:return [0,_1qX[1],E([0,_1qU,_1r1]),E(_1qY),E(_1qZ)];default:return new F(function(){return _qZ(_1r0,_1qY,B(_1qJ(_1qU,_1r2,_1r3,_1qZ)));});}break;default:return new F(function(){return _qZ(_1r0,_1qY,B(_1qJ(_1qU,_1r2,_1r3,_1qZ)));});}break;default:return new F(function(){return _qZ(_1r0,_1qY,B(_1qT(_1qU,_1qV,_1qZ)));});}}else{return [0,1,E([0,_1qU,_1qV]),E(_qi),E(_qi)];}},_1r5=function(_1r6,_1r7){while(1){var _1r8=E(_1r7);if(!_1r8[0]){return E(_1r6);}else{var _1r9=E(_1r8[1]),_1ra=B(_1qT(_1r9[1],_1r9[2],_1r6));_1r7=_1r8[2];_1r6=_1ra;continue;}}},_1rb=function(_1rc,_1rd,_1re,_1rf){return new F(function(){return _1r5(B(_1qT(_1rd,_1re,_1rc)),_1rf);});},_1rg=function(_1rh,_1ri,_1rj){var _1rk=E(_1ri);return new F(function(){return _1r5(B(_1qT(_1rk[1],_1rk[2],_1rh)),_1rj);});},_1rl=function(_1rm,_1rn,_1ro){var _1rp=E(_1ro);if(!_1rp[0]){return E(_1rn);}else{var _1rq=_1rp[1],_1rr=E(_1rp[2]);if(!_1rr[0]){return new F(function(){return _rF(_1rq,_1rn);});}else{var _1rs=E(_1rq),_1rt=_1rs[1],_1ru=_1rs[2],_1rv=E(_1rr[1]),_1rw=_1rv[1],_1rx=_1rv[2],_1ry=function(_1rz){var _1rA=B(_1qa(_1rm,_1rw,_1rx,_1rr[2])),_1rB=_1rA[1],_1rC=E(_1rA[3]);if(!_1rC[0]){return new F(function(){return _1rl(_1rm<<1,B(_sj(_1rs,_1rn,_1rB)),_1rA[2]);});}else{return new F(function(){return _1rg(B(_sj(_1rs,_1rn,_1rB)),_1rC[1],_1rC[2]);});}};switch(B(_1hC(_1md,_1rt,_1rw))){case 0:return new F(function(){return _1ry(_);});break;case 1:var _1rD=E(_1ru),_1rE=E(_1rx);switch(B(_1hC(_1mb,_1rD[1],_1rE[1]))){case 0:return new F(function(){return _1ry(_);});break;case 1:return !B(A(_1pN,[_1rD[2],_1rE[2]]))?B(_1ry(_)):B(_1rb(_1rn,_1rt,_1rD,_1rr));default:return new F(function(){return _1rb(_1rn,_1rt,_1rD,_1rr);});}break;default:return new F(function(){return _1rb(_1rn,_1rt,_1ru,_1rr);});}}}},_1rF=function(_1rG,_1rH,_1rI,_1rJ,_1rK,_1rL){var _1rM=E(_1rL);if(!_1rM[0]){return new F(function(){return _rF([0,_1rI,[0,_1rJ,_1rK]],_1rH);});}else{var _1rN=E(_1rM[1]),_1rO=_1rN[1],_1rP=_1rN[2],_1rQ=function(_1rR){var _1rS=B(_1qa(_1rG,_1rO,_1rP,_1rM[2])),_1rT=_1rS[1],_1rU=E(_1rS[3]);if(!_1rU[0]){return new F(function(){return _1rl(_1rG<<1,B(_sj([0,_1rI,[0,_1rJ,_1rK]],_1rH,_1rT)),_1rS[2]);});}else{return new F(function(){return _1rg(B(_sj([0,_1rI,[0,_1rJ,_1rK]],_1rH,_1rT)),_1rU[1],_1rU[2]);});}};switch(B(_1hC(_1md,_1rI,_1rO))){case 0:return new F(function(){return _1rQ(_);});break;case 1:var _1rV=E(_1rP);switch(B(_1hC(_1mb,_1rJ,_1rV[1]))){case 0:return new F(function(){return _1rQ(_);});break;case 1:return !B(A(_1pN,[_1rK,_1rV[2]]))?B(_1rQ(_)):B(_1rb(_1rH,_1rI,[0,_1rJ,_1rK],_1rM));default:return new F(function(){return _1rb(_1rH,_1rI,[0,_1rJ,_1rK],_1rM);});}break;default:return new F(function(){return _1rb(_1rH,_1rI,[0,_1rJ,_1rK],_1rM);});}}},_1rW=function(_1rX,_1rY,_1rZ,_1s0,_1s1){var _1s2=E(_1s1);if(!_1s2[0]){return new F(function(){return _rF([0,_1rZ,_1s0],_1rY);});}else{var _1s3=E(_1s2[1]),_1s4=_1s3[1],_1s5=_1s3[2],_1s6=function(_1s7){var _1s8=B(_1qa(_1rX,_1s4,_1s5,_1s2[2])),_1s9=_1s8[1],_1sa=E(_1s8[3]);if(!_1sa[0]){return new F(function(){return _1rl(_1rX<<1,B(_sj([0,_1rZ,_1s0],_1rY,_1s9)),_1s8[2]);});}else{return new F(function(){return _1rg(B(_sj([0,_1rZ,_1s0],_1rY,_1s9)),_1sa[1],_1sa[2]);});}};switch(B(_1hC(_1md,_1rZ,_1s4))){case 0:return new F(function(){return _1s6(_);});break;case 1:var _1sb=E(_1s0),_1sc=E(_1s5);switch(B(_1hC(_1mb,_1sb[1],_1sc[1]))){case 0:return new F(function(){return _1s6(_);});break;case 1:return !B(A(_1pN,[_1sb[2],_1sc[2]]))?B(_1s6(_)):B(_1rb(_1rY,_1rZ,_1sb,_1s2));default:return new F(function(){return _1rb(_1rY,_1rZ,_1sb,_1s2);});}break;default:return new F(function(){return _1rb(_1rY,_1rZ,_1s0,_1s2);});}}},_1sd=function(_1se){var _1sf=E(_1se);if(!_1sf[0]){return [1];}else{var _1sg=_1sf[1],_1sh=E(_1sf[2]);if(!_1sh[0]){return [0,1,E(E(_1sg)),E(_qi),E(_qi)];}else{var _1si=_1sh[2],_1sj=E(_1sg),_1sk=E(_1sh[1]),_1sl=_1sk[1],_1sm=_1sk[2];switch(B(_1hC(_1md,_1sj[1],_1sl))){case 0:return new F(function(){return _1rW(1,[0,1,E(_1sj),E(_qi),E(_qi)],_1sl,_1sm,_1si);});break;case 1:var _1sn=E(_1sj[2]),_1so=E(_1sm),_1sp=_1so[1],_1sq=_1so[2];switch(B(_1hC(_1mb,_1sn[1],_1sp))){case 0:return new F(function(){return _1rF(1,[0,1,E(_1sj),E(_qi),E(_qi)],_1sl,_1sp,_1sq,_1si);});break;case 1:return !B(A(_1pN,[_1sn[2],_1sq]))?B(_1rF(1,[0,1,E(_1sj),E(_qi),E(_qi)],_1sl,_1sp,_1sq,_1si)):B(_1rb([0,1,E(_1sj),E(_qi),E(_qi)],_1sl,_1so,_1si));default:return new F(function(){return _1rb([0,1,E(_1sj),E(_qi),E(_qi)],_1sl,_1so,_1si);});}break;default:return new F(function(){return _1rb([0,1,E(_1sj),E(_qi),E(_qi)],_1sl,_1sm,_1si);});}}}},_1sr=new T(function(){return B(_4f(0,1,_f));}),_1ss=new T(function(){return B(unAppCStr("delta_",_1sr));}),_1st=[9,_,_,_1ss],_1su=[0,_1st],_1sv=[1,_1su,_f],_1sw=new T(function(){return B(unAppCStr("phi_",_1sr));}),_1sx=[3,_,_,_1sw],_1sy=[2,_,_1sx],_1sz=[1,_1sy,_f],_1sA=[1,_1sz],_1sB=[0,_1sv,_1sA],_1sC=new T(function(){return B(_4f(0,2,_f));}),_1sD=new T(function(){return B(unAppCStr("phi_",_1sC));}),_1sE=[3,_,_,_1sD],_1sF=[2,_,_1sE],_1sG=[1,_1sF,_f],_1sH=[1,_1sG],_1sI=new T(function(){return B(unAppCStr("delta_",_1sC));}),_1sJ=[9,_,_,_1sI],_1sK=[0,_1sJ],_1sL=[1,_1sK,_f],_1sM=[0,_1sL,_1sH],_1sN=[1,_1sM,_f],_1sO=[1,_1sB,_1sN],_1sP=[9,_,_199,_1sy,_1sF],_1sQ=[1,_1sP,_f],_1sR=[1,_1sQ],_1sS=[1,_1su,_1sL],_1sT=[0,_1sS,_1sR],_1sU=[0,_1sO,_1sT],_1sV=[0,_1sL,_1sA],_1sW=[1,_1sV,_f],_1sX=[0,_1sv,_1sH],_1sY=[1,_1sX,_1sW],_1sZ=[0,_1sY,_1sT],_1t0=[1,_1sZ,_f],_1t1=[1,_1sU,_1t0],_1t2=new T(function(){return B(_1sd(_1t1));}),_1t3=[0,_1t2,_1hg],_1t4=[1,_1sB,_f],_1t5=[9,_,_18L,_1sy,_1sF],_1t6=[1,_1t5,_f],_1t7=[1,_1t6],_1t8=[0,_1sv,_1t7],_1t9=[0,_1t4,_1t8],_1ta=[9,_,_18L,_1sF,_1sy],_1tb=[1,_1ta,_f],_1tc=[1,_1tb],_1td=[0,_1sv,_1tc],_1te=[0,_1t4,_1td],_1tf=[1,_1te,_f],_1tg=[1,_1t9,_1tf],_1th=new T(function(){return B(_1sd(_1tg));}),_1ti=[0,_1th,_1hf],_1tj=[1,_1sA,_1sL],_1tk=[7,_,_19A,_1sF],_1tl=[1,_1tk,_f],_1tm=[1,_1tl],_1tn=[0,_1tj,_1tm],_1to=[1,_1tn,_f],_1tp=[1,_1sA,_1sv],_1tq=[0,_1tp,_1sH],_1tr=[1,_1tq,_1to],_1ts=[7,_,_19A,_1sy],_1tt=[1,_1ts,_f],_1tu=[1,_1tt],_1tv=[0,_1sS,_1tu],_1tw=[0,_1tr,_1tv],_1tx=[1,_1sX,_1to],_1ty=[0,_1tx,_1tv],_1tz=[0,_1sL,_1tm],_1tA=[1,_1tz,_f],_1tB=[1,_1tq,_1tA],_1tC=[0,_1tB,_1tv],_1tD=[1,_1sX,_1tA],_1tE=[0,_1tD,_1tv],_1tF=[1,_1tq,_f],_1tG=[1,_1tn,_1tF],_1tH=[0,_1tG,_1tv],_1tI=[1,_1tz,_1tF],_1tJ=[0,_1tI,_1tv],_1tK=[1,_1sX,_f],_1tL=[1,_1tn,_1tK],_1tM=[0,_1tL,_1tv],_1tN=[1,_1tz,_1tK],_1tO=[0,_1tN,_1tv],_1tP=[1,_1tu,_1sL],_1tQ=[0,_1tP,_1tm],_1tR=[1,_1tu,_1sv],_1tS=[0,_1tR,_1sH],_1tT=[1,_1tS,_f],_1tU=[1,_1tQ,_1tT],_1tV=[0,_1sS,_1sA],_1tW=[0,_1tU,_1tV],_1tX=[1,_1tz,_1tT],_1tY=[0,_1tX,_1tV],_1tZ=[1,_1tQ,_1tK],_1u0=[0,_1tZ,_1tV],_1u1=[0,_1tN,_1tV],_1u2=[1,_1u1,_f],_1u3=[1,_1u0,_1u2],_1u4=[1,_1tY,_1u3],_1u5=[1,_1tW,_1u4],_1u6=[1,_1tO,_1u5],_1u7=[1,_1tM,_1u6],_1u8=[1,_1tJ,_1u7],_1u9=[1,_1tH,_1u8],_1ua=[1,_1tE,_1u9],_1ub=[1,_1tC,_1ua],_1uc=[1,_1ty,_1ub],_1ud=[1,_1tw,_1uc],_1ue=new T(function(){return B(_1sd(_1ud));}),_1uf=[0,_1ue,_1hq],_1ug=[1,_1uf,_f],_1uh=[1,_1ti,_1ug],_1ui=[0,83],_1uj=[1,_1ui,_f],_1uk=[0,_1sv,_1sR],_1ul=[1,_1uk,_f],_1um=[0,_1ul,_1sB],_1un=[0,_1ul,_1sX],_1uo=[1,_1un,_f],_1up=[1,_1um,_1uo],_1uq=new T(function(){return B(_1sd(_1up));}),_1ur=[0,_1uq,_1uj],_1us=[1,_1ur,_1uh],_1ut=[0,_1sS,_1sH],_1uu=[0,_1sL,_1tu],_1uv=[1,_1uu,_f],_1uw=[1,_1td,_1uv],_1ux=[0,_1uw,_1ut],_1uy=[1,_1td,_f],_1uz=[1,_1uu,_1uy],_1uA=[0,_1uz,_1ut],_1uB=[1,_1ux,_f],_1uC=[1,_1uA,_1uB],_1uD=[1,_1ux,_1uC],_1uE=[1,_1ux,_1uD],_1uF=new T(function(){return B(_1sd(_1uE));}),_1uG=[0,_1uF,_1ho],_1uH=[1,_1uG,_1us],_1uI=[9,_,_17z,_1sy,_1sF],_1uJ=[1,_1uI,_f],_1uK=[1,_1uJ],_1uL=[0,_1sL,_1uK],_1uM=[1,_1uL,_f],_1uN=[1,_1sB,_1uM],_1uO=[0,_1uN,_1ut],_1uP=[0,_1sv,_1uK],_1uQ=[1,_1uP,_1sW],_1uR=[0,_1uQ,_1ut],_1uS=[1,_1uR,_f],_1uT=[1,_1uO,_1uS],_1uU=new T(function(){return B(_1sd(_1uT));}),_1uV=[0,_1uU,_1hp],_1uW=[1,_1uV,_1uH],_1uX=[0,_1tK,_1uP],_1uY=[0,_1tF,_1uP],_1uZ=[1,_1uY,_f],_1v0=[1,_1uX,_1uZ],_1v1=new T(function(){return B(_1sd(_1v0));}),_1v2=[0,_1v1,_1hr],_1v3=[1,_1v2,_1uW],_1v4=[1,_1t3,_1v3],_1v5=new T(function(){return B(_1pG(_1v4));}),_1v6=function(_1v7){return new F(function(){return _wz(_1v7,_f);});},_1v8=function(_1v9,_1va){return _1v9<=B(_iX(_1va,0))?[1,new T(function(){var _1vb=_1v9-1|0;if(_1vb>=0){var _1vc=B(_zN(B(_1v6(_1va)),_1vb));}else{var _1vc=E(_zK);}var _1vd=_1vc,_1ve=_1vd;return _1ve;})]:[0];},_1vf=function(_1vg,_1vh,_1vi){var _1vj=function(_1vk){return _1vk<=B(_iX(_1vi,0))?[1,[0,new T(function(){var _1vl=_1vg-1|0;if(_1vl>=0){var _1vm=B(_zN(B(_1v6(_1vi)),_1vl));}else{var _1vm=E(_zK);}var _1vn=_1vm,_1vo=_1vn;return _1vo;}),new T(function(){var _1vp=_1vh-1|0;if(_1vp>=0){var _1vq=B(_zN(B(_1v6(_1vi)),_1vp));}else{var _1vq=E(_zK);}var _1vr=_1vq,_1vs=_1vr;return _1vs;})]]:[0];};return _1vg>_1vh?B(_1vj(_1vg)):B(_1vj(_1vh));},_1vt=[0],_1vu=new T(function(){return B(unCStr("depends on unjustified lines"));}),_1vv=new T(function(){return B(unCStr("unavailable lines"));}),_1vw=new T(function(){return B(unCStr("wrong number of premises"));}),_1vx=new T(function(){return B(unCStr("Impossible Error 1"));}),_1vy=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1vz=new T(function(){return B(unCStr("PR"));}),_1vA=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1vB=function(_1vC,_1vD,_1vE,_1vF,_1vG,_1vH){var _1vI=function(_1vJ){var _1vK=B(A(_1vF,[_1vD]));if(!_1vK[0]){return [0,[1,_1vA,_1vG],[1,_10,_1vH]];}else{var _1vL=E(_1vK[1]);if(!_1vL[0]){switch(E(E(_1vL[1])[1])){case 1:var _1vM=E(_1vE);if(!_1vM[0]){return [0,[1,_1vw,_1vG],[1,_10,_1vH]];}else{if(!E(_1vM[2])[0]){var _1vN=B(_1v8(E(_1vM[1])[1],_1vH));if(!_1vN[0]){return [0,[1,_1vv,_1vG],[1,_10,_1vH]];}else{var _1vO=E(_1vN[1]);return _1vO[0]==0?[0,[1,_1vu,_1vG],[1,_10,_1vH]]:[0,[1,_f,_1vG],[1,[1,[0,_1vC,[1,_1vD,[1,_1vO[1],_f]]]],_1vH]];}}else{return [0,[1,_1vw,_1vG],[1,_10,_1vH]];}}break;case 2:var _1vP=E(_1vE);if(!_1vP[0]){return [0,[1,_1vw,_1vG],[1,_10,_1vH]];}else{var _1vQ=E(_1vP[2]);if(!_1vQ[0]){return [0,[1,_1vw,_1vG],[1,_10,_1vH]];}else{if(!E(_1vQ[2])[0]){var _1vR=B(_1vf(E(_1vP[1])[1],E(_1vQ[1])[1],_1vH));if(!_1vR[0]){return [0,[1,_1vv,_1vG],[1,_10,_1vH]];}else{var _1vS=E(_1vR[1]),_1vT=E(_1vS[1]);if(!_1vT[0]){return [0,[1,_1vu,_1vG],[1,_10,_1vH]];}else{var _1vU=E(_1vS[2]);return _1vU[0]==0?[0,[1,_1vu,_1vG],[1,_10,_1vH]]:[0,[1,_f,_1vG],[1,[1,[0,_1vC,[1,_1vD,[1,_1vT[1],[1,_1vU[1],_f]]]]],_1vH]];}}}else{return [0,[1,_1vw,_1vG],[1,_10,_1vH]];}}}break;default:return [0,[1,_1vx,_1vG],[1,_10,_1vH]];}}else{return [0,[1,_1vy,_1vG],[1,_10,_1vH]];}}};return !B(_bw(_1vD,_1vz))?B(_1vI(_)):E(_1vE)[0]==0?[0,[1,_f,_1vG],[1,[1,[0,_1vC,_1vt]],_1vH]]:B(_1vI(_));},_1vV=new T(function(){return B(unCStr("depends on an unjustified line"));}),_1vW=new T(function(){return B(unCStr("unavailable line"));}),_1vX=function(_1vY,_1vZ,_1w0,_1w1){return E(B(_1w2(_1vY,_1vZ,[1,_f,_1w0],[1,_10,_1w1]))[2]);},_1w3=function(_1w4,_1w5,_1w6,_1w7,_1w8,_1w9,_1wa,_1wb){var _1wc=B(_1vf(_1w7,_1w8,B(_1vX(_1w4,_1w5,_1wa,_1wb))));if(!_1wc[0]){return new F(function(){return _1w2(_1w4,_1w5,[1,_1vW,_1wa],[1,_10,_1wb]);});}else{var _1wd=E(_1wc[1]),_1we=E(_1wd[1]);if(!_1we[0]){return new F(function(){return _1w2(_1w4,_1w5,[1,_1vV,_1wa],[1,_10,_1wb]);});}else{var _1wf=E(_1wd[2]);return _1wf[0]==0?B(_1w2(_1w4,_1w5,[1,_1vV,_1wa],[1,_10,_1wb])):B(_1w2(_1w4,_1w5,[1,_f,_1wa],[1,[1,[0,_1w6,[1,_1w9,[1,_1we[1],[1,_1wf[1],_f]]]]],_1wb]));}}},_1wg=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1wh=function(_1wi,_1wj,_1wk,_1wl,_1wm,_1wn,_1wo){var _1wp=E(_1wm);if(!_1wp[0]){return new F(function(){return _1w2(_1wi,_1wj,[1,_1wg,_1wn],[1,_10,_1wo]);});}else{var _1wq=E(_1wp[2]);if(!_1wq[0]){return new F(function(){return _1w2(_1wi,_1wj,[1,_1wg,_1wn],[1,_10,_1wo]);});}else{if(!E(_1wq[2])[0]){return new F(function(){return _1w3(_1wi,_1wj,_1wk,E(_1wp[1])[1],E(_1wq[1])[1],_1wl,_1wn,_1wo);});}else{return new F(function(){return _1w2(_1wi,_1wj,[1,_1wg,_1wn],[1,_10,_1wo]);});}}}},_1wr=function(_1ws,_1wt,_1wu){return [0,[1,_f,_1wt],[1,_10,new T(function(){var _1wv=B(_iX(_1wt,0))-E(_1ws)[1]|0,_1ww=new T(function(){return _1wv>=0?B(_nC(_1wv,_1wu)):E(_1wu);});if(_1wv>0){var _1wx=function(_1wy,_1wz){var _1wA=E(_1wy);return _1wA[0]==0?E(_1ww):_1wz>1?[1,_10,new T(function(){return B(_1wx(_1wA[2],_1wz-1|0));})]:E([1,_10,_1ww]);},_1wB=B(_1wx(_1wu,_1wv));}else{var _1wB=E(_1ww);}var _1wC=_1wB,_1wD=_1wC,_1wE=_1wD,_1wF=_1wE;return _1wF;})]];},_1wG=function(_1wH,_1wI,_1wJ,_1wK,_1wL,_1wM,_1wN){var _1wO=new T(function(){return E(B(_1w2(_1wH,_1wI,[1,_f,_1wM],[1,_10,_1wN]))[2]);});if(_1wK<=B(_iX(_1wO,0))){var _1wP=_1wK-1|0;if(_1wP>=0){var _1wQ=B(_zN(B(_1v6(_1wO)),_1wP));return _1wQ[0]==0?B(_1w2(_1wH,_1wI,[1,_1vV,_1wM],[1,_10,_1wN])):B(_1w2(_1wH,_1wI,[1,_f,_1wM],[1,[1,[0,_1wJ,[1,_1wL,[1,_1wQ[1],_f]]]],_1wN]));}else{return E(_zK);}}else{return new F(function(){return _1w2(_1wH,_1wI,[1,_1vW,_1wM],[1,_10,_1wN]);});}},_1wR=function(_1wS,_1wT,_1wU,_1wV,_1wW,_1wX,_1wY){var _1wZ=E(_1wW);if(!_1wZ[0]){return new F(function(){return _1w2(_1wS,_1wT,[1,_1wg,_1wX],[1,_10,_1wY]);});}else{if(!E(_1wZ[2])[0]){return new F(function(){return _1wG(_1wS,_1wT,_1wU,E(_1wZ[1])[1],_1wV,_1wX,_1wY);});}else{return new F(function(){return _1w2(_1wS,_1wT,[1,_1wg,_1wX],[1,_10,_1wY]);});}}},_1x0=new T(function(){return B(unCStr("Open Subproof"));}),_1x1=new T(function(){return B(unCStr("Impossible Error 2"));}),_1x2=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1x3=new T(function(){return B(unCStr("SHOW"));}),_1x4=function(_1x5,_1x6,_1x7,_1x8,_1x9,_1xa,_1xb){if(!B(_bw(_1x6,_1x3))){var _1xc=B(A(_1x8,[_1x6]));if(!_1xc[0]){return [0,[1,_1vA,_1xa],[1,_10,_1xb]];}else{var _1xd=E(_1xc[1]);if(!_1xd[0]){return [0,[1,_1x2,_1xa],[1,_10,_1xb]];}else{switch(E(E(_1xd[1])[1])){case 1:var _1xe=B(_1wR(_1x9,_1x8,_1x5,_1x6,_1x7,_1xa,_1xb));return new F(function(){return _1wr(new T(function(){return [0,B(_iX(_1xa,0))+1|0];},1),_1xe[1],_1xe[2]);});break;case 2:var _1xf=B(_1wh(_1x9,_1x8,_1x5,_1x6,_1x7,_1xa,_1xb));return new F(function(){return _1wr(new T(function(){return [0,B(_iX(_1xa,0))+1|0];},1),_1xf[1],_1xf[2]);});break;default:return [0,[1,_1x1,_1xa],[1,_10,_1xb]];}}}}else{var _1xg=B(_1w2(_1x9,_1x8,[1,_1x0,_1xa],[1,_10,_1xb]));return new F(function(){return _1wr(new T(function(){return [0,B(_iX(_1xa,0))+1|0];},1),_1xg[1],_1xg[2]);});}},_1xh=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1xi=new T(function(){return B(unCStr("formula syntax error"));}),_1xj=function(_1xk,_1xl,_1xm,_1xn,_1xo){var _1xp=E(_1xk);if(!_1xp[0]){return E(_1xl)[0]==0?[0,[1,_1xi,_1xn],[1,_10,_1xo]]:[0,[1,_1xh,_1xn],[1,_10,_1xo]];}else{var _1xq=_1xp[1],_1xr=E(_1xl);if(!_1xr[0]){var _1xs=E(_1xq);return new F(function(){return _1vB(_1xs[1],_1xs[2],_1xs[3],_1xm,_1xn,_1xo);});}else{var _1xt=E(_1xq);return new F(function(){return _1x4(_1xt[1],_1xt[2],_1xt[3],_1xm,_1xr,_1xn,_1xo);});}}},_1w2=function(_1xu,_1xv,_1xw,_1xx){return new F(function(){return (function(_1xy,_1xz,_1xA){while(1){var _1xB=E(_1xA);if(!_1xB[0]){return [0,_1xy,_1xz];}else{var _1xC=E(_1xB[1]),_1xD=B(_1xj(_1xC[1],_1xC[2],_1xv,_1xy,_1xz));_1xy=_1xD[1];_1xz=_1xD[2];_1xA=_1xB[2];continue;}}})(_1xw,_1xx,_1xu);});},_1xE=function(_1xF,_1xG){while(1){var _1xH=E(_1xG);if(!_1xH[0]){return true;}else{if(!B(A(_1xF,[_1xH[1]]))){return false;}else{_1xG=_1xH[2];continue;}}}},_1xI=[0,666],_1xJ=[0,_,_1xI],_1xK=[1,_1xJ],_1xL=[0,_1xK,_1vt],_1xM=function(_1xN){return new F(function(){return _bw(_1xN,_f);});},_1xO=function(_1xP,_1xQ){var _1xR=B(_1w2(_1xP,_1xQ,_f,_f)),_1xS=_1xR[1];return !B(_1xE(_1xM,_1xS))?[0,_1xS]:[1,new T(function(){var _1xT=B(_iX(_1xP,0))-1|0;if(_1xT>=0){var _1xU=B(_zN(B(_wz(_1xR[2],_f)),_1xT)),_1xV=_1xU[0]==0?E(_1xL):E(_1xU[1]);}else{var _1xV=E(_zK);}var _1xW=_1xV,_1xX=_1xW,_1xY=_1xX;return _1xY;})];},_1xZ=function(_1y0,_1y1){return E(_61);},_1y2=function(_1y3,_1y4,_1y5,_1y6){var _1y7=E(_1y5);switch(_1y7[0]){case 0:var _1y8=E(_1y6);return _1y8[0]==0?E(_61):E(_1y8[1]);case 1:return new F(function(){return A(_1y3,[_1y7[1],_f]);});break;case 2:return new F(function(){return A(_1y4,[_1y7[1],[1,new T(function(){return B(_1y2(_1y3,_1y4,_1y7[2],_1y6));}),_f]]);});break;default:return new F(function(){return A(_1y4,[_1y7[1],[1,new T(function(){return B(_1y2(_1y3,_1y4,_1y7[2],_1y6));}),[1,new T(function(){return B(_1y2(_1y3,_1y4,_1y7[3],_1y6));}),_f]]]);});}},_1y9=function(_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yg,_1yh){var _1yi=E(_1yg);switch(_1yi[0]){case 0:return [0];case 1:return new F(function(){return A(_1yd,[_1yi[1],_f]);});break;case 2:return new F(function(){return A(_1ya,[_1yi[1],[1,new T(function(){return B(_1y2(_1yd,_1ye,_1yi[2],_1yh));}),_f]]);});break;case 3:return new F(function(){return A(_1ya,[_1yi[1],[1,new T(function(){return B(_1y2(_1yd,_1ye,_1yi[2],_1yh));}),[1,new T(function(){return B(_1y2(_1yd,_1ye,_1yi[3],_1yh));}),_f]]]);});break;case 4:return new F(function(){return A(_1yb,[_1yi[1],[1,new T(function(){return B(_1y9(_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yi[2],_1yh));}),_f]]);});break;case 5:return new F(function(){return A(_1yb,[_1yi[1],[1,new T(function(){return B(_1y9(_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yi[2],_1yh));}),[1,new T(function(){return B(_1y9(_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yi[3],_1yh));}),_f]]]);});break;default:var _1yj=_1yi[1],_1yk=_1yi[2];return new F(function(){return A(_1yc,[_1yj,[1,new T(function(){return B(A(_1yf,[new T(function(){return B(A(_1yk,[_an]));}),_1yj]));}),[1,new T(function(){return B(_1y9(_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,B(A(_1yk,[_an])),[1,new T(function(){return B(A(_1yf,[new T(function(){return B(A(_1yk,[_an]));}),_1yj]));}),_f]));}),_f]]]);});}},_1yl=[0,95],_1ym=[1,_1yl,_f],_1yn=[1,_1ym,_f],_1yo=function(_1yp,_){return _1yp;},_1yq=function(_1yr){var _1ys=E(_1yr);return _1ys[0]==0?E(_1yo):function(_1yt,_){var _1yu=B(A(new T(function(){var _1yv=E(_1ys[1]);return B(_1yw(_1yv[1],_1yv[2]));}),[_1yt,_])),_1yx=_1yu,_1yy=B(A(new T(function(){return B(_1yq(_1ys[2]));}),[_1yt,_])),_1yz=_1yy;return _1yt;};},_1yA=function(_1yB,_1yC){return function(_1yD,_){var _1yE=B(A(new T(function(){var _1yF=E(_1yB);return B(_1yw(_1yF[1],_1yF[2]));}),[_1yD,_])),_1yG=_1yE,_1yH=B(A(new T(function(){return B(_1yq(_1yC));}),[_1yD,_])),_1yI=_1yH;return _1yD;};},_1yJ=function(_1yK,_1yL){return new F(function(){return _4f(0,E(_1yK)[1],_1yL);});},_1yM=function(_1yN){return function(_m0,_m1){return new F(function(){return _5U(new T(function(){return B(_1P(_1yJ,_1yN,_f));}),_m0,_m1);});};},_1yO=function(_1yP){return function(_m0,_m1){return new F(function(){return _5U(new T(function(){return B(_1y9(_6y,_6p,_6y,_6v,_6y,_1xZ,_1yP,_1yn));}),_m0,_m1);});};},_1yQ=new T(function(){return B(unCStr("open"));}),_1yR=new T(function(){return B(unCStr("termination"));}),_1yS=new T(function(){return B(unCStr("closed"));}),_1yT=function(_1yU){var _1yV=E(_1yU);return _1yV[0]==0?E(_1yo):function(_1yW,_){var _1yX=B(A(new T(function(){var _1yY=E(_1yV[1]);return B(_1yw(_1yY[1],_1yY[2]));}),[_1yW,_])),_1yZ=_1yX,_1z0=B(A(new T(function(){return B(_1yT(_1yV[2]));}),[_1yW,_])),_1z1=_1z0;return _1yW;};},_1z2=function(_1z3,_1z4){return function(_1z5,_){var _1z6=B(A(new T(function(){var _1z7=E(_1z3);return B(_1yw(_1z7[1],_1z7[2]));}),[_1z5,_])),_1z8=_1z6,_1z9=B(A(new T(function(){return B(_1yT(_1z4));}),[_1z5,_])),_1za=_1z9;return _1z5;};},_1zb=new T(function(){return B(unCStr("SHOW"));}),_1yw=function(_1zc,_1zd){var _1ze=E(_1zc);if(!_1ze[0]){return function(_m0,_m1){return new F(function(){return _vg(_5U,_1ze[1],_m0,_m1);});};}else{var _1zf=E(_1ze[1]),_1zg=_1zf[1],_1zh=_1zf[2],_1zi=_1zf[3];if(!B(_bw(_1zh,_1zb))){var _1zj=E(_1zd);return _1zj[0]==0?function(_m0,_m1){return new F(function(){return _vg(_55,function(_1zk,_){var _1zl=B(_4V(_1yO,_1zg,_1zk,_)),_1zm=_1zl,_1zn=B(_4V(_55,function(_1zo,_){var _1zp=B(_4V(_5U,_1zh,_1zo,_)),_1zq=_1zp,_1zr=B(_4V(_1yM,_1zi,_1zo,_)),_1zs=_1zr;return _1zo;},_1zk,_)),_1zt=_1zn;return _1zk;},_m0,_m1);});}:function(_m0,_m1){return new F(function(){return _vg(_55,function(_1zu,_){var _1zv=B(_4V(_5U,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1y9(_6y,_6p,_6y,_6v,_6y,_1xZ,_1zg,_1yn));})));}),_1zu,_)),_1zw=_1zv,_1zx=B(_vg(_55,function(_1zy,_){var _1zz=B(_4V(_55,new T(function(){return B(_1yA(_1zj[1],_1zj[2]));}),_1zy,_)),_1zA=_1zz,_1zB=B(_vg(_55,function(_1zC,_){var _1zD=B(_4V(_5U,_f,_1zC,_)),_1zE=_1zD,_1zF=B(A(_42,[_4s,_1zE,_vD,_1yR,_])),_1zG=_1zF,_1zH=B(_4V(_55,function(_1zI,_){var _1zJ=B(_4V(_5U,_1zh,_1zI,_)),_1zK=_1zJ,_1zL=B(_4V(_1yM,_1zi,_1zI,_)),_1zM=_1zL;return _1zI;},_1zC,_)),_1zN=_1zH;return _1zC;},_1zy,_)),_1zO=_1zB;return _1zy;},_1zu,_)),_1zP=_1zx,_1zQ=B(A(_42,[_4s,_1zP,_vD,_1yS,_])),_1zR=_1zQ;return _1zu;},_m0,_m1);});};}else{var _1zS=E(_1zd);return _1zS[0]==0?function(_m0,_m1){return new F(function(){return _vg(_55,function(_v0,_){return new F(function(){return _4V(_5U,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1y9(_6y,_6p,_6y,_6v,_6y,_1xZ,_1zg,_1yn));})));}),_v0,_);});},_m0,_m1);});}:function(_m0,_m1){return new F(function(){return _vg(_55,function(_1zT,_){var _1zU=B(_4V(_5U,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1y9(_6y,_6p,_6y,_6v,_6y,_1xZ,_1zg,_1yn));})));}),_1zT,_)),_1zV=_1zU,_1zW=B(_vg(_55,function(_v0,_){return new F(function(){return _4V(_55,new T(function(){return B(_1z2(_1zS[1],_1zS[2]));}),_v0,_);});},_1zT,_)),_1zX=_1zW,_1zY=B(A(_42,[_4s,_1zX,_vD,_1yQ,_])),_1zZ=_1zY;return _1zT;},_m0,_m1);});};}}},_1A0=function(_1A1){var _1A2=E(_1A1);return _1A2[0]==0?E(_1yo):function(_1A3,_){var _1A4=B(A(new T(function(){var _1A5=E(_1A2[1]);return B(_1yw(_1A5[1],_1A5[2]));}),[_1A3,_])),_1A6=_1A4,_1A7=B(A(new T(function(){return B(_1A0(_1A2[2]));}),[_1A3,_])),_1A8=_1A7;return _1A3;};},_1A9=[0,10],_1Aa=[1,_1A9,_f],_1Ab=function(_1Ac){var _1Ad=new T(function(){var _1Ae=B(_Xr(_Wj,_XN,[0,new T(function(){return B(_1F(_1Ac,_1Aa));}),E(_We),E(_0)]));if(!_1Ae[0]){var _1Af=E(_1Ae[1]);if(!_1Af[0]){var _1Ag=E(E(_1Af[1])[1]);}else{var _1Ag=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9T(_1Af[1]));})));})],_f],_f];}var _1Ah=_1Ag;}else{var _1Ai=E(_1Ae[1]);if(!_1Ai[0]){var _1Aj=E(E(_1Ai[1])[1]);}else{var _1Aj=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9T(_1Ai[1]));})));})],_f],_f];}var _1Ah=_1Aj;}return _1Ah;});return function(_m0,_m1){return new F(function(){return _57(_vC,function(_1Ak,_1Al,_){return new F(function(){return _57(_uZ,function(_1Am,_1An,_){return new F(function(){return _57(_v5,function(_1Ao,_1Ap,_){return new F(function(){return _57(function(_1Aq,_){return [0,[0,function(_1Ar,_){var _1As=B(_vg(_5U,_f,_1Ar,_)),_1At=_1As,_1Au=B(A(_42,[_4s,_1At,_4r,_1Ak,_])),_1Av=_1Au,_1Aw=B(A(_42,[_4s,_1At,_vD,_v6,_])),_1Ax=_1Aw;return _1At;},_vb],_1Aq];},function(_1Ay,_1Az,_){return new F(function(){return _57(function(_1AA,_){return [0,[0,function(_1AB,_){var _1AC=B(_4V(_55,new T(function(){return B(_1A0(_1Ad));}),_1AB,_)),_1AD=_1AC,_1AE=B(A(_42,[_4s,_1AD,_4r,_1Am,_])),_1AF=_1AE,_1AG=B(A(_42,[_4s,_1AD,_vD,_v7,_])),_1AH=_1AG;return _1AD;},_vb],_1AA];},function(_1AI){return E(new T(function(){var _1AJ=E(new T(function(){var _1AK=B(_1xO(_1Ad,_1hx));return _1AK[0]==0?[0,_1AK[1]]:[1,new T(function(){var _1AL=E(_1AK[1]);return B(_uv(_62,_6N,_6v,_6y,_6y,_6p,_6y,_6J,_a3,_9X,_a6,_1v5,_1AL[1],_1AL[2]));})];}));if(!_1AJ[0]){var _1AM=function(_1AN,_){return [0,[0,function(_1AO,_){var _1AP=B(_vg(_55,function(_v0,_){return new F(function(){return _vq(new T(function(){return B(_wz(_1AJ[1],_f));}),_v0,_);});},_1AO,_)),_1AQ=_1AP,_1AR=B(A(_42,[_4s,_1AQ,_4r,_1Ao,_])),_1AS=_1AR,_1AT=B(A(_42,[_4s,_1AQ,_vD,_v8,_])),_1AU=_1AT;return _1AQ;},_vb],_1AN];};}else{var _1AV=E(_1AJ[1]);if(!_1AV[0]){var _1AW=function(_v0,_){return new F(function(){return _vF(_1Ak,_uS,_vd,_v0,_);});};}else{var _1AW=function(_m0,_m1){return new F(function(){return _vF(_1Ak,_uS,function(_1AX,_){return [0,[0,function(_v0,_){return new F(function(){return _4V(_5U,new T(function(){var _1AY=E(_1AV[1]);return B(_aZ(_1AY[1],_1AY[2]));}),_v0,_);});},_vb],_1AX];},_m0,_m1);});};}var _1AM=_1AW;}return _1AM;}));},_1Az,_);});},_1Ap,_);});},_1An,_);});},_1Al,_);});},_m0,_m1);});};},_1AZ=new T(function(){return B(unCStr("lined"));}),_1B0=function(_1B1,_1B2,_){var _1B3=jsCreateElem(toJSStr(E(_1B1))),_1B4=_1B3,_1B5=jsAppendChild(_1B4,E(_1B2)[1]);return [0,_1B4];},_1B6=function(_1B7,_1B8,_1B9,_){var _1Ba=B(_1B0(_1B7,_1B9,_)),_1Bb=_1Ba,_1Bc=B(A(_1B8,[_1Bb,_])),_1Bd=_1Bc;return _1Bb;},_1Be=new T(function(){return B(unCStr("()"));}),_1Bf=new T(function(){return B(unCStr("GHC.Tuple"));}),_1Bg=new T(function(){return B(unCStr("ghc-prim"));}),_1Bh=new T(function(){var _1Bi=hs_wordToWord64(2170319554),_1Bj=_1Bi,_1Bk=hs_wordToWord64(26914641),_1Bl=_1Bk;return [0,_1Bj,_1Bl,[0,_1Bj,_1Bl,_1Bg,_1Bf,_1Be],_f];}),_1Bm=function(_1Bn){return E(_1Bh);},_1Bo=new T(function(){return B(unCStr("PerchM"));}),_1Bp=new T(function(){return B(unCStr("Haste.Perch"));}),_1Bq=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1Br=new T(function(){var _1Bs=hs_wordToWord64(3005229400),_1Bt=_1Bs,_1Bu=hs_wordToWord64(2682402736),_1Bv=_1Bu;return [0,_1Bt,_1Bv,[0,_1Bt,_1Bv,_1Bq,_1Bp,_1Bo],_f];}),_1Bw=function(_1Bx){return E(_1Br);},_1By=function(_1Bz){var _1BA=E(_1Bz);if(!_1BA[0]){return [0];}else{var _1BB=E(_1BA[1]);return [1,[0,_1BB[1],_1BB[2]],new T(function(){return B(_1By(_1BA[2]));})];}},_1BC=function(_1BD,_1BE){var _1BF=E(_1BD);if(!_1BF){return [0,_f,_1BE];}else{var _1BG=E(_1BE);if(!_1BG[0]){return [0,_f,_f];}else{var _1BH=new T(function(){var _1BI=B(_1BC(_1BF-1|0,_1BG[2]));return [0,_1BI[1],_1BI[2]];});return [0,[1,_1BG[1],new T(function(){return E(E(_1BH)[1]);})],new T(function(){return E(E(_1BH)[2]);})];}}},_1BJ=[0,120],_1BK=[0,48],_1BL=function(_1BM){var _1BN=new T(function(){var _1BO=B(_1BC(8,new T(function(){var _1BP=md5(toJSStr(E(_1BM))),_1BQ=_1BP;return fromJSStr(_1BQ);})));return [0,_1BO[1],_1BO[2]];}),_1BR=parseInt([0,toJSStr([1,_1BK,[1,_1BJ,new T(function(){return E(E(_1BN)[1]);})]])]),_1BS=_1BR,_1BT=new T(function(){var _1BU=B(_1BC(8,new T(function(){return E(E(_1BN)[2]);})));return [0,_1BU[1],_1BU[2]];}),_1BV=parseInt([0,toJSStr([1,_1BK,[1,_1BJ,new T(function(){return E(E(_1BT)[1]);})]])]),_1BW=_1BV,_1BX=hs_mkWord64(_1BS,_1BW),_1BY=_1BX,_1BZ=parseInt([0,toJSStr([1,_1BK,[1,_1BJ,new T(function(){return E(B(_1BC(8,new T(function(){return E(E(_1BT)[2]);})))[1]);})]])]),_1C0=_1BZ,_1C1=hs_mkWord64(_1C0,_1C0),_1C2=_1C1;return [0,_1BY,_1C2];},_1C3=function(_1C4,_1C5){var _1C6=jsShowI(_1C4),_1C7=_1C6,_1C8=md5(_1C7),_1C9=_1C8;return new F(function(){return _1F(fromJSStr(_1C9),new T(function(){var _1Ca=jsShowI(_1C5),_1Cb=_1Ca,_1Cc=md5(_1Cb),_1Cd=_1Cc;return fromJSStr(_1Cd);},1));});},_1Ce=function(_1Cf){var _1Cg=E(_1Cf);return new F(function(){return _1C3(_1Cg[1],_1Cg[2]);});},_1Ch=function(_1Ci,_1Cj){return function(_1Ck){return E(new T(function(){var _1Cl=B(A(_1Ci,[_])),_1Cm=E(_1Cl[3]),_1Cn=_1Cm[1],_1Co=_1Cm[2],_1Cp=B(_1F(_1Cl[4],[1,new T(function(){return B(A(_1Cj,[_]));}),_f]));if(!_1Cp[0]){var _1Cq=[0,_1Cn,_1Co,_1Cm,_f];}else{var _1Cr=B(_1BL(new T(function(){return B(_7o(B(_7U(_1Ce,[1,[0,_1Cn,_1Co],new T(function(){return B(_1By(_1Cp));})]))));},1))),_1Cq=[0,_1Cr[1],_1Cr[2],_1Cm,_1Cp];}var _1Cs=_1Cq,_1Ct=_1Cs;return _1Ct;}));};},_1Cu=new T(function(){return B(_1Ch(_1Bw,_1Bm));}),_1Cv=function(_1Cw,_1Cx,_1Cy,_){var _1Cz=E(_1Cx),_1CA=B(A(_1Cw,[_1Cy,_])),_1CB=_1CA,_1CC=B(A(_42,[_4s,_1CB,_1Cz[1],_1Cz[2],_])),_1CD=_1CC;return _1CB;},_1CE=function(_1CF,_1CG){while(1){var _1CH=(function(_1CI,_1CJ){var _1CK=E(_1CJ);if(!_1CK[0]){return E(_1CI);}else{_1CF=function(_1CL,_){return new F(function(){return _1Cv(_1CI,_1CK[1],_1CL,_);});};_1CG=_1CK[2];return null;}})(_1CF,_1CG);if(_1CH!=null){return _1CH;}}},_1CM=new T(function(){return B(unCStr("value"));}),_1CN=new T(function(){return B(unCStr("id"));}),_1CO=new T(function(){return B(unCStr("onclick"));}),_1CP=new T(function(){return B(unCStr("checked"));}),_1CQ=[0,_1CP,_f],_1CR=[1,_1CQ,_f],_1CS=new T(function(){return B(unCStr("type"));}),_1CT=new T(function(){return B(unCStr("input"));}),_1CU=function(_1CV,_){return new F(function(){return _1B0(_1CT,_1CV,_);});},_1CW=function(_1CX,_1CY,_1CZ,_1D0,_1D1){var _1D2=new T(function(){var _1D3=new T(function(){return B(_1CE(_1CU,[1,[0,_1CS,_1CY],[1,[0,_1CN,_1CX],[1,[0,_1CM,_1CZ],_f]]]));});return !E(_1D0)?E(_1D3):B(_1CE(_1D3,_1CR));}),_1D4=E(_1D1);return _1D4[0]==0?E(_1D2):B(_1CE(_1D2,[1,[0,_1CO,_1D4[1]],_f]));},_1D5=new T(function(){return B(unCStr("href"));}),_1D6=[0,97],_1D7=[1,_1D6,_f],_1D8=function(_1D9,_){return new F(function(){return _1B0(_1D7,_1D9,_);});},_1Da=function(_1Db,_1Dc){return function(_1Dd,_){var _1De=B(A(new T(function(){return B(_1CE(_1D8,[1,[0,_1D5,_1Db],_f]));}),[_1Dd,_])),_1Df=_1De,_1Dg=B(A(_1Dc,[_1Df,_])),_1Dh=_1Dg;return _1Df;};},_1Di=function(_1Dj){return new F(function(){return _1Da(_1Dj,function(_1CL,_){return new F(function(){return _5U(_1Dj,_1CL,_);});});});},_1Dk=new T(function(){return B(unCStr("option"));}),_1Dl=function(_1Dm,_){return new F(function(){return _1B0(_1Dk,_1Dm,_);});},_1Dn=new T(function(){return B(unCStr("selected"));}),_1Do=[0,_1Dn,_f],_1Dp=[1,_1Do,_f],_1Dq=function(_1Dr,_1Ds,_1Dt){var _1Du=new T(function(){return B(_1CE(_1Dl,[1,[0,_1CM,_1Dr],_f]));});if(!E(_1Dt)){return function(_1Dv,_){var _1Dw=B(A(_1Du,[_1Dv,_])),_1Dx=_1Dw,_1Dy=B(A(_1Ds,[_1Dx,_])),_1Dz=_1Dy;return _1Dx;};}else{return new F(function(){return _1CE(function(_1DA,_){var _1DB=B(A(_1Du,[_1DA,_])),_1DC=_1DB,_1DD=B(A(_1Ds,[_1DC,_])),_1DE=_1DD;return _1DC;},_1Dp);});}},_1DF=function(_1DG,_1DH){return new F(function(){return _1Dq(_1DG,function(_1CL,_){return new F(function(){return _5U(_1DG,_1CL,_);});},_1DH);});},_1DI=new T(function(){return B(unCStr("method"));}),_1DJ=new T(function(){return B(unCStr("action"));}),_1DK=new T(function(){return B(unCStr("UTF-8"));}),_1DL=new T(function(){return B(unCStr("acceptCharset"));}),_1DM=[0,_1DL,_1DK],_1DN=new T(function(){return B(unCStr("form"));}),_1DO=function(_1DP,_){return new F(function(){return _1B0(_1DN,_1DP,_);});},_1DQ=function(_1DR,_1DS,_1DT){return function(_1DU,_){var _1DV=B(A(new T(function(){return B(_1CE(_1DO,[1,_1DM,[1,[0,_1DJ,_1DR],[1,[0,_1DI,_1DS],_f]]]));}),[_1DU,_])),_1DW=_1DV,_1DX=B(A(_1DT,[_1DW,_])),_1DY=_1DX;return _1DW;};},_1DZ=new T(function(){return B(unCStr("select"));}),_1E0=function(_1E1,_){return new F(function(){return _1B0(_1DZ,_1E1,_);});},_1E2=function(_1E3,_1E4){return function(_1E5,_){var _1E6=B(A(new T(function(){return B(_1CE(_1E0,[1,[0,_1CN,_1E3],_f]));}),[_1E5,_])),_1E7=_1E6,_1E8=B(A(_1E4,[_1E7,_])),_1E9=_1E8;return _1E7;};},_1Ea=new T(function(){return B(unCStr("textarea"));}),_1Eb=function(_1Ec,_){return new F(function(){return _1B0(_1Ea,_1Ec,_);});},_1Ed=function(_1Ee,_1Ef){return function(_1Eg,_){var _1Eh=B(A(new T(function(){return B(_1CE(_1Eb,[1,[0,_1CN,_1Ee],_f]));}),[_1Eg,_])),_1Ei=_1Eh,_1Ej=B(_5U(_1Ef,_1Ei,_)),_1Ek=_1Ej;return _1Ei;};},_1El=new T(function(){return B(unCStr("color:red"));}),_1Em=new T(function(){return B(unCStr("style"));}),_1En=[0,_1Em,_1El],_1Eo=[1,_1En,_f],_1Ep=[0,98],_1Eq=[1,_1Ep,_f],_1Er=function(_1Es){return new F(function(){return _1CE(function(_1Et,_){var _1Eu=B(_1B0(_1Eq,_1Et,_)),_1Ev=_1Eu,_1Ew=B(A(_1Es,[_1Ev,_])),_1Ex=_1Ew;return _1Ev;},_1Eo);});},_1Ey=function(_1Ez,_1EA,_){var _1EB=E(_1Ez);if(!_1EB[0]){return _1EA;}else{var _1EC=B(A(_1EB[1],[_1EA,_])),_1ED=_1EC,_1EE=B(_1Ey(_1EB[2],_1EA,_)),_1EF=_1EE;return _1EA;}},_1EG=function(_1EH,_1EI,_){return new F(function(){return _1Ey(_1EH,_1EI,_);});},_1EJ=function(_1EK,_1EL,_1EM,_){var _1EN=B(A(_1EK,[_1EM,_])),_1EO=_1EN,_1EP=B(A(_1EL,[_1EM,_])),_1EQ=_1EP;return _1EM;},_1ER=[0,_4v,_1EJ,_1EG],_1ES=[0,_1ER,_1Cu,_5U,_5U,_1B6,_1Er,_1Da,_1Di,_1CW,_1Ed,_1E2,_1Dq,_1DF,_1DQ,_1CE],_1ET=function(_1EU,_1EV,_){var _1EW=B(A(_1EV,[_])),_1EX=_1EW;return _1EU;},_1EY=function(_1EZ,_1F0,_){var _1F1=B(A(_1F0,[_])),_1F2=_1F1;return new T(function(){return B(A(_1EZ,[_1F2]));});},_1F3=[0,_1EY,_1ET],_1F4=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1F5=new T(function(){return B(unCStr("base"));}),_1F6=new T(function(){return B(unCStr("IOException"));}),_1F7=new T(function(){var _1F8=hs_wordToWord64(4053623282),_1F9=_1F8,_1Fa=hs_wordToWord64(3693590983),_1Fb=_1Fa;return [0,_1F9,_1Fb,[0,_1F9,_1Fb,_1F5,_1F4,_1F6],_f];}),_1Fc=function(_1Fd){return E(_1F7);},_1Fe=function(_1Ff){var _1Fg=E(_1Ff);return new F(function(){return _1q(B(_1o(_1Fg[1])),_1Fc,_1Fg[2]);});},_1Fh=new T(function(){return B(unCStr(": "));}),_1Fi=[0,41],_1Fj=new T(function(){return B(unCStr(" ("));}),_1Fk=new T(function(){return B(unCStr("already exists"));}),_1Fl=new T(function(){return B(unCStr("does not exist"));}),_1Fm=new T(function(){return B(unCStr("protocol error"));}),_1Fn=new T(function(){return B(unCStr("failed"));}),_1Fo=new T(function(){return B(unCStr("invalid argument"));}),_1Fp=new T(function(){return B(unCStr("inappropriate type"));}),_1Fq=new T(function(){return B(unCStr("hardware fault"));}),_1Fr=new T(function(){return B(unCStr("unsupported operation"));}),_1Fs=new T(function(){return B(unCStr("timeout"));}),_1Ft=new T(function(){return B(unCStr("resource vanished"));}),_1Fu=new T(function(){return B(unCStr("interrupted"));}),_1Fv=new T(function(){return B(unCStr("resource busy"));}),_1Fw=new T(function(){return B(unCStr("resource exhausted"));}),_1Fx=new T(function(){return B(unCStr("end of file"));}),_1Fy=new T(function(){return B(unCStr("illegal operation"));}),_1Fz=new T(function(){return B(unCStr("permission denied"));}),_1FA=new T(function(){return B(unCStr("user error"));}),_1FB=new T(function(){return B(unCStr("unsatisified constraints"));}),_1FC=new T(function(){return B(unCStr("system error"));}),_1FD=function(_1FE,_1FF){switch(E(_1FE)){case 0:return new F(function(){return _1F(_1Fk,_1FF);});break;case 1:return new F(function(){return _1F(_1Fl,_1FF);});break;case 2:return new F(function(){return _1F(_1Fv,_1FF);});break;case 3:return new F(function(){return _1F(_1Fw,_1FF);});break;case 4:return new F(function(){return _1F(_1Fx,_1FF);});break;case 5:return new F(function(){return _1F(_1Fy,_1FF);});break;case 6:return new F(function(){return _1F(_1Fz,_1FF);});break;case 7:return new F(function(){return _1F(_1FA,_1FF);});break;case 8:return new F(function(){return _1F(_1FB,_1FF);});break;case 9:return new F(function(){return _1F(_1FC,_1FF);});break;case 10:return new F(function(){return _1F(_1Fm,_1FF);});break;case 11:return new F(function(){return _1F(_1Fn,_1FF);});break;case 12:return new F(function(){return _1F(_1Fo,_1FF);});break;case 13:return new F(function(){return _1F(_1Fp,_1FF);});break;case 14:return new F(function(){return _1F(_1Fq,_1FF);});break;case 15:return new F(function(){return _1F(_1Fr,_1FF);});break;case 16:return new F(function(){return _1F(_1Fs,_1FF);});break;case 17:return new F(function(){return _1F(_1Ft,_1FF);});break;default:return new F(function(){return _1F(_1Fu,_1FF);});}},_1FG=[0,125],_1FH=new T(function(){return B(unCStr("{handle: "));}),_1FI=function(_1FJ,_1FK,_1FL,_1FM,_1FN,_1FO){var _1FP=new T(function(){var _1FQ=new T(function(){return B(_1FD(_1FK,new T(function(){var _1FR=E(_1FM);return _1FR[0]==0?E(_1FO):B(_1F(_1Fj,new T(function(){return B(_1F(_1FR,[1,_1Fi,_1FO]));},1)));},1)));},1),_1FS=E(_1FL);return _1FS[0]==0?E(_1FQ):B(_1F(_1FS,new T(function(){return B(_1F(_1Fh,_1FQ));},1)));},1),_1FT=E(_1FN);if(!_1FT[0]){var _1FU=E(_1FJ);if(!_1FU[0]){return E(_1FP);}else{var _1FV=E(_1FU[1]);return _1FV[0]==0?B(_1F(_1FH,new T(function(){return B(_1F(_1FV[1],[1,_1FG,new T(function(){return B(_1F(_1Fh,_1FP));})]));},1))):B(_1F(_1FH,new T(function(){return B(_1F(_1FV[1],[1,_1FG,new T(function(){return B(_1F(_1Fh,_1FP));})]));},1)));}}else{return new F(function(){return _1F(_1FT[1],new T(function(){return B(_1F(_1Fh,_1FP));},1));});}},_1FW=function(_1FX){var _1FY=E(_1FX);return new F(function(){return _1FI(_1FY[1],_1FY[2],_1FY[3],_1FY[4],_1FY[6],_f);});},_1FZ=function(_1G0,_1G1){var _1G2=E(_1G0);return new F(function(){return _1FI(_1G2[1],_1G2[2],_1G2[3],_1G2[4],_1G2[6],_1G1);});},_1G3=function(_1G4,_1G5){return new F(function(){return _1P(_1FZ,_1G4,_1G5);});},_1G6=function(_1G7,_1G8,_1G9){var _1Ga=E(_1G8);return new F(function(){return _1FI(_1Ga[1],_1Ga[2],_1Ga[3],_1Ga[4],_1Ga[6],_1G9);});},_1Gb=[0,_1G6,_1FW,_1G3],_1Gc=new T(function(){return [0,_1Fc,_1Gb,_1Gd,_1Fe];}),_1Gd=function(_1Ge){return [0,_1Gc,_1Ge];},_1Gf=7,_1Gg=function(_1Gh){return [0,_10,_1Gf,_f,_1Gh,_10,_10];},_1Gi=function(_1Gj,_){return new F(function(){return die(new T(function(){return B(_1Gd(new T(function(){return B(_1Gg(_1Gj));})));}));});},_1Gk=function(_1Gl,_){return new F(function(){return _1Gi(_1Gl,_);});},_1Gm=function(_1Gn,_){return new F(function(){return _1Gk(_1Gn,_);});},_1Go=function(_1Gp,_){return new F(function(){return _1Gm(_1Gp,_);});},_1Gq=function(_1Gr,_1Gs,_){var _1Gt=B(A(_1Gr,[_])),_1Gu=_1Gt;return new F(function(){return A(_1Gs,[_1Gu,_]);});},_1Gv=function(_1Gw,_1Gx,_){var _1Gy=B(A(_1Gw,[_])),_1Gz=_1Gy;return new F(function(){return A(_1Gx,[_]);});},_1GA=[0,_1Gq,_1Gv,_4v,_1Go],_1GB=[0,_1GA,_4s],_1GC=function(_1GD){return E(E(_1GD)[1]);},_1GE=function(_1GF){return E(E(_1GF)[2]);},_1GG=function(_1GH,_1GI){var _1GJ=new T(function(){return B(_1GC(_1GH));});return function(_1GK){return new F(function(){return A(new T(function(){return B(_17P(_1GJ));}),[new T(function(){return B(A(_1GE,[_1GH,_1GI]));}),function(_1GL){return new F(function(){return A(new T(function(){return B(_C8(_1GJ));}),[[0,_1GL,_1GK]]);});}]);});};},_1GM=function(_1GN,_1GO){return [0,_1GN,function(_1GP){return new F(function(){return _1GG(_1GO,_1GP);});}];},_1GQ=function(_1GR,_1GS,_1GT,_1GU){return new F(function(){return A(_17P,[_1GR,new T(function(){return B(A(_1GS,[_1GU]));}),function(_1GV){return new F(function(){return A(_1GT,[new T(function(){return E(E(_1GV)[1]);}),new T(function(){return E(E(_1GV)[2]);})]);});}]);});},_1GW=function(_1GX,_1GY,_1GZ,_1H0){return new F(function(){return A(_17P,[_1GX,new T(function(){return B(A(_1GY,[_1H0]));}),function(_1H1){return new F(function(){return A(_1GZ,[new T(function(){return E(E(_1H1)[2]);})]);});}]);});},_1H2=function(_1H3,_1H4,_1H5,_1H6){return new F(function(){return _1GW(_1H3,_1H4,_1H5,_1H6);});},_1H7=function(_1H8){return E(E(_1H8)[4]);},_1H9=function(_1Ha,_1Hb){return function(_1Hc){return E(new T(function(){return B(A(_1H7,[_1Ha,_1Hb]));}));};},_1Hd=function(_1He){return [0,function(_1H4,_1H5,_1H6){return new F(function(){return _1GQ(_1He,_1H4,_1H5,_1H6);});},function(_1H4,_1H5,_1H6){return new F(function(){return _1H2(_1He,_1H4,_1H5,_1H6);});},function(_1Hf,_1Hg){return new F(function(){return A(new T(function(){return B(_C8(_1He));}),[[0,_1Hf,_1Hg]]);});},function(_1H6){return new F(function(){return _1H9(_1He,_1H6);});}];},_1Hh=function(_1Hi,_1Hj,_1Hk){return new F(function(){return A(_C8,[_1Hi,[0,_1Hj,_1Hk]]);});},_1Hl=[0,10],_1Hm=function(_1Hn,_1Ho){var _1Hp=E(_1Ho);if(!_1Hp[0]){return E(_4s);}else{var _1Hq=_1Hp[1],_1Hr=E(_1Hp[2]);if(!_1Hr[0]){var _1Hs=E(_1Hq);return new F(function(){return _1Ht(_1Hl,_1Hs[3],_1Hs[4]);});}else{return function(_1Hu){return new F(function(){return A(new T(function(){var _1Hv=E(_1Hq);return B(_1Ht(_1Hl,_1Hv[3],_1Hv[4]));}),[new T(function(){return B(A(_1Hn,[new T(function(){return B(A(new T(function(){return B(_1Hm(_1Hn,_1Hr));}),[_1Hu]));})]));})]);});};}}},_1Hw=new T(function(){return B(unCStr("(->)"));}),_1Hx=new T(function(){return B(unCStr("GHC.Prim"));}),_1Hy=new T(function(){var _1Hz=hs_wordToWord64(4173248105),_1HA=_1Hz,_1HB=hs_wordToWord64(4270398258),_1HC=_1HB;return [0,_1HA,_1HC,[0,_1HA,_1HC,_1Bg,_1Hx,_1Hw],_f];}),_1HD=new T(function(){return E(E(_1Hy)[3]);}),_1HE=new T(function(){return B(unCStr("GHC.Types"));}),_1HF=new T(function(){return B(unCStr("[]"));}),_1HG=new T(function(){var _1HH=hs_wordToWord64(4033920485),_1HI=_1HH,_1HJ=hs_wordToWord64(786266835),_1HK=_1HJ;return [0,_1HI,_1HK,[0,_1HI,_1HK,_1Bg,_1HE,_1HF],_f];}),_1HL=[1,_1Bh,_f],_1HM=function(_1HN){var _1HO=E(_1HN);if(!_1HO[0]){return [0];}else{var _1HP=E(_1HO[1]);return [1,[0,_1HP[1],_1HP[2]],new T(function(){return B(_1HM(_1HO[2]));})];}},_1HQ=new T(function(){var _1HR=E(_1HG),_1HS=E(_1HR[3]),_1HT=B(_1F(_1HR[4],_1HL));if(!_1HT[0]){var _1HU=E(_1HS);}else{var _1HV=B(_1BL(new T(function(){return B(_7o(B(_7U(_1Ce,[1,[0,_1HS[1],_1HS[2]],new T(function(){return B(_1HM(_1HT));})]))));},1))),_1HU=E(_1HS);}var _1HW=_1HU,_1HX=_1HW;return _1HX;}),_1HY=[0,8],_1HZ=[0,32],_1I0=function(_1I1){return [1,_1HZ,_1I1];},_1I2=new T(function(){return B(unCStr(" -> "));}),_1I3=[0,9],_1I4=[0,93],_1I5=[0,91],_1I6=[0,41],_1I7=[0,44],_1I8=function(_1I1){return [1,_1I7,_1I1];},_1I9=[0,40],_1Ia=[0,0],_1Ht=function(_1Ib,_1Ic,_1Id){var _1Ie=E(_1Id);if(!_1Ie[0]){return function(_1If){return new F(function(){return _1F(E(_1Ic)[5],_1If);});};}else{var _1Ig=_1Ie[1],_1Ih=function(_1Ii){var _1Ij=E(_1Ic)[5],_1Ik=function(_1Il){var _1Im=new T(function(){return B(_1Hm(_1I0,_1Ie));});return E(_1Ib)[1]<=9?function(_1In){return new F(function(){return _1F(_1Ij,[1,_1HZ,new T(function(){return B(A(_1Im,[_1In]));})]);});}:function(_1Io){return [1,_4e,new T(function(){return B(_1F(_1Ij,[1,_1HZ,new T(function(){return B(A(_1Im,[[1,_4d,_1Io]]));})]));})];};},_1Ip=E(_1Ij);if(!_1Ip[0]){return new F(function(){return _1Ik(_);});}else{if(E(E(_1Ip[1])[1])==40){var _1Iq=E(_1Ip[2]);if(!_1Iq[0]){return new F(function(){return _1Ik(_);});}else{if(E(E(_1Iq[1])[1])==44){return function(_1Ir){return [1,_1I9,new T(function(){return B(A(new T(function(){return B(_1Hm(_1I8,_1Ie));}),[[1,_1I6,_1Ir]]));})];};}else{return new F(function(){return _1Ik(_);});}}}else{return new F(function(){return _1Ik(_);});}}},_1Is=E(_1Ie[2]);if(!_1Is[0]){var _1It=E(_1Ic),_1Iu=E(_1HQ),_1Iv=hs_eqWord64(_1It[1],_1Iu[1]),_1Iw=_1Iv;if(!E(_1Iw)){return new F(function(){return _1Ih(_);});}else{var _1Ix=hs_eqWord64(_1It[2],_1Iu[2]),_1Iy=_1Ix;if(!E(_1Iy)){return new F(function(){return _1Ih(_);});}else{return function(_1Iz){return [1,_1I5,new T(function(){return B(A(new T(function(){var _1IA=E(_1Ig);return B(_1Ht(_1Ia,_1IA[3],_1IA[4]));}),[[1,_1I4,_1Iz]]));})];};}}}else{if(!E(_1Is[2])[0]){var _1IB=E(_1Ic),_1IC=E(_1HD),_1ID=hs_eqWord64(_1IB[1],_1IC[1]),_1IE=_1ID;if(!E(_1IE)){return new F(function(){return _1Ih(_);});}else{var _1IF=hs_eqWord64(_1IB[2],_1IC[2]),_1IG=_1IF;if(!E(_1IG)){return new F(function(){return _1Ih(_);});}else{var _1IH=new T(function(){var _1II=E(_1Is[1]);return B(_1Ht(_1HY,_1II[3],_1II[4]));}),_1IJ=new T(function(){var _1IK=E(_1Ig);return B(_1Ht(_1I3,_1IK[3],_1IK[4]));});return E(_1Ib)[1]<=8?function(_1IL){return new F(function(){return A(_1IJ,[new T(function(){return B(_1F(_1I2,new T(function(){return B(A(_1IH,[_1IL]));},1)));})]);});}:function(_1IM){return [1,_4e,new T(function(){return B(A(_1IJ,[new T(function(){return B(_1F(_1I2,new T(function(){return B(A(_1IH,[[1,_4d,_1IM]]));},1)));})]));})];};}}}else{return new F(function(){return _1Ih(_);});}}}},_1IN=function(_1IO,_1IP){return new F(function(){return A(_1IO,[function(_){return new F(function(){return jsFind(toJSStr(E(_1IP)));});}]);});},_1IQ=[0],_1IR=function(_1IS){return E(E(_1IS)[3]);},_1IT=new T(function(){return [0,"value"];}),_1IU=function(_1IV){return E(E(_1IV)[6]);},_1IW=function(_1IX){return E(E(_1IX)[1]);},_1IY=new T(function(){return B(unCStr("Char"));}),_1IZ=new T(function(){var _1J0=hs_wordToWord64(3763641161),_1J1=_1J0,_1J2=hs_wordToWord64(1343745632),_1J3=_1J2;return [0,_1J1,_1J3,[0,_1J1,_1J3,_1Bg,_1HE,_1IY],_f];}),_1J4=function(_1J5){return E(_1IZ);},_1J6=function(_1J7){return E(_1HG);},_1J8=new T(function(){return B(_1Ch(_1J6,_1J4));}),_1J9=new T(function(){return B(A(_1J8,[_]));}),_1Ja=function(_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg,_1Jh,_1Ji,_1Jj){var _1Jk=new T(function(){return B(A(_1Je,[_1IQ]));});return new F(function(){return A(_1Jc,[new T(function(){return B(_1IN(E(_1Jb)[2],_1Jj));}),function(_1Jl){var _1Jm=E(_1Jl);return _1Jm[0]==0?E(_1Jk):B(A(_1Jc,[new T(function(){return B(A(E(_1Jb)[2],[function(_){var _1Jn=jsGet(E(_1Jm[1])[1],E(_1IT)[1]),_1Jo=_1Jn;return [1,new T(function(){return fromJSStr(_1Jo);})];}]));}),function(_1Jp){var _1Jq=E(_1Jp);if(!_1Jq[0]){return E(_1Jk);}else{var _1Jr=_1Jq[1];if(!E(new T(function(){var _1Js=B(A(_1Jg,[_])),_1Jt=E(_1J9),_1Ju=hs_eqWord64(_1Js[1],_1Jt[1]),_1Jv=_1Ju;if(!E(_1Jv)){var _1Jw=false;}else{var _1Jx=hs_eqWord64(_1Js[2],_1Jt[2]),_1Jy=_1Jx,_1Jw=E(_1Jy)==0?false:true;}var _1Jz=_1Jw,_1JA=_1Jz;return _1JA;}))){var _1JB=function(_1JC){return new F(function(){return A(_1Je,[[1,_1Jr,new T(function(){return B(A(new T(function(){return B(_1IU(_1Ji));}),[new T(function(){return B(A(new T(function(){return B(_1IR(_1Ji));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_1F(_1Jr,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1JD=B(A(_1Jg,[_]));return B(A(_1Ht,[_1Ia,_1JD[3],_1JD[4],_f]));})));})));})));})]));})]));})]]);});},_1JE=B(A(new T(function(){return B(A(_1IW,[_1Jh,_J]));}),[_1Jr]));if(!_1JE[0]){return new F(function(){return _1JB(_);});}else{var _1JF=E(_1JE[1]);return E(_1JF[2])[0]==0?E(_1JE[2])[0]==0?B(A(_1Je,[[2,_1JF[1]]])):B(_1JB(_)):B(_1JB(_));}}else{return new F(function(){return A(_1Je,[[2,_1Jr]]);});}}}]));}]);});},_1JG=function(_1JH){return E(E(_1JH)[10]);},_1JI=function(_1JJ){return new F(function(){return _Em([1,function(_1JK){return new F(function(){return A(_LW,[_1JK,function(_1JL){return E(new T(function(){return B(_Nc(function(_1JM){var _1JN=E(_1JM);return _1JN[0]==0?B(A(_1JJ,[_1JN[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_Ny(_1JO,_1JJ))];}));});},_1JO=function(_1JP,_1JQ){return new F(function(){return _1JI(_1JQ);});},_1JR=[0,91],_1JS=[1,_1JR,_f],_1JT=function(_1JU,_1JV){var _1JW=function(_1JX,_1JY){return [1,function(_1JZ){return new F(function(){return A(_LW,[_1JZ,function(_1K0){return E(new T(function(){return B(_Nc(function(_1K1){var _1K2=E(_1K1);if(_1K2[0]==2){var _1K3=E(_1K2[1]);if(!_1K3[0]){return [2];}else{var _1K4=_1K3[2];switch(E(E(_1K3[1])[1])){case 44:return E(_1K4)[0]==0?!E(_1JX)?[2]:E(new T(function(){return B(A(_1JU,[_Nx,function(_1K5){return new F(function(){return _1JW(_Ht,function(_1K6){return new F(function(){return A(_1JY,[[1,_1K5,_1K6]]);});});});}]));})):[2];case 93:return E(_1K4)[0]==0?E(new T(function(){return B(A(_1JY,[_f]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1K7=function(_1K8){return new F(function(){return _Em([1,function(_1K9){return new F(function(){return A(_LW,[_1K9,function(_1Ka){return E(new T(function(){return B(_Nc(function(_1Kb){var _1Kc=E(_1Kb);return _1Kc[0]==2?!B(_bw(_1Kc[1],_1JS))?[2]:E(new T(function(){return B(_Em(B(_1JW(_K,_1K8)),new T(function(){return B(A(_1JU,[_Nx,function(_1Kd){return new F(function(){return _1JW(_Ht,function(_1Ke){return new F(function(){return A(_1K8,[[1,_1Kd,_1Ke]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_Ny(function(_1Kf,_1Kg){return new F(function(){return _1K7(_1Kg);});},_1K8))];}));});};return new F(function(){return _1K7(_1JV);});},_1Kh=function(_1Ki){return new F(function(){return _Em(B(_Em([1,function(_1Kj){return new F(function(){return A(_LW,[_1Kj,function(_1Kk){return E(new T(function(){return B(_Nc(function(_1Kl){var _1Km=E(_1Kl);return _1Km[0]==1?B(A(_1Ki,[_1Km[1]])):[2];}));}));}]);});}],new T(function(){return B(_1JT(_1JO,_1Ki));}))),new T(function(){return [1,B(_Ny(_1Kn,_1Ki))];}));});},_1Kn=function(_1Ko,_1Kp){return new F(function(){return _1Kh(_1Kp);});},_1Kq=new T(function(){return B(_1Kh(_F5));}),_1Kr=function(_1Ks){return new F(function(){return _Ec(_1Kq,_1Ks);});},_1Kt=new T(function(){return B(_1JI(_F5));}),_1Ku=function(_1Ks){return new F(function(){return _Ec(_1Kt,_1Ks);});},_1Kv=function(_1Kw){return E(_1Ku);},_1Kx=[0,_1Kv,_1Kr,_1JO,_1Kn],_1Ky=function(_1Kz){return E(E(_1Kz)[4]);},_1KA=function(_1KB,_1KC,_1KD){return new F(function(){return _1JT(new T(function(){return B(_1Ky(_1KB));}),_1KD);});},_1KE=function(_1KF){return function(_m0){return new F(function(){return _Ec(new T(function(){return B(_1JT(new T(function(){return B(_1Ky(_1KF));}),_F5));}),_m0);});};},_1KG=function(_1KH,_1KI){return function(_m0){return new F(function(){return _Ec(new T(function(){return B(A(_1Ky,[_1KH,_1KI,_F5]));}),_m0);});};},_1KJ=function(_1KK){return [0,function(_1Ks){return new F(function(){return _1KG(_1KK,_1Ks);});},new T(function(){return B(_1KE(_1KK));}),new T(function(){return B(_1Ky(_1KK));}),function(_1KL,_1Ks){return new F(function(){return _1KA(_1KK,_1KL,_1Ks);});}];},_1KM=new T(function(){return B(_1KJ(_1Kx));}),_1KN=function(_1KO,_1KP,_1KQ){var _1KR=new T(function(){return B(_1JG(_1KO));}),_1KS=new T(function(){return B(_1GC(_1KQ));}),_1KT=new T(function(){return B(_C8(_1KS));});return function(_1KU,_1KV){return new F(function(){return A(new T(function(){return B(_17P(_1KS));}),[new T(function(){return B(A(new T(function(){return B(_17P(_1KS));}),[new T(function(){return B(A(new T(function(){return B(_C8(_1KS));}),[[0,_1KV,_1KV]]));}),function(_1KW){var _1KX=new T(function(){return E(E(_1KW)[1]);}),_1KY=new T(function(){return E(E(_1KX)[2]);});return new F(function(){return A(new T(function(){return B(_17P(_1KS));}),[new T(function(){return B(A(new T(function(){return B(_C8(_1KS));}),[[0,_0,new T(function(){var _1KZ=E(_1KX);return [0,_1KZ[1],new T(function(){return [0,E(_1KY)[1]+1|0];}),_1KZ[3],_1KZ[4],_1KZ[5],_1KZ[6],_1KZ[7]];})]]));}),function(_1L0){return new F(function(){return A(new T(function(){return B(_C8(_1KS));}),[[0,[1,_4l,new T(function(){return B(_1F(B(_4f(0,E(_1KY)[1],_f)),new T(function(){return E(E(_1KX)[1]);},1)));})],new T(function(){return E(E(_1L0)[2]);})]]);});}]);});}]));}),function(_1L1){var _1L2=new T(function(){return E(E(_1L1)[1]);});return new F(function(){return A(new T(function(){return B(_17P(_1KS));}),[new T(function(){return B(A(_1Ja,[new T(function(){return B(_1GM(new T(function(){return B(_1Hd(_1KS));}),_1KQ));}),function(_1L3,_1CL,_1L4){return new F(function(){return _1GQ(_1KS,_1L3,_1CL,_1L4);});},function(_1L3,_1CL,_1L4){return new F(function(){return _1H2(_1KS,_1L3,_1CL,_1L4);});},function(_1CL,_1L4){return new F(function(){return _1Hh(_1KS,_1CL,_1L4);});},function(_1L4){return new F(function(){return _1H9(_1KS,_1L4);});},_1J8,_1KM,_1KO,_1L2,new T(function(){return E(E(_1L1)[2]);})]));}),function(_1L5){var _1L6=E(_1L5),_1L7=_1L6[2],_1L8=E(_1L6[1]);switch(_1L8[0]){case 0:return new F(function(){return A(_1KT,[[0,[0,new T(function(){return B(A(_1KR,[_1L2,_1KU]));}),_10],_1L7]]);});break;case 1:return new F(function(){return A(_1KT,[[0,[0,new T(function(){return B(A(_1KR,[_1L2,_1L8[1]]));}),_10],_1L7]]);});break;default:var _1L9=_1L8[1];return new F(function(){return A(_1KT,[[0,[0,new T(function(){return B(A(_1KR,[_1L2,_1L9]));}),[1,_1L9]],_1L7]]);});}}]);});}]);});};},_1La=new T(function(){return B(_1KN(_1ES,_1F3,_1GB));}),_1Lb=function(_1Lc){return E(E(_1Lc)[2]);},_1Ld=function(_1Le){return E(E(_1Le)[1]);},_1Lf=function(_1Lg,_1Lh,_1Li){return function(_1Lj,_){var _1Lk=B(A(_1Lh,[_1Lj,_])),_1Ll=_1Lk,_1Lm=E(_1Ll),_1Ln=E(_1Lm[1]),_1Lo=new T(function(){return B(A(new T(function(){return B(_1Lb(_1Lg));}),[_1Li,function(_){var _1Lp=E(E(_1Lj)[4]),_1Lq=B(A(_1Lp[1],[_])),_1Lr=_1Lq,_1Ls=E(_1Lr);if(!_1Ls[0]){return _0;}else{var _1Lt=B(A(_1Lp[2],[_1Ls[1],_])),_1Lu=_1Lt;return _0;}}]));});return [0,[0,function(_1Lv,_){var _1Lw=B(A(_1Ln[1],[_1Lv,_])),_1Lx=_1Lw,_1Ly=E(_1Lx),_1Lz=E(_1Lo),_1LA=jsSetCB(_1Ly[1],toJSStr(E(new T(function(){return B(A(_1Ld,[_1Lg,_1Li]));}))),_1Lo),_1LB=_1LA;return _1Ly;},_1Ln[2]],_1Lm[2]];};},_1LC=function(_1LD){return function(_m0,_m1){return new F(function(){return _57(function(_1LE,_){var _1LF=B(A(new T(function(){return B(_1Lf(_41,new T(function(){return B(_1Lf(_41,new T(function(){return B(A(_1La,[_1LD]));}),_h));}),_g));}),[_1LE,_])),_1LG=_1LF,_1LH=E(_1LG),_1LI=E(_1LH[1]);return [0,[0,function(_1LJ,_){var _1LK=B(A(_1LI[1],[_1LJ,_])),_1LL=_1LK,_1LM=B(A(_42,[_4s,_1LL,_vD,_1AZ,_])),_1LN=_1LM;return _1LL;},_1LI[2]],_1LH[2]];},_1Ab,_m0,_m1);});};},_1LO=new T(function(){return B(unCStr("innerHTML"));}),_1LP=new T(function(){return B(unCStr("textContent"));}),_1LQ=function(_1LR,_){var _1LS=B(_4(_1LR,_1LP,_)),_1LT=_1LS,_1LU=[0,_1LR],_1LV=B(A(_9,[_4s,_1LU,_1LO,_f,_])),_1LW=_1LV,_1LX=E(_1d)[1],_1LY=takeMVar(_1LX),_1LZ=_1LY,_1M0=B(A(_1LC,[_1LT,_1LZ,_])),_1M1=_1M0,_1M2=E(_1M1),_1M3=E(_1M2[1]),_=putMVar(_1LX,_1M2[2]),_1M4=B(A(_1M3[1],[_1LU,_])),_1M5=_1M4;return _1M3[2];},_1M6=function(_1M7,_){while(1){var _1M8=E(_1M7);if(!_1M8[0]){return _0;}else{var _1M9=B(_1LQ(E(_1M8[1])[1],_)),_1Ma=_1M9;_1M7=_1M8[2];continue;}}},_1Mb=function(_){var _1Mc=jsElemsByClassName("proofbox"),_1Md=_1Mc,_1Me=B(_1M6(_1Md,_)),_1Mf=_1Me,_1Mg=jsSetTimeout(60,_1);return _0;},_1Mh=function(_){return new F(function(){return _1Mb(_);});};
var hasteMain = function() {B(A(_1Mh, [0]));};window.onload = hasteMain;