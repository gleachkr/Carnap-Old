/*! bespoke-forms v1.0.0 © 2014 Mark Dalgleish, MIT License */
!function(e){if("object"==typeof exports&&"undefined"!=typeof module)module.exports=e();else if("function"==typeof define&&define.amd)define([],e);else{var n;"undefined"!=typeof window?n=window:"undefined"!=typeof global?n=global:"undefined"!=typeof self&&(n=self);var t=n;t=t.bespoke||(t.bespoke={}),t=t.plugins||(t.plugins={}),t.forms=e()}}(function(){return function e(n,t,o){function r(i,u){if(!t[i]){if(!n[i]){var d="function"==typeof require&&require;if(!u&&d)return d(i,!0);if(f)return f(i,!0);throw new Error("Cannot find module '"+i+"'")}var p=t[i]={exports:{}};n[i][0].call(p.exports,function(e){var t=n[i][1][e];return r(t?t:e)},p,p.exports,e,n,t,o)}return t[i].exports}for(var f="function"==typeof require&&require,i=0;i<o.length;i++)r(o[i]);return r}({1:[function(e,n){n.exports=function(){return function(e){e.slides.forEach(function(e){e.addEventListener("keydown",function(e){(/INPUT|TEXTAREA|SELECT/.test(e.target.nodeName)||"true"===e.target.contentEditable)&&e.stopPropagation()})})}}},{}]},{},[1])(1)});
