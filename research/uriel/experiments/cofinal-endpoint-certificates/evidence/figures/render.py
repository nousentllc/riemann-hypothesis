"""Render the three vector figures directly from the geometry and archived prime data."""
import argparse
import json
import math
from pathlib import Path
from fractions import Fraction

from reportlab.lib.colors import HexColor
from reportlab.pdfgen.canvas import Canvas

BASE=Path(__file__).resolve().parents[1]
INK="#153832"
BLUE="#09675F"
RED="#884F68"
MUTE="#53665E"
GRID="#D0DDD6"

def text(c,x,y,value,size=9,bold=False,color=MUTE):
    c.setFillColor(HexColor(color))
    c.setFont("Helvetica-Bold" if bold else "Helvetica",size)
    c.drawString(x,y,value)

def line(c,x,y,xx,yy,color=GRID,width=.65):
    c.setStrokeColor(HexColor(color))
    c.setLineWidth(width)
    c.line(x,y,xx,yy)

def dot(c,x,y,color,r=2.3):
    c.setFillColor(HexColor(color))
    c.circle(x,y,r,fill=1,stroke=0)

def gap(out):
    receipt=json.loads((BASE/"outer/results.json").read_text())
    row=next(r for r in receipt["sharp_schedules"] if r["J"]=="8")
    left,right=map(float,map(Fraction,row["first_three_open_gaps"][0]))
    x=lambda v: 48+4.4*v
    c=Canvas(str(out/"supply.pdf"),pagesize=(472,167),invariant=1)
    text(c,18,149,"How an outer query can miss an entire open interval",12,True,INK)
    text(c,18,134,"Exact witness schedule, J = 8. Horizontal positions use log(x/k).",9)
    c.setFillColor(HexColor("#F3EBED"))
    c.rect(x(left),30,x(right)-x(left),94,fill=1,stroke=0)
    for i,U in enumerate([48,64,72,104,128,256]):
        y=115-i*14
        w=U/2 if 64<U<256 else U/8
        text(c,4,y-2,f"U={U}",7)
        line(c,x(0),y,x(90),y,GRID,.35)
        end=min(90,2*w,U-1)
        line(c,x(w),y,x(end),y,BLUE,2.3)
        dot(c,x(w),y,BLUE,1.5)
        if end<90:dot(c,x(end),y,BLUE,1.5)
    for v in (0,16,32,48,64,80):
        text(c,x(v)-4,13,str(v),8)
    text(c,273,13,"logarithmic ordinate",8)
    c.save()

def mass(out):
    d=json.loads((BASE/"numeric/results.json").read_text())
    c=Canvas(str(out/"mass.pdf"),pagesize=(472,198),invariant=1)
    text(c,17,180,"Observation count and the mass still compatible with the data",12,True,INK)
    text(c,17,165,"Minimum certified upper mass / genuine mass. Both exterior observations count.",9)
    X=lambda n: 40+12.8*(n-2)
    Y=lambda r: 37+94*math.log(r)/math.log(14)
    for r in (1,1.25,2,4,8,13):
        line(c,40,Y(r),442,Y(r))
        text(c,13,Y(r)-2,str(r),7)
    for n in (2,5,9,13,17,21,25,29,33):text(c,X(n)-4,21,str(n),8)
    for key,color,name in (("step8",RED,"Regular grid"),("upward",BLUE,"Upward jumps")):
        rows=d["menus"][key]["frontier"]
        prev=None
        for row in rows:
            p=(X(row["k"]),Y(float(row["ratio"][1])))
            if prev:line(c,*prev,*p,color,1.3)
            dot(c,*p,color,1.3)
            prev=p
    text(c,230,143,"Regular grid",8,True,RED)
    text(c,304,143,"Upward jumps",8,True,BLUE)
    text(c,307,5,"number of measured heights",8)
    c.save()

def ceilings(out):
    d=json.loads((BASE/"numeric/ceilings.json").read_text())["1"]
    c=Canvas(str(out/"placement.pdf"),pagesize=(472,135),invariant=1)
    text(c,17,118,"A ceiling-only certificate on the true modulo-four example",12,True,INK)
    text(c,17,103,"Two passing menus for G(y) at or below sqrt(y). Each tick is one observed ordinate.",9)
    X=lambda y:76+(y-256)*1.42
    for key,y,color,name in (("downward",71,BLUE,"23 jumps"),("step8",47,RED,"Step 8")):
        text(c,10,y-3,name,8,True,color)
        line(c,X(256),y,X(512),y)
        pts=d["menus"][key]["active_hull_vertices"] if key=="downward" else list(range(256,513,8))
        for n in pts:line(c,X(n),y-4,X(n),y+4,color,1.2)
    for n in (256,320,384,448,512):text(c,X(n)-7,30,str(n),8)
    text(c,76,11,"Upper row certifies zero excess. Lower row leaves a strictly positive worst case.",8)
    c.save()

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("output",type=Path)
    args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    for generate in (gap,mass,ceilings):generate(args.output)
