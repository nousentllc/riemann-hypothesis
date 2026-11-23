"""Render the two vector exhibits embedded in the standalone LuaLaTeX manuscript."""
import json
import math
from pathlib import Path
from reportlab.lib import colors
from reportlab.pdfgen.canvas import Canvas

HERE=Path(__file__).resolve().parent
INK="#183831"; BLUE="#255a79"; GREEN="#177560"; LIGHT="#eaf1ed"; GRAY="#54665f"; RULE="#b7c9c0"
def paint(c,fill):
    c.setFillColor(colors.HexColor(fill))
def label(c,x,y,s,size=10,face="Helvetica",ink=INK):
    paint(c,ink);c.setFont(face,size);c.drawString(x,y,s)
def box(c,x,y,w,h,head,lines):
    paint(c,LIGHT);c.roundRect(x,y,w,h,4,stroke=0,fill=1)
    label(c,x+10,y+h-17,head,11,"Helvetica-Bold")
    for i,t in enumerate(lines):label(c,x+10,y+h-33-13*i,t,9,"Helvetica",GRAY)
def arrow(c,x,y,x2,y2):
    c.setStrokeColor(colors.HexColor(GREEN));c.setLineWidth(1.1);c.line(x,y,x2,y2)
    ang=math.atan2(y2-y,x2-x)
    for offset in (-.48,.48):c.line(x2,y2,x2-5*math.cos(ang+offset),y2-5*math.sin(ang+offset))

def chain():
    c=Canvas(str(HERE/'witness.pdf'),pagesize=(502,236),invariant=1)
    box(c,5,160,234,64,"Roster field: discriminant -7",["Degree two, Minkowski bound below 2.","The conductor-one odd primes are 3 and 7."])
    box(c,261,160,236,64,"Local field: conductor 7",["Degree six, class number 1.","Each next cyclotomic step has degree 7."])
    box(c,261,78,236,60,"All tower layers",["Only the prime over 7 ramifies.","No layer acquires a 7-primary ideal class."])
    box(c,5,78,234,60,"Local length sum",["Trivial 7-primary module; descent at each","nonzero weight. Every positive-weight sum is 0."])
    box(c,5,5,492,47,"Original principal-character window",["Slot 3 was already controlled. The remaining exceptional-weight tests concern the moving field at 2."])
    arrow(c,239,192,261,192);arrow(c,379,160,379,139);arrow(c,261,108,239,108);arrow(c,117,78,117,53)
    c.showPage();c.save()

def growth():
    rows=[r for r in json.loads((HERE.parent/'numerics/extended.json').read_text())['rows'] if r['prime']==7]
    rows.sort(key=lambda r:r['power'])
    c=Canvas(str(HERE/'classnumbers.pdf'),pagesize=(502,223),invariant=1)
    label(c,8,204,"Relative class numbers in the 7-power tower",12,"Helvetica-Bold")
    label(c,8,187,"Positions show decimal digits on a logarithmic axis. Labels give the exact digit counts.",9,"Helvetica",GRAY)
    x0=80;x1=456
    def X(a):return x0+(x1-x0)*math.log10(a)/3
    for val in (1,2,10,100,1000):
        x=X(val);c.setStrokeColor(colors.HexColor(RULE));c.setLineWidth(.55);c.line(x,30,x,165)
        label(c,x-3,15,str(val),8,"Helvetica",GRAY)
    for i,r in enumerate(rows):
        n=len(r['relative_class_number']);y=151-i*36;x=X(n)
        label(c,8,y-3,"q = "+str(r['conductor']),10,"Helvetica-Bold")
        c.setStrokeColor(colors.HexColor(GREEN));c.setLineWidth(2);c.line(x0,y,x,y)
        paint(c,GREEN);c.circle(x,y,3.6,stroke=0,fill=1)
        suffix=" digit" if n==1 else " digits"
        if n>500:label(c,x-53,y+6,str(n)+suffix,9,"Helvetica-Bold",BLUE)
        else:label(c,x+8,y-3,str(n)+suffix,9,"Helvetica-Bold",BLUE)
    c.showPage();c.save()
if __name__ == "__main__":
    chain();growth()
