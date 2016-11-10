/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package com.sun.hotspot.igv.view;

import com.sun.hotspot.igv.graph.Figure;
import java.util.ArrayList;
import java.util.List;
import org.netbeans.api.visual.widget.Scene;

/** Centers given figures after scene is validated.
 *
 * @author Radek Smogura <radek@smogura.eu>
 */
public class CenterFiguresSceneListener implements Scene.SceneListener {
    private final List<Figure> figuresToCenter = new ArrayList<>();
    private final DiagramScene diagramScene;

    public CenterFiguresSceneListener(DiagramScene diagramScene) {
        this.diagramScene = diagramScene;
    }
    
    @Override
    public void sceneRepaint() {
    }

    @Override
    public void sceneValidating() {
    }

    @Override
    public synchronized void sceneValidated() {
        if (!figuresToCenter.isEmpty()) {
            diagramScene.centerFigures(figuresToCenter);
            figuresToCenter.clear();
        }
    }

    public synchronized void setFiguresToCenter(List<Figure> figures) {
        figuresToCenter.addAll(figures);
    }
}
